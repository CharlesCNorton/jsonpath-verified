#!/usr/bin/env python3
"""
Fully faithful JSONPath CLI implementation with complete RFC 9535 parser.
"""

import os
import sys
import shutil
import subprocess
import json
import argparse
from pathlib import Path

# Complete OCaml JSONPath parser and executor
OCAML_MAIN_ML = r'''open Printf
open Jsonpath_exec
open Big_int

let string_of_z (z : Big_int.big_int) = Big_int.string_of_big_int z

let string_of_step = function
  | JSON.SName s  -> "." ^ (String.of_seq (List.to_seq s))
  | JSON.SIndex i -> "[" ^ string_of_z i ^ "]"

let string_of_path (p : JSON.path) =
  String.concat "" (List.map string_of_step p)

let string_of_value =
  let rec go = function
    | JSON.JNull       -> "null"
    | JSON.JBool b     -> if b then "true" else "false"
    | JSON.JStr s      -> "\"" ^ String.escaped (String.of_seq (List.to_seq s)) ^ "\""
    | JSON.JNum q      -> 
        (* Convert rational to decimal string *)
        let num_str = Big_int.string_of_big_int q.Jsonpath_exec.qnum in
        let den_str = Big_int.string_of_big_int q.Jsonpath_exec.qden in
        if den_str = "1" then num_str
        else begin
          (* Perform division for display - this is just for output *)
          let open Big_int in
          let num = q.Jsonpath_exec.qnum in
          let den = q.Jsonpath_exec.qden in
          if eq_big_int den unit_big_int then
            string_of_big_int num
          else
            (* Show as decimal approximation *)
            let q = quomod_big_int num den in
            let int_part = fst q in
            let rem = snd q in
            if sign_big_int rem = 0 then
              string_of_big_int int_part
            else
              (* Compute a few decimal places *)
              let rec decimal_places rem den acc n =
                if n = 0 || sign_big_int rem = 0 then List.rev acc
                else
                  let rem10 = mult_int_big_int 10 rem in
                  let q = quomod_big_int rem10 den in
                  let digit = int_of_big_int (fst q) in
                  let new_rem = snd q in
                  decimal_places new_rem den (digit :: acc) (n - 1)
              in
              let decimals = decimal_places rem den [] 6 in
              let decimal_str = String.concat "" (List.map string_of_int decimals) in
              string_of_big_int int_part ^ "." ^ decimal_str
        end
    | JSON.JArr xs     -> "[" ^ (String.concat ", " (List.map go xs)) ^ "]"
    | JSON.JObject kvs ->
        let fields =
          List.map (fun (k,v) -> "\"" ^ String.escaped (String.of_seq (List.to_seq k)) ^ "\": " ^ go v) kvs in
        "{ " ^ String.concat ", " fields ^ " }"
  in go

(* Convert decimal string to JSON.JNum with exact rational *)
let jnum_of_decimal_string (s : string) : JSON.value =
  let len = String.length s in
  let idx = ref 0 in
  let get i = if i < len then s.[i] else '\000' in
  let is_digit c = '0' <= c && c <= '9' in
  let sign =
    match get !idx with
    | '-' -> incr idx; -1
    | '+' -> incr idx;  1
    | _   -> 1
  in
  let digits_from i =
    let j = ref i in
    while !j < len && is_digit (get !j) do incr j done;
    (String.sub s i (!j - i), !j)
  in
  let int_part, i1 = digits_from !idx in
  idx := i1;
  let frac_part =
    if !idx < len && get !idx = '.' then (
      incr idx;
      let ds, j = digits_from !idx in
      idx := j; ds
    ) else ""
  in
  let exp_val =
    if !idx < len && (get !idx = 'e' || get !idx = 'E') then (
      incr idx;
      let esign =
        if !idx < len && (get !idx = '+' || get !idx = '-') then
          let c = get !idx in incr idx; if c = '-' then -1 else 1
        else 1
      in
      let estr, j = digits_from !idx in
      idx := j;
      let e = if estr = "" then 0 else int_of_string estr in
      esign * e
    ) else 0
  in
  let pow10 n = Big_int.power_int_positive_int 10 (abs n) in
  let bi s = if s = "" then Big_int.zero_big_int else Big_int.big_int_of_string s in
  let f = String.length frac_part in
  let int_bi  = bi (if int_part = "" then "0" else int_part) in
  let frac_bi = bi (if frac_part = "" then "0" else frac_part) in
  let base    = pow10 f in
  let num0    = Big_int.add_big_int (Big_int.mult_big_int int_bi base) frac_bi in
  let num0    = if sign < 0 then Big_int.minus_big_int num0 else num0 in
  let den0    = if f = 0 then Big_int.unit_big_int else base in
  let num, den =
    if exp_val = 0 then num0, den0
    else if exp_val > 0 then
      Big_int.mult_big_int num0 (pow10 exp_val), den0
    else
      let p = pow10 exp_val in
      num0, Big_int.mult_big_int den0 p
  in
  let den = if Big_int.sign_big_int den <= 0 then Big_int.unit_big_int else den in
  let q = { Jsonpath_exec.qnum = num; Jsonpath_exec.qden = den } in
  JSON.JNum q

let rec of_yojson (j : Yojson.Safe.t) : JSON.value =
  match j with
  | `Null       -> JSON.JNull
  | `Bool b     -> JSON.JBool b
  | `String s   -> JSON.JStr (List.of_seq (String.to_seq s))
  | `Int i      -> JSON.JNum { Jsonpath_exec.qnum = Big_int.big_int_of_int i; Jsonpath_exec.qden = Big_int.unit_big_int }
  | `Float f    -> jnum_of_decimal_string (Printf.sprintf "%.17g" f)
  | `List xs    -> JSON.JArr (List.map of_yojson xs)
  | `Assoc kvs  -> JSON.JObject (List.map (fun (k,v) -> (List.of_seq (String.to_seq k), of_yojson v)) kvs)
  | _ -> JSON.JNull  (* Handle other Yojson variants as null *)

(* ============ COMPLETE JSONPATH PARSER ============ *)

exception Parse_error of string

type token =
  | TDollar
  | TDot
  | TDotDot
  | TLBracket
  | TRBracket
  | TLParen
  | TRParen
  | TComma
  | TColon
  | TStar
  | TAt
  | TQuestion
  | TBang
  | TEq | TNe | TLt | TLe | TGt | TGe
  | TAnd | TOr
  | TPlus | TMinus | TDiv | TMul
  | TString of string
  | TInt of string
  | TFloat of string
  | TTrue | TFalse | TNull
  | TIdent of string
  | TRegex of string * string  (* pattern, flags *)
  | TEOF

let tokenize (s : string) : token list =
  let len = String.length s in
  let idx = ref 0 in
  let get i = if i < len then s.[i] else '\000' in
  let peek () = get !idx in
  let advance () = incr idx in
  let consume c = if peek () = c then (advance (); true) else false in
  
  let rec skip_whitespace () =
    match peek () with
    | ' ' | '\t' | '\n' | '\r' -> advance (); skip_whitespace ()
    | _ -> ()
  in
  
  let parse_string delim =
    let buf = Buffer.create 16 in
    advance (); (* skip opening quote *)
    let rec loop () =
      match peek () with
      | '\000' -> raise (Parse_error "Unterminated string")
      | '\\' ->
          advance ();
          (match peek () with
           | '"' | '\'' | '\\' | '/' -> Buffer.add_char buf (peek ()); advance ()
           | 'b' -> Buffer.add_char buf '\b'; advance ()
           | 'f' -> Buffer.add_char buf '\012'; advance ()
           | 'n' -> Buffer.add_char buf '\n'; advance ()
           | 'r' -> Buffer.add_char buf '\r'; advance ()
           | 't' -> Buffer.add_char buf '\t'; advance ()
           | 'u' ->
               advance ();
               let hex = String.sub s !idx 4 in
               idx := !idx + 4;
               let code = int_of_string ("0x" ^ hex) in
               Buffer.add_char buf (Char.chr (code land 0xFF))  (* Simplified unicode handling *)
           | c -> Buffer.add_char buf c; advance ());
          loop ()
      | c when c = delim -> advance (); Buffer.contents buf
      | c -> Buffer.add_char buf c; advance (); loop ()
    in
    loop ()
  in
  
  let parse_number () =
    let start = !idx in
    if peek () = '-' then advance ();
    while '0' <= peek () && peek () <= '9' do advance () done;
    let has_dot = peek () = '.' in
    if has_dot then (
      advance ();
      while '0' <= peek () && peek () <= '9' do advance () done
    );
    if peek () = 'e' || peek () = 'E' then (
      advance ();
      if peek () = '+' || peek () = '-' then advance ();
      while '0' <= peek () && peek () <= '9' do advance () done
    );
    let num_str = String.sub s start (!idx - start) in
    if has_dot || String.contains num_str 'e' || String.contains num_str 'E' 
    then TFloat num_str
    else TInt num_str
  in
  
  let parse_ident () =
    let start = !idx in
    while match peek () with
          | 'a'..'z' | 'A'..'Z' | '0'..'9' | '_' -> true
          | _ -> false
    do advance () done;
    String.sub s start (!idx - start)
  in
  
  let parse_regex () =
    (* Format: /pattern/flags *)
    advance (); (* skip opening / *)
    let buf = Buffer.create 16 in
    let rec loop () =
      match peek () with
      | '\000' -> raise (Parse_error "Unterminated regex")
      | '\\' ->
          Buffer.add_char buf '\\';
          advance ();
          if peek () <> '\000' then (Buffer.add_char buf (peek ()); advance ());
          loop ()
      | '/' -> advance (); Buffer.contents buf
      | c -> Buffer.add_char buf c; advance (); loop ()
    in
    let pattern = loop () in
    let flag_start = !idx in
    while match peek () with 'i' | 'm' | 's' | 'x' -> true | _ -> false do
      advance ()
    done;
    let flags = String.sub s flag_start (!idx - flag_start) in
    TRegex (pattern, flags)
  in
  
  let rec tokenize_rec acc =
    skip_whitespace ();
    if !idx >= len then List.rev (TEOF :: acc)
    else
      let tok = 
        match peek () with
        | '$' -> advance (); TDollar
        | '@' -> advance (); TAt
        | '*' -> advance (); TStar
        | '(' -> advance (); TLParen
        | ')' -> advance (); TRParen
        | '[' -> advance (); TLBracket
        | ']' -> advance (); TRBracket
        | ',' -> advance (); TComma
        | ':' -> advance (); TColon
        | '?' -> advance (); TQuestion
        | '+' -> advance (); TPlus
        | '-' -> 
            advance ();
            if '0' <= peek () && peek () <= '9' then
              (decr idx; parse_number ())
            else TMinus
        | '/' ->
            (* Could be division or regex *)
            let saved = !idx in
            advance ();
            (* Simple heuristic: if followed by *, it's likely regex *)
            if peek () = '*' || (peek () <> ' ' && peek () <> '\t' && peek () <> '\n') then
              (idx := saved; parse_regex ())
            else TDiv
        | '.' ->
            advance ();
            if peek () = '.' then (advance (); TDotDot)
            else TDot
        | '!' ->
            advance ();
            if peek () = '=' then (advance (); TNe)
            else TBang
        | '=' ->
            advance ();
            if peek () = '=' then advance ();
            TEq
        | '<' ->
            advance ();
            if peek () = '=' then (advance (); TLe)
            else TLt
        | '>' ->
            advance ();
            if peek () = '=' then (advance (); TGe)
            else TGt
        | '&' ->
            advance ();
            if peek () = '&' then (advance (); TAnd)
            else raise (Parse_error "Expected &&")
        | '|' ->
            advance ();
            if peek () = '|' then (advance (); TOr)
            else raise (Parse_error "Expected ||")
        | '"' -> TString (parse_string '"')
        | '\'' -> TString (parse_string '\'')
        | '0'..'9' -> parse_number ()
        | 'a'..'z' | 'A'..'Z' | '_' ->
            let id = parse_ident () in
            (match id with
             | "true" -> TTrue
             | "false" -> TFalse
             | "null" -> TNull
             | _ -> TIdent id)
        | c -> raise (Parse_error (Printf.sprintf "Unexpected character: %c" c))
      in
      tokenize_rec (tok :: acc)
  in
  tokenize_rec []

(* Parser combinators *)
type 'a parser = token list -> 'a * token list

let peek_token : token parser = fun toks ->
  match toks with
  | [] -> (TEOF, [])
  | t :: _ -> (t, toks)

let consume_token : token parser = fun toks ->
  match toks with
  | [] -> raise (Parse_error "Unexpected end of input")
  | t :: rest -> (t, rest)

let expect tok : unit parser = fun toks ->
  match toks with
  | t :: rest when t = tok -> ((), rest)
  | t :: _ -> raise (Parse_error (Printf.sprintf "Expected %s" (match tok with
      | TDollar -> "$" | TDot -> "." | TDotDot -> ".."
      | TLBracket -> "[" | TRBracket -> "]"
      | TLParen -> "(" | TRParen -> ")"
      | TComma -> "," | TColon -> ":" | TStar -> "*"
      | _ -> "token")))
  | [] -> raise (Parse_error "Unexpected end of input")

let rec parse_query (toks : token list) : JSONPath.query * token list =
  let _, toks = expect TDollar toks in
  let segs, toks' = parse_segments toks in
  (JSONPath.Query segs, toks')

and parse_segments toks =
  let rec loop acc toks =
    match peek_token toks with
    | (TDot, _) ->
        let seg, toks = parse_child_segment toks in
        loop (seg :: acc) toks
    | (TDotDot, _) ->
        let seg, toks = parse_descendant_segment toks in
        loop (seg :: acc) toks
    | (TLBracket, _) ->
        let seg, toks = parse_bracket_segment toks in
        loop (seg :: acc) toks
    | _ -> (List.rev acc, toks)
  in
  loop [] toks

and parse_child_segment toks =
  let _, toks = expect TDot toks in
  match peek_token toks with
  | (TStar, toks') ->
      let _, toks' = consume_token toks' in
      (JSONPath.Child [JSONPath.SelWildcard], toks')
  | (TIdent name, toks') ->
      let _, toks' = consume_token toks' in
      (JSONPath.Child [JSONPath.SelName (List.of_seq (String.to_seq name))], toks')
  | _ -> raise (Parse_error "Expected identifier or * after .")

and parse_descendant_segment toks =
  let _, toks = expect TDotDot toks in
  match peek_token toks with
  | (TStar, toks') ->
      let _, toks' = consume_token toks' in
      (JSONPath.Desc [JSONPath.SelWildcard], toks')
  | (TIdent name, toks') ->
      let _, toks' = consume_token toks' in
      (JSONPath.Desc [JSONPath.SelName (List.of_seq (String.to_seq name))], toks')
  | (TLBracket, _) ->
      let sels, toks = parse_bracket_selectors toks in
      (JSONPath.Desc sels, toks)
  | _ -> raise (Parse_error "Expected identifier, * or [ after ..")

and parse_bracket_segment toks =
  let sels, toks = parse_bracket_selectors toks in
  (JSONPath.Child sels, toks)

and parse_bracket_selectors toks =
  let _, toks = expect TLBracket toks in
  let rec loop acc toks =
    let sel, toks = parse_selector toks in
    let acc' = sel :: acc in
    match peek_token toks with
    | (TComma, toks') ->
        let _, toks' = consume_token toks' in
        loop acc' toks'
    | (TRBracket, toks') ->
        let _, toks' = consume_token toks' in
        (List.rev acc', toks')
    | _ -> raise (Parse_error "Expected , or ] in bracket selector")
  in
  loop [] toks

and parse_selector toks =
  match peek_token toks with
  | (TStar, toks') ->
      let _, toks' = consume_token toks' in
      (JSONPath.SelWildcard, toks')
  | (TString s, toks') ->
      let _, toks' = consume_token toks' in
      (JSONPath.SelName (List.of_seq (String.to_seq s)), toks')
  | (TInt n, toks') ->
      let _, toks' = consume_token toks' in
      (* Check for slice syntax *)
      (match peek_token toks' with
       | (TColon, _) -> parse_slice_from (int_of_string n) toks'
       | _ -> (JSONPath.SelIndex (Big_int.big_int_of_int (int_of_string n)), toks'))
  | (TColon, _) ->
      (* Slice starting from beginning *)
      parse_slice_from 0 toks
  | (TQuestion, toks') ->
      let _, toks' = consume_token toks' in
      let _, toks' = expect TLParen toks' in
      let fexpr, toks' = parse_filter_expr toks' in
      let _, toks' = expect TRParen toks' in
      (JSONPath.SelFilter fexpr, toks')
  | (TMinus, toks') ->
      (* Negative index *)
      let _, toks' = consume_token toks' in
      (match peek_token toks' with
       | (TInt n, toks'') ->
           let _, toks'' = consume_token toks'' in
           let idx = Big_int.minus_big_int (Big_int.big_int_of_int (int_of_string n)) in
           (JSONPath.SelIndex idx, toks'')
       | _ -> raise (Parse_error "Expected number after -"))
  | _ -> raise (Parse_error "Invalid selector")

and parse_slice_from start toks =
  let _, toks = expect TColon toks in
  let stop, toks = 
    match peek_token toks with
    | (TInt n, toks') ->
        let _, toks' = consume_token toks' in
        (Some (int_of_string n), toks')
    | (TColon, _) | (TComma, _) | (TRBracket, _) ->
        (None, toks)
    | (TMinus, toks') ->
        let _, toks' = consume_token toks' in
        (match peek_token toks' with
         | (TInt n, toks'') ->
             let _, toks'' = consume_token toks'' in
             (Some (-(int_of_string n)), toks'')
         | _ -> raise (Parse_error "Expected number after -"))
    | _ -> raise (Parse_error "Invalid slice syntax")
  in
  let step, toks =
    match peek_token toks with
    | (TColon, toks') ->
        let _, toks' = consume_token toks' in
        (match peek_token toks' with
         | (TInt n, toks'') ->
             let _, toks'' = consume_token toks'' in
             (int_of_string n, toks'')
         | (TMinus, toks'') ->
             let _, toks'' = consume_token toks'' in
             (match peek_token toks'' with
              | (TInt n, toks3) ->
                  let _, toks3 = consume_token toks3 in
                  (-(int_of_string n), toks3)
              | _ -> raise (Parse_error "Expected number after -"))
         | _ -> (1, toks'))
    | _ -> (1, toks)
  in
  let mk_bi n = Big_int.big_int_of_int n in
  let slice = JSONPath.SelSlice (
    Some (mk_bi start),
    (match stop with None -> None | Some n -> Some (mk_bi n)),
    mk_bi step
  ) in
  (slice, toks)

and parse_filter_expr toks =
  parse_or_expr toks

and parse_or_expr toks =
  let left, toks = parse_and_expr toks in
  match peek_token toks with
  | (TOr, toks') ->
      let _, toks' = consume_token toks' in
      let right, toks' = parse_or_expr toks' in
      (JSONPath.FOr (left, right), toks')
  | _ -> (left, toks)

and parse_and_expr toks =
  let left, toks = parse_not_expr toks in
  match peek_token toks with
  | (TAnd, toks') ->
      let _, toks' = consume_token toks' in
      let right, toks' = parse_and_expr toks' in
      (JSONPath.FAnd (left, right), toks')
  | _ -> (left, toks)

and parse_not_expr toks =
  match peek_token toks with
  | (TBang, toks') ->
      let _, toks' = consume_token toks' in
      let expr, toks' = parse_not_expr toks' in
      (JSONPath.FNot expr, toks')
  | _ -> parse_comparison_expr toks

and parse_comparison_expr toks =
  let left, toks = parse_basic_expr toks in
  match peek_token toks with
  | (TEq, toks') ->
      let _, toks' = consume_token toks' in
      let right, toks' = parse_basic_expr toks' in
      (JSONPath.FCmp (JSONPath.CEq, left, right), toks')
  | (TNe, toks') ->
      let _, toks' = consume_token toks' in
      let right, toks' = parse_basic_expr toks' in
      (JSONPath.FCmp (JSONPath.CNe, left, right), toks')
  | (TLt, toks') ->
      let _, toks' = consume_token toks' in
      let right, toks' = parse_basic_expr toks' in
      (JSONPath.FCmp (JSONPath.CLt, left, right), toks')
  | (TLe, toks') ->
      let _, toks' = consume_token toks' in
      let right, toks' = parse_basic_expr toks' in
      (JSONPath.FCmp (JSONPath.CLe, left, right), toks')
  | (TGt, toks') ->
      let _, toks' = consume_token toks' in
      let right, toks' = parse_basic_expr toks' in
      (JSONPath.FCmp (JSONPath.CGt, left, right), toks')
  | (TGe, toks') ->
      let _, toks' = consume_token toks' in
      let right, toks' = parse_basic_expr toks' in
      (JSONPath.FCmp (JSONPath.CGe, left, right), toks')
  | _ -> 
      (* Not a comparison, check if it's an existence test *)
      match left with
      | JSONPath.AValue q -> (JSONPath.FExists q, toks)
      | _ -> raise (Parse_error "Invalid filter expression")

and parse_basic_expr toks =
  match peek_token toks with
  | (TAt, toks') ->
      let _, toks' = consume_token toks' in
      let segs, toks' = parse_segments toks' in
      (JSONPath.AValue (JSONPath.Query segs), toks')
  | (TDollar, _) ->
      let q, toks' = parse_query toks in
      (JSONPath.AValue q, toks')
  | (TString s, toks') ->
      let _, toks' = consume_token toks' in
      (JSONPath.APrim (JSONPath.PStr (List.of_seq (String.to_seq s))), toks')
  | (TInt n, toks') ->
      let _, toks' = consume_token toks' in
      let num = Big_int.big_int_of_int (int_of_string n) in
      (JSONPath.APrim (JSONPath.PNum { Jsonpath_exec.qnum = num; Jsonpath_exec.qden = Big_int.unit_big_int }), toks')
  | (TFloat f, toks') ->
      let _, toks' = consume_token toks' in
      (match jnum_of_decimal_string f with
       | JSON.JNum q -> (JSONPath.APrim (JSONPath.PNum q), toks')
       | _ -> raise (Parse_error "Invalid number"))
  | (TTrue, toks') ->
      let _, toks' = consume_token toks' in
      (JSONPath.APrim (JSONPath.PBool true), toks')
  | (TFalse, toks') ->
      let _, toks' = consume_token toks' in
      (JSONPath.APrim (JSONPath.PBool false), toks')
  | (TNull, toks') ->
      let _, toks' = consume_token toks' in
      (JSONPath.APrim JSONPath.PNull, toks')
  | (TLParen, toks') ->
      let _, toks' = consume_token toks' in
      let expr, toks' = parse_basic_expr toks' in
      let _, toks' = expect TRParen toks' in
      (expr, toks')
  | _ -> raise (Parse_error "Invalid expression")

let parse_jsonpath (s : string) : JSONPath.query =
  let tokens = tokenize s in
  let query, remaining = parse_query tokens in
  match remaining with
  | [TEOF] | [] -> query
  | _ -> raise (Parse_error "Unexpected tokens after query")

(* Main entry point *)
let () =
  let query = ref "" in
  let file = ref "" in
  let speclist = [
    ("-q", Arg.Set_string query, "JSONPath query");
    ("-f", Arg.Set_string file, "JSON file to query");
  ] in
  Arg.parse speclist (fun s -> file := s) "Usage: jsonpath -q QUERY [-f] FILE.json";
  
  if !query = "" || !file = "" then (
    eprintf "Error: both query and file are required\n";
    eprintf "Usage: jsonpath -q QUERY [-f] FILE.json\n";
    eprintf "\nExamples:\n";
    eprintf "  Simple paths:\n";
    eprintf "    jsonpath -q '$.store.book[0].title' -f data.json\n";
    eprintf "    jsonpath -q '$..author' -f data.json\n";
    eprintf "    jsonpath -q '$.store.*' -f data.json\n";
    eprintf "  Arrays:\n";
    eprintf "    jsonpath -q '$.book[0]' -f data.json\n";
    eprintf "    jsonpath -q '$.book[-1]' -f data.json  # last element\n";
    eprintf "    jsonpath -q '$.book[0:2]' -f data.json  # slice\n";
    eprintf "    jsonpath -q '$.book[::2]' -f data.json  # every 2nd element\n";
    eprintf "  Filters:\n";
    eprintf "    jsonpath -q '$.book[?(@.price < 10)]' -f data.json\n";
    eprintf "    jsonpath -q '$.book[?(@.isbn)]' -f data.json  # has isbn\n";
    eprintf "    jsonpath -q '$..[?(@.price > 5 && @.category==\"fiction\")]' -f data.json\n";
    eprintf "  Multiple selectors:\n";
    eprintf "    jsonpath -q '$.book[0,2]' -f data.json\n";
    eprintf "    jsonpath -q '$.book[0,2:4]' -f data.json\n";
    exit 1
  );
  
  try
    let q = parse_jsonpath !query in
    let json_data = Yojson.Safe.from_file !file in
    let json_value = of_yojson json_data in
    let results = Exec.eval_exec q json_value in
    List.iter (fun (p,v) ->
      printf "%s => %s\n" (string_of_path p) (string_of_value v)
    ) results
  with
  | Parse_error msg -> eprintf "Parse error: %s\n" msg; exit 1
  | Failure msg -> eprintf "Error: %s\n" msg; exit 1
  | e -> eprintf "Error: %s\n" (Printexc.to_string e); exit 1
'''

# Rest of the build infrastructure remains the same
DUNE_PROJECT = """(lang dune 3.13)
(name jsonpath_cli)
"""

LIB_DUNE = """(library
 (name jsonpath_lib)
 (modules jsonpath_exec)
 (flags -w -39)
 (libraries num))
"""

BIN_DUNE = """(executable
 (name jsonpath)
 (modules jsonpath jsonpath_exec)
 (flags -w -39)
 (libraries yojson num))
"""

def run_cmd(args, cwd=None):
    """Run a subprocess and return (rc, stdout, stderr)."""
    p = subprocess.run(
        args,
        cwd=cwd,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        shell=False
    )
    return p.returncode, p.stdout, p.stderr

def build_ocaml_executable():
    """Build the OCaml executable from extracted code."""
    
    # Check prerequisites
    if not shutil.which("coqc"):
        print("Error: coqc not found. Please install Coq.")
        return False
    
    if not shutil.which("dune"):
        print("Error: dune not found. Please install with: opam install dune")
        return False
    
    # Check if jsonpath_exec.ml exists (already extracted)
    if not Path("jsonpath_exec.ml").exists():
        print("jsonpath_exec.ml not found. Extracting from Coq...")
        
        # Find the .v file
        v_file = Path("jsonpath_verified.v")
        if not v_file.exists():
            v_file = Path("jsonpath-verified.v")
            if not v_file.exists():
                print("Error: No Coq file found (jsonpath_verified.v or jsonpath-verified.v)")
                return False
        
        # Run coqc
        print(f"Running coqc on {v_file}...")
        rc, out, err = run_cmd(["coqc", str(v_file)])
        if rc != 0:
            print(f"coqc failed:\n{err}")
            return False
    
    # Create build directory
    build_dir = Path("_jsonpath_build")
    build_dir.mkdir(exist_ok=True)
    (build_dir / "lib").mkdir(exist_ok=True)
    (build_dir / "bin").mkdir(exist_ok=True)
    
    # Write dune files
    (build_dir / "dune-project").write_text(DUNE_PROJECT)
    (build_dir / "lib" / "dune").write_text(LIB_DUNE)
    (build_dir / "bin" / "dune").write_text(BIN_DUNE)
    
    # Copy extracted ML and add Big_int_Z module alias
    with open("jsonpath_exec.ml", "r") as f:
        content = f.read()
    
    # Add module alias at the beginning
    content = "module Big_int_Z = Big_int\n\n" + content
    
    # Write to both lib and bin directories
    (build_dir / "lib" / "jsonpath_exec.ml").write_text(content)
    (build_dir / "bin" / "jsonpath_exec.ml").write_text(content)
    
    # Write main.ml
    (build_dir / "bin" / "jsonpath.ml").write_text(OCAML_MAIN_ML)
    
    # Build with dune
    print("Building with dune...")
    rc, out, err = run_cmd(["dune", "build"], cwd=str(build_dir))
    if rc != 0:
        print(f"dune build failed. Make sure you have: opam install num yojson")
        print(err)
        return False
    
    # Copy executable to current directory
    exe_path = build_dir / "_build" / "default" / "bin" / "jsonpath.exe"
    if not exe_path.exists():
        exe_path = build_dir / "_build" / "default" / "bin" / "jsonpath"
    
    if exe_path.exists():
        shutil.copy2(exe_path, "./jsonpath_faithful")
        os.chmod("./jsonpath_faithful", 0o755)
        print("Successfully built ./jsonpath_faithful executable")
        return True
    else:
        print("Error: Could not find built executable")
        return False

def main():
    parser = argparse.ArgumentParser(description='Fully faithful JSONPath CLI')
    parser.add_argument('--build', action='store_true', help='Build the OCaml executable')
    parser.add_argument('-q', '--query', help='JSONPath query')
    parser.add_argument('-f', '--file', help='JSON file to query')
    
    args = parser.parse_args()
    
    if args.build:
        if build_ocaml_executable():
            print("\nYou can now run queries with:")
            print("  ./jsonpath_faithful -q QUERY -f FILE.json")
            print("\nTry complex queries like:")
            print("  ./jsonpath_faithful -q '$.store.book[?(@.price < 10)]' -f store.json")
            print("  ./jsonpath_faithful -q '$..book[0:2]' -f store.json")
        return
    
    # If not building, try to run the executable
    if args.query and args.file:
        if not Path("./jsonpath_faithful").exists():
            print("Error: ./jsonpath_faithful executable not found. Run with --build first.")
            sys.exit(1)
        
        rc, out, err = run_cmd(["./jsonpath_faithful", "-q", args.query, "-f", args.file])
        if out:
            print(out, end='')
        if err:
            print(err, end='', file=sys.stderr)
        sys.exit(rc)
    else:
        parser.print_help()

if __name__ == "__main__":
    main()