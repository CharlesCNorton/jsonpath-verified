#!/usr/bin/env python3
"""
Command-line JSONPath runner for Coq-extracted OCaml code.
"""

import os
import sys
import shutil
import subprocess
import json
import argparse
from pathlib import Path

# OCaml harness code
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
    | JSON.JNum _q     -> "<num>"
    | JSON.JArr xs     -> "[" ^ (String.concat ", " (List.map go xs)) ^ "]"
    | JSON.JObject kvs ->
        let fields =
          List.map (fun (k,v) -> "\"" ^ String.escaped (String.of_seq (List.to_seq k)) ^ "\": " ^ go v) kvs in
        "{ " ^ String.concat ", " fields ^ " }"
  in go

let print_nodes (nodes : JSON.node list) =
  List.iter (fun (p,v) ->
    printf "%s => %s\n" (string_of_path p) (string_of_value v)
  ) nodes

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

let parse_query (q : string) : JSONPath.query =
  (* Simple query parser for common JSONPath expressions *)
  let len = String.length q in
  if len = 0 then failwith "Empty query" else
  if q = "$" then JSONPath.Query [] else
  if q = "$..*" then JSONPath.Query [ JSONPath.Desc [ JSONPath.SelWildcard ] ] else
  if len > 3 && String.sub q 0 3 = "$.." then
    let name = String.sub q 3 (len - 3) in
    JSONPath.Query [ JSONPath.Desc [ JSONPath.SelName (List.of_seq (String.to_seq name)) ] ]
  else if len > 2 && String.sub q 0 2 = "$." then
    let name = String.sub q 2 (len - 2) in
    JSONPath.Query [ JSONPath.Child [ JSONPath.SelName (List.of_seq (String.to_seq name)) ] ]
  else if len > 2 && String.sub q 0 2 = "$[" && q.[len-1] = ']' then
    let idx_str = String.sub q 2 (len - 3) in
    let idx = int_of_string idx_str in
    JSONPath.Query [ JSONPath.Child [ JSONPath.SelIndex (Big_int.big_int_of_int idx) ] ]
  else
    failwith ("Unsupported query format: " ^ q)

let () =
  let query = ref "" in
  let file = ref "" in
  let speclist = [
    ("-q", Arg.Set_string query, "JSONPath query (e.g., '$.name', '$..id', '$..*')");
    ("-f", Arg.Set_string file, "JSON file to query");
  ] in
  Arg.parse speclist (fun s -> file := s) "Usage: jsonpath -q QUERY [-f] FILE.json";
  
  if !query = "" || !file = "" then (
    eprintf "Error: both query and file are required\n";
    eprintf "Usage: jsonpath -q QUERY [-f] FILE.json\n";
    eprintf "Examples:\n";
    eprintf "  jsonpath -q '$.name' -f data.json\n";
    eprintf "  jsonpath -q '$..id' -f data.json\n";
    eprintf "  jsonpath -q '$..*' -f data.json\n";
    exit 1
  );
  
  try
    let q = parse_query !query in
    let json_data = Yojson.Safe.from_file !file in
    let json_value = of_yojson json_data in
    let results = Exec.eval_exec q json_value in
    List.iter (fun (p,v) ->
      printf "%s => %s\n" (string_of_path p) (string_of_value v)
    ) results
  with
  | Failure msg -> eprintf "Error: %s\n" msg; exit 1
  | e -> eprintf "Error: %s\n" (Printexc.to_string e); exit 1
'''

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
        shutil.copy2(exe_path, "./jsonpath")
        os.chmod("./jsonpath", 0o755)
        print("Successfully built ./jsonpath executable")
        return True
    else:
        print("Error: Could not find built executable")
        return False

def main():
    parser = argparse.ArgumentParser(description='JSONPath CLI runner')
    parser.add_argument('--build', action='store_true', help='Build the OCaml executable')
    parser.add_argument('-q', '--query', help='JSONPath query')
    parser.add_argument('-f', '--file', help='JSON file to query')
    parser.add_argument('--example', action='store_true', help='Show example usage')
    
    args = parser.parse_args()
    
    if args.example:
        print("Example usage:")
        print("  1. Build the executable:")
        print("     python3 jsonpath_cli.py --build")
        print("  2. Create a test JSON file:")
        print("     echo '{\"name\": \"Alice\", \"age\": 30, \"items\": [{\"id\": 1}, {\"id\": 2}]}' > test.json")
        print("  3. Run queries:")
        print("     ./jsonpath -q '$.name' -f test.json")
        print("     ./jsonpath -q '$..id' -f test.json")
        print("     ./jsonpath -q '$..*' -f test.json")
        return
    
    if args.build:
        if build_ocaml_executable():
            print("\nYou can now run queries with:")
            print("  ./jsonpath -q QUERY -f FILE.json")
        return
    
    # If not building, try to run the executable
    if args.query and args.file:
        if not Path("./jsonpath").exists():
            print("Error: ./jsonpath executable not found. Run with --build first.")
            sys.exit(1)
        
        rc, out, err = run_cmd(["./jsonpath", "-q", args.query, "-f", args.file])
        if out:
            print(out, end='')
        if err:
            print(err, end='', file=sys.stderr)
        sys.exit(rc)
    else:
        parser.print_help()

if __name__ == "__main__":
    main()