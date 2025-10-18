open Ascii
open BinInt
open Bool
open Datatypes
open List0
open Nat
open QArith_base
open String0

val index_zip : 'a1 list -> (nat * 'a1) list

val str_ltb : char list -> char list -> bool

val coq_Q_of_Z : Big_int_Z.big_int -> coq_Q

val coq_Q_of_nat : nat -> coq_Q

module JSON :
 sig
  type value =
  | JNull
  | JBool of bool
  | JNum of coq_Q
  | JStr of char list
  | JArr of value list
  | JObject of (char list * value) list

  val value_rect :
    'a1 -> (bool -> 'a1) -> (coq_Q -> 'a1) -> (char list -> 'a1) -> (value
    list -> 'a1) -> ((char list * value) list -> 'a1) -> value -> 'a1

  val value_rec :
    'a1 -> (bool -> 'a1) -> (coq_Q -> 'a1) -> (char list -> 'a1) -> (value
    list -> 'a1) -> ((char list * value) list -> 'a1) -> value -> 'a1

  type step =
  | SName of char list
  | SIndex of Big_int_Z.big_int

  val step_rect :
    (char list -> 'a1) -> (Big_int_Z.big_int -> 'a1) -> step -> 'a1

  val step_rec :
    (char list -> 'a1) -> (Big_int_Z.big_int -> 'a1) -> step -> 'a1

  type path = step list

  type node = path * value
 end

val mk_node : JSON.path -> JSON.value -> JSON.node

module JSONPath :
 sig
  type prim =
  | PNull
  | PBool of bool
  | PNum of coq_Q
  | PStr of char list

  val prim_rect :
    'a1 -> (bool -> 'a1) -> (coq_Q -> 'a1) -> (char list -> 'a1) -> prim ->
    'a1

  val prim_rec :
    'a1 -> (bool -> 'a1) -> (coq_Q -> 'a1) -> (char list -> 'a1) -> prim ->
    'a1

  val prim_of_value : JSON.value -> prim option

  type cmp =
  | CEq
  | CNe
  | CLt
  | CLe
  | CGt
  | CGe

  val cmp_rect : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> cmp -> 'a1

  val cmp_rec : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> cmp -> 'a1

  type regex =
  | REmpty
  | REps
  | RChr of char
  | RAny
  | RAlt of regex * regex
  | RCat of regex * regex
  | RStar of regex
  | RPlus of regex
  | ROpt of regex
  | RRepeat of regex * nat * nat
  | RCharClass of bool * char list

  val regex_rect :
    'a1 -> 'a1 -> (char -> 'a1) -> 'a1 -> (regex -> 'a1 -> regex -> 'a1 ->
    'a1) -> (regex -> 'a1 -> regex -> 'a1 -> 'a1) -> (regex -> 'a1 -> 'a1) ->
    (regex -> 'a1 -> 'a1) -> (regex -> 'a1 -> 'a1) -> (regex -> 'a1 -> nat ->
    nat -> 'a1) -> (bool -> char list -> 'a1) -> regex -> 'a1

  val regex_rec :
    'a1 -> 'a1 -> (char -> 'a1) -> 'a1 -> (regex -> 'a1 -> regex -> 'a1 ->
    'a1) -> (regex -> 'a1 -> regex -> 'a1 -> 'a1) -> (regex -> 'a1 -> 'a1) ->
    (regex -> 'a1 -> 'a1) -> (regex -> 'a1 -> 'a1) -> (regex -> 'a1 -> nat ->
    nat -> 'a1) -> (bool -> char list -> 'a1) -> regex -> 'a1

  type aexpr =
  | APrim of prim
  | ACount of query
  | AValue of query
  | ALengthV of query
  and fexpr =
  | FTrue
  | FNot of fexpr
  | FAnd of fexpr * fexpr
  | FOr of fexpr * fexpr
  | FExists of query
  | FCmp of cmp * aexpr * aexpr
  | FMatch of aexpr * regex
  | FSearch of aexpr * regex
  and selector =
  | SelName of char list
  | SelWildcard
  | SelIndex of Big_int_Z.big_int
  | SelSlice of Big_int_Z.big_int option * Big_int_Z.big_int option
     * Big_int_Z.big_int
  | SelFilter of fexpr
  and segment =
  | Child of selector list
  | Desc of selector list
  and query =
  | Query of segment list

  val aexpr_rect :
    (prim -> 'a1) -> (query -> 'a1) -> (query -> 'a1) -> (query -> 'a1) ->
    aexpr -> 'a1

  val aexpr_rec :
    (prim -> 'a1) -> (query -> 'a1) -> (query -> 'a1) -> (query -> 'a1) ->
    aexpr -> 'a1

  val fexpr_rect :
    'a1 -> (fexpr -> 'a1 -> 'a1) -> (fexpr -> 'a1 -> fexpr -> 'a1 -> 'a1) ->
    (fexpr -> 'a1 -> fexpr -> 'a1 -> 'a1) -> (query -> 'a1) -> (cmp -> aexpr
    -> aexpr -> 'a1) -> (aexpr -> regex -> 'a1) -> (aexpr -> regex -> 'a1) ->
    fexpr -> 'a1

  val fexpr_rec :
    'a1 -> (fexpr -> 'a1 -> 'a1) -> (fexpr -> 'a1 -> fexpr -> 'a1 -> 'a1) ->
    (fexpr -> 'a1 -> fexpr -> 'a1 -> 'a1) -> (query -> 'a1) -> (cmp -> aexpr
    -> aexpr -> 'a1) -> (aexpr -> regex -> 'a1) -> (aexpr -> regex -> 'a1) ->
    fexpr -> 'a1

  val selector_rect :
    (char list -> 'a1) -> 'a1 -> (Big_int_Z.big_int -> 'a1) ->
    (Big_int_Z.big_int option -> Big_int_Z.big_int option ->
    Big_int_Z.big_int -> 'a1) -> (fexpr -> 'a1) -> selector -> 'a1

  val selector_rec :
    (char list -> 'a1) -> 'a1 -> (Big_int_Z.big_int -> 'a1) ->
    (Big_int_Z.big_int option -> Big_int_Z.big_int option ->
    Big_int_Z.big_int -> 'a1) -> (fexpr -> 'a1) -> selector -> 'a1

  val segment_rect :
    (selector list -> 'a1) -> (selector list -> 'a1) -> segment -> 'a1

  val segment_rec :
    (selector list -> 'a1) -> (selector list -> 'a1) -> segment -> 'a1

  val query_rect : (segment list -> 'a1) -> query -> 'a1

  val query_rec : (segment list -> 'a1) -> query -> 'a1

  val q_segs : query -> segment list
 end

module Regex :
 sig
  val nullable : JSONPath.regex -> bool

  val char_in_list : char -> char list -> bool

  val deriv : char -> JSONPath.regex -> JSONPath.regex

  val rsimpl : JSONPath.regex -> JSONPath.regex

  val deriv_simpl : char -> JSONPath.regex -> JSONPath.regex

  val list_of_string : char list -> char list

  val matches_from : JSONPath.regex -> char list -> bool

  val regex_match : JSONPath.regex -> char list -> bool

  val regex_search : JSONPath.regex -> char list -> bool
 end

module Exec :
 sig
  val prim_eq : JSONPath.prim -> JSONPath.prim -> bool

  val prim_lt : JSONPath.prim -> JSONPath.prim -> bool

  val cmp_prim : JSONPath.cmp -> JSONPath.prim -> JSONPath.prim -> bool

  val sel_exec_nf : JSONPath.selector -> JSON.node -> JSON.node list

  val visit_df_value : JSON.path -> JSON.value -> JSON.node list

  val visit_df_node : JSON.node -> JSON.node list

  val child_on_node_impl :
    (JSONPath.selector -> JSON.node -> JSON.node list) -> JSONPath.selector
    list -> JSON.node -> JSON.node list

  val seg_exec_impl :
    (JSONPath.selector -> JSON.node -> JSON.node list) -> JSONPath.segment ->
    JSON.node -> JSON.node list

  val segs_exec_impl :
    (JSONPath.selector -> JSON.node -> JSON.node list) -> JSONPath.segment
    list -> JSON.node list -> JSON.node list

  val eval_exec_impl :
    (JSONPath.selector -> JSON.node -> JSON.node list) -> JSONPath.query ->
    JSON.value -> JSON.node list

  val child_on_node_nf : JSONPath.selector list -> JSON.node -> JSON.node list

  val seg_exec_nf : JSONPath.segment -> JSON.node -> JSON.node list

  val segs_exec_nf : JSONPath.segment list -> JSON.node list -> JSON.node list

  val eval_exec_nf : JSONPath.query -> JSON.value -> JSON.node list

  val sel_exec : JSONPath.selector -> JSON.node -> JSON.node list

  val holds_b : JSONPath.fexpr -> JSON.node -> bool

  val aeval : JSONPath.aexpr -> JSON.value -> JSONPath.prim option

  val child_on_node : JSONPath.selector list -> JSON.node -> JSON.node list

  val seg_exec : JSONPath.segment -> JSON.node -> JSON.node list

  val segs_exec : JSONPath.segment list -> JSON.node list -> JSON.node list

  val eval_exec : JSONPath.query -> JSON.value -> JSON.node list
 end

module Typing :
 sig
  type primty =
  | TNull
  | TBool
  | TNum
  | TStr
  | TAnyPrim

  val primty_rect : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> primty -> 'a1

  val primty_rec : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> primty -> 'a1

  val selector_ok : JSONPath.selector -> bool

  val segment_ok : JSONPath.segment -> bool

  val singleton_query : JSONPath.query -> bool

  val aety : JSONPath.aexpr -> primty

  val comparable : primty -> primty -> bool

  val wf_fexpr : JSONPath.fexpr -> bool
 end

val coq_JQ : Big_int_Z.big_int -> JSON.value

val proj_phoenix_a : JSON.value

val proj_drake_a : JSON.value

val proj_phoenix_c : JSON.value

val proj_eagle_c : JSON.value

val proj_crm_d : JSON.value

val emp_alice : JSON.value

val emp_bob : JSON.value

val emp_carol : JSON.value

val emp_dave : JSON.value

val emp_erin : JSON.value

val dept_research : JSON.value

val dept_sales : JSON.value

val company_json : JSON.value

val acme_db_json : JSON.value
