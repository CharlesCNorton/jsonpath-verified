From Coq Require Import Init.Prelude.
From Coq Require Import
  List String Ascii ZArith Arith Lia Bool
  Sorting.Permutation QArith QArith_base.

Require Export JPV_Extensions.

Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Module API.
  Import JSON JSONPath Exec Typing JSONPath_Equiv.

  (* Small error space suitable for user-facing messages. *)
  Inductive exec_error :=
  | E_NotWF          (* query fails static wf check for filters/regexes *)
  | E_NotChildOnly   (* query uses Desc/filters; not supported by nf engine *)
  | E_NotLinear      (* query is not in the linear fragment *)
  | E_NotFound       (* linear: evaluated to [] *)
  | E_Multiple.      (* linear: evaluated to >1 *)

  (* Pretty printer for errors (useful when extracting). *)
  Definition show_error (e:exec_error) : string :=
    match e with
    | E_NotWF        => "not_wf"
    | E_NotChildOnly => "not_child_only"
    | E_NotLinear    => "not_linear"
    | E_NotFound     => "not_found"
    | E_Multiple     => "multiple_results"
    end.

  (* Executable well-formedness for filters inside selectors. *)
  Definition wf_selector (sel:selector) : bool :=
    match sel with
    | SelFilter f => Typing.wf_fexpr f
    | _ => true
    end.

  Definition wf_segment (seg:segment) : bool :=
    match seg with
    | Child sels | Desc sels => forallb wf_selector sels
    end.

  Definition wf_query (q:query) : bool :=
    match q with Query segs => forallb wf_segment segs end.

  (* A simple result type; we map it to OCaml's ('a,'e) result on extraction. *)
  Inductive result (A E:Type) :=
  | Ok    (a:A)
  | Error (e:E).
  Arguments Ok   {A E} _.
  Arguments Error{A E} _.

  (* Full evaluator with filter/regex wf guard. *)
  Definition eval_checked (q:query) (J:value)
    : result (list node) exec_error :=
    if wf_query q then Ok (eval_exec q J) else Error E_NotWF.

  (* Filter-free/child-only evaluator guard for the nf engine. *)
  Definition eval_nf_checked (q:query) (J:value)
    : result (list node) exec_error :=
    if query_child_only q
    then Ok (eval_exec_nf q J)
    else Error E_NotChildOnly.

  (* Linear queries return exactly zero or one result; expose as result. *)
  Definition eval_one_linear (q:query) (J:value)
    : result node exec_error :=
    if linear_query q then
      match eval_exec_nf q J with
      | [n] => Ok n
      | []  => Error E_NotFound
      | _   => Error E_Multiple
      end
    else Error E_NotLinear.

  (* QoL: projections *)
  Definition values_of (ns:list node) : list value := map snd ns.
  Definition paths_of  (ns:list node) : list path  := map fst ns.
End API.

(* ------------------------------------------------------------ *)
(* QuickChick section                                            *)
(* ------------------------------------------------------------ *)
(* This monolithic file is kept free of QuickChick dependencies
   so that raw `coqc -q jsonpath_verified.v` works in a base Rocq/Coq
   install. Property-based tests live in `quickchick_run.v`. *)

(* ------------------------------------------------------------ *)
(* OCaml Extraction                                             *)
(* ------------------------------------------------------------ *)

From Coq Require Import Extraction.
Require Import Coq.extraction.ExtrOcamlBasic.
Require Import Coq.extraction.ExtrOcamlString.
Require Import Coq.extraction.ExtrOcamlChar.
Require Import Coq.extraction.ExtrOcamlZBigInt.

Set Extraction KeepSingleton.
Extraction Language OCaml.
Extraction Blacklist String List Int Z.

Extraction NoInline
  Exec.eval_exec
  Exec.eval_exec_nf
  Exec.visit_df_node
  Regex.regex_match
  Regex.regex_search.

Extraction Inline
  string_eqb ascii_eqb ascii_ltb ascii_leb
  Qeqb Qltb Qleb
  clamp normalize_slice_bounds up_by down_by slice_positions
  nth_default
  Exec.child_on_node_impl Exec.seg_exec_impl Exec.segs_exec_impl
  Regex.nullable Regex.deriv Regex.rsimpl Regex.deriv_simpl
  Regex.list_of_string Regex.matches_from.

Separate Extraction
  JSON
  JSONPath
  Regex
  Exec
  Typing
  company_json
  acme_db_json.
