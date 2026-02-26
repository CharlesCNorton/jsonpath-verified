From Coq Require Import Init.Prelude.
From Coq Require Import
  List String Ascii ZArith Arith Lia Bool
  Sorting.Permutation QArith QArith_base.

Require Export JPV_Extensions.

Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Module API.
  Import JSON JSONPath Exec TypingPrecise JSONPath_Equiv.

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

  (* Proved precise wf gate that does not reject RFC-valid filter forms. *)
  Definition wf_selector : selector -> bool := TypingPrecise.wf_selector.
  Definition wf_segment : segment -> bool := TypingPrecise.wf_segment.
  Definition wf_query   : query -> bool := TypingPrecise.wf_query.

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

  Theorem eval_checked_exact :
    forall q J,
      eval_checked q J = Ok (eval_exec q J).
  Proof.
    intros q J.
    unfold eval_checked, wf_query.
    rewrite TypingPrecise.wf_query_total.
    reflexivity.
  Qed.

  Corollary eval_checked_never_notwf :
    forall q J,
      eval_checked q J <> Error E_NotWF.
  Proof.
    intros q J H.
    rewrite eval_checked_exact in H.
    discriminate H.
  Qed.

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

Module UnicodeAPI.
  Import Unicode UnicodeJSON UnicodeJSONPath UnicodeExec.

  Inductive exec_error :=
  | E_NotWF
  | E_NotChildOnly
  | E_NotLinear
  | E_NotFound
  | E_Multiple.

  Definition show_error (e:exec_error) : ustring :=
    string_to_ustring
      (match e with
       | E_NotWF => "not_wf"
       | E_NotChildOnly => "not_child_only"
       | E_NotLinear => "not_linear"
       | E_NotFound => "not_found"
       | E_Multiple => "multiple_results"
       end).

  Inductive result (A E:Type) :=
  | Ok (a:A)
  | Error (e:E).
  Arguments Ok   {A E} _.
  Arguments Error{A E} _.

  Fixpoint wf_fexpr (f:ufexpr) : bool :=
    match f with
    | UFTrue => true
    | UFNot g => wf_fexpr g
    | UFAnd g h | UFOr g h => andb (wf_fexpr g) (wf_fexpr h)
    | UFExists _ => true
    | UFCmp _ _ _ => true
    | UFMatch _ _ | UFSearch _ _ => true
    end.

  Definition wf_selector (sel:uselector) : bool :=
    match sel with
    | USelFilter f => wf_fexpr f
    | _ => true
    end.

  Definition wf_segment (seg:usegment) : bool :=
    match seg with
    | UChild sels | UDesc sels => forallb wf_selector sels
    end.

  Definition wf_query (q:uquery) : bool :=
    match q with UQuery segs => forallb wf_segment segs end.

  Lemma wf_fexpr_total :
    forall f, wf_fexpr f = true.
  Proof.
    induction f; simpl; try reflexivity.
    - exact IHf.
    - rewrite IHf1, IHf2. reflexivity.
    - rewrite IHf1, IHf2. reflexivity.
  Qed.

  Lemma wf_selector_total :
    forall sel, wf_selector sel = true.
  Proof.
    intros sel.
    destruct sel; simpl; try reflexivity.
    apply wf_fexpr_total.
  Qed.

  Lemma wf_segment_total :
    forall seg, wf_segment seg = true.
  Proof.
    intros [sels|sels]; simpl.
    - induction sels as [|s sels IH]; simpl; [reflexivity|].
      rewrite wf_selector_total, IH. reflexivity.
    - induction sels as [|s sels IH]; simpl; [reflexivity|].
      rewrite wf_selector_total, IH. reflexivity.
  Qed.

  Lemma wf_query_total :
    forall q, wf_query q = true.
  Proof.
    intros [segs]. simpl.
    induction segs as [|seg segs IH]; simpl; [reflexivity|].
    rewrite wf_segment_total, IH. reflexivity.
  Qed.

  Definition eval_checked (q:uquery) (J:uvalue)
    : result (list unode) exec_error :=
    if wf_query q then Ok (UnicodeExec.eval_exec q J) else Error E_NotWF.

  Theorem eval_checked_exact :
    forall q J,
      eval_checked q J = Ok (UnicodeExec.eval_exec q J).
  Proof.
    intros q J.
    unfold eval_checked.
    rewrite wf_query_total.
    reflexivity.
  Qed.

  Corollary eval_checked_never_notwf :
    forall q J,
      eval_checked q J <> Error E_NotWF.
  Proof.
    intros q J H.
    rewrite eval_checked_exact in H.
    discriminate H.
  Qed.

  Definition eval_nf_checked (q:uquery) (J:uvalue)
    : result (list unode) exec_error :=
    if UnicodeExec.query_child_only q
    then Ok (UnicodeExec.eval_exec_nf q J)
    else Error E_NotChildOnly.

  Definition eval_one_linear (q:uquery) (J:uvalue)
    : result unode exec_error :=
    if UnicodeExec.linear_query q then
      match UnicodeExec.eval_exec_nf q J with
      | [n] => Ok n
      | [] => Error E_NotFound
      | _ => Error E_Multiple
      end
    else Error E_NotLinear.

  Definition values_of (ns:list unode) : list uvalue := map snd ns.
  Definition paths_of  (ns:list unode) : list upath  := map fst ns.

  Definition eval_exec_ascii_bridge
      (q:JSONPath.query) (J:JSON.value) : list JSON.node :=
    map UnicodeJSON.to_ascii_node
        (UnicodeExec.eval_exec
           (UnicodeJSONPath.of_ascii_query q)
           (UnicodeJSON.of_ascii_value J)).

  Theorem eval_exec_ascii_bridge_empty_query :
    forall J,
      eval_exec_ascii_bridge (JSONPath.Query []) J = [([], J)].
  Proof.
    intros J. unfold eval_exec_ascii_bridge. simpl.
    assert (Hnode : UnicodeJSON.to_ascii_node ([], UnicodeJSON.of_ascii_value J) = ([], J)).
    {
      unfold UnicodeJSON.to_ascii_node. simpl.
      rewrite UnicodeJSON.to_ascii_of_ascii_value.
      reflexivity.
    }
    rewrite Hnode. reflexivity.
  Qed.
End UnicodeAPI.

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
  Regex.regex_search
  UnicodeExec.eval_exec
  UnicodeExec.eval_exec_nf
  UnicodeExec.visit_df_unode
  UnicodeRegex.regex_match
  UnicodeRegex.regex_search.

Extraction Inline
  string_eqb ascii_eqb ascii_ltb ascii_leb
  Qeqb Qltb Qleb
  clamp normalize_slice_bounds up_by down_by slice_positions
  nth_default
  Exec.child_on_node_impl Exec.seg_exec_impl Exec.segs_exec_impl
  Regex.nullable Regex.deriv Regex.rsimpl Regex.deriv_simpl
  Regex.list_of_string Regex.matches_from
  Unicode.ustring_eqb Unicode.ustring_ltb Unicode.ustring_leb
  UnicodeRegex.nullable UnicodeRegex.deriv UnicodeRegex.rsimpl UnicodeRegex.deriv_simpl
  UnicodeRegex.matches_from
  UnicodeExec.child_on_node_impl UnicodeExec.seg_exec_impl UnicodeExec.segs_exec_impl.

Separate Extraction
  JSON
  JSONPath
  Regex
  Exec
  Typing
  Unicode
  UnicodeJSON
  UnicodeJSONPath
  UnicodeRegex
  UnicodeExec
  UnicodeAPI
  company_json
  acme_db_json.
