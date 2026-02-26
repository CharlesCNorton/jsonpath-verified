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
      wf_query q = true ->
      eval_checked q J = Ok (eval_exec q J).
  Proof.
    intros q J Hwf.
    unfold eval_checked.
    rewrite Hwf.
    reflexivity.
  Qed.

  Theorem eval_checked_notwf :
    forall q J,
      wf_query q = false ->
      eval_checked q J = Error E_NotWF.
  Proof.
    intros q J Hwf.
    unfold eval_checked.
    rewrite Hwf.
    reflexivity.
  Qed.

  Theorem eval_checked_notwf_iff :
    forall q J,
      eval_checked q J = Error E_NotWF <->
      wf_query q = false.
  Proof.
    intros q J.
    unfold eval_checked, wf_query.
    destruct (TypingPrecise.wf_query q) eqn:Hwf.
    - split.
      + discriminate.
      + discriminate.
    - split.
      + intro H.
        reflexivity.
      + intro H.
        reflexivity.
  Qed.

  Corollary eval_checked_never_notwf :
    forall q J,
      wf_query q = true ->
      eval_checked q J <> Error E_NotWF.
  Proof.
    intros q J Hwf H.
    rewrite (eval_checked_exact q J Hwf) in H.
    discriminate H.
  Qed.

  (* Filter-free/child-only evaluator guard for the nf engine. *)
  Definition eval_nf_checked (q:query) (J:value)
    : result (list node) exec_error :=
    if query_child_only q
    then Ok (eval_exec_nf q J)
    else Error E_NotChildOnly.

  Theorem eval_nf_checked_notchildonly_iff :
    forall q J,
      eval_nf_checked q J = Error E_NotChildOnly <->
      query_child_only q = false.
  Proof.
    intros q J.
    unfold eval_nf_checked.
    destruct (query_child_only q) eqn:Hco.
    - split.
      + discriminate.
      + discriminate.
    - split.
      + intro H. reflexivity.
      + intro H. reflexivity.
  Qed.

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

  Theorem eval_one_linear_notlinear_iff :
    forall q J,
      eval_one_linear q J = Error E_NotLinear <->
      linear_query q = false.
  Proof.
    intros q J.
    unfold eval_one_linear.
    destruct (linear_query q) eqn:Hlin.
    - split.
      + destruct (eval_exec_nf q J) as [|n [|n2 rest]]; discriminate.
      + discriminate.
    - split.
      + intro H. reflexivity.
      + intro H. reflexivity.
  Qed.

  Theorem eval_one_linear_notfound_iff :
    forall q J,
      linear_query q = true ->
      eval_one_linear q J = Error E_NotFound <->
      eval_exec_nf q J = [].
  Proof.
    intros q J Hlin.
    unfold eval_one_linear.
    rewrite Hlin.
    destruct (eval_exec_nf q J) as [|n [|n2 rest]] eqn:Hnf.
    - split.
      + intro H. reflexivity.
      + intro H. reflexivity.
    - split; discriminate.
    - split; discriminate.
  Qed.

  Theorem eval_one_linear_multiple_iff :
    forall q J,
      linear_query q = true ->
      eval_one_linear q J = Error E_Multiple <->
      exists n1 n2 rest, eval_exec_nf q J = n1 :: n2 :: rest.
  Proof.
    intros q J Hlin.
    unfold eval_one_linear.
    rewrite Hlin.
    destruct (eval_exec_nf q J) as [|n1 [|n2 rest]] eqn:Hnf.
    - split.
      + discriminate.
      + intros [x1 [x2 [xs Hx]]]. discriminate Hx.
    - split.
      + discriminate.
      + intros [x1 [x2 [xs Hx]]]. discriminate Hx.
    - split.
      + intro H. exists n1, n2, rest. reflexivity.
      + intro H. reflexivity.
  Qed.

  Theorem eval_one_linear_ok_iff :
    forall q J n,
      linear_query q = true ->
      eval_one_linear q J = Ok n <->
      eval_exec_nf q J = [n].
  Proof.
    intros q J n Hlin.
    unfold eval_one_linear.
    rewrite Hlin.
    destruct (eval_exec_nf q J) as [|n1 [|n2 rest]] eqn:Hnf.
    - split.
      + discriminate.
      + discriminate.
    - split.
      + intro H. inversion H; subst. reflexivity.
      + intro H. inversion H; subst. reflexivity.
    - split.
      + discriminate.
      + discriminate.
  Qed.

  Theorem eval_one_linear_error_exclusive :
    forall q J e1 e2,
      eval_one_linear q J = Error e1 ->
      eval_one_linear q J = Error e2 ->
      e1 = e2.
  Proof.
    intros q J e1 e2 H1 H2.
    rewrite H1 in H2.
    inversion H2.
    reflexivity.
  Qed.

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

  Inductive primty := TNull | TBool | TNum | TStr | TAnyPrim.

  Definition aety (a:uaexpr) : primty :=
    match a with
    | UAPrim UPNull => TNull
    | UAPrim (UPBool _) => TBool
    | UAPrim (UPNum _) => TNum
    | UAPrim (UPStr _) => TStr
    | UACount _ => TNum
    | UALengthV _ => TNum
    | UAValue _ => TAnyPrim
    end.

  Definition comparable (t1 t2:primty) : bool :=
    match t1, t2 with
    | TAnyPrim, _ => true
    | _, TAnyPrim => true
    | TNull, TNull => true
    | TBool, TBool => true
    | TNum, TNum => true
    | TStr, TStr => true
    | _, _ => false
    end.

  Fixpoint wf_regex (r:uregex) : bool :=
    match r with
    | UREmpty | UREps | URAny => true
    | URChr c => codepoint_valid c
    | URAlt r1 r2 | URCat r1 r2 => andb (wf_regex r1) (wf_regex r2)
    | URStar r1 | URPlus r1 | UROpt r1 => wf_regex r1
    | URRepeat r1 min max => andb (wf_regex r1) (Nat.leb min max)
    | URCharClass _ cs => forallb codepoint_valid cs
    end.

  Fixpoint wf_aexpr (a:uaexpr) : bool
  with wf_fexpr (f:ufexpr) : bool
  with wf_selector (sel:uselector) : bool
  with wf_segment (seg:usegment) : bool
  with wf_query (q:uquery) : bool.
  Proof.
    - destruct a as [p|q|q|q].
      + exact true.
      + exact (wf_query q).
      + exact (wf_query q).
      + exact (wf_query q).
    - destruct f as [|g|g h|g h|q|op a b|a r|a r].
      + exact true.
      + exact (wf_fexpr g).
      + exact (andb (wf_fexpr g) (wf_fexpr h)).
      + exact (andb (wf_fexpr g) (wf_fexpr h)).
      + exact (wf_query q).
      + exact (andb (wf_aexpr a)
                    (andb (wf_aexpr b)
                          (comparable (aety a) (aety b)))).
      + exact (andb (wf_aexpr a)
                    (andb (wf_regex r)
                          (match aety a with
                           | TStr | TAnyPrim => true
                           | _ => false
                           end))).
      + exact (andb (wf_aexpr a)
                    (andb (wf_regex r)
                          (match aety a with
                           | TStr | TAnyPrim => true
                           | _ => false
                           end))).
    - destruct sel as [s| |i|start end_ stp|f].
      + exact true.
      + exact true.
      + exact true.
      + exact (negb (Z.eqb stp 0)).
      + exact (wf_fexpr f).
    - destruct seg as [sels|sels].
      + exact (forallb wf_selector sels).
      + exact (forallb wf_selector sels).
    - destruct q as [segs].
      exact (forallb wf_segment segs).
  Defined.

  Definition eval_checked (q:uquery) (J:uvalue)
    : result (list unode) exec_error :=
    if wf_query q then Ok (UnicodeExec.eval_exec q J) else Error E_NotWF.

  Theorem eval_checked_exact :
    forall q J,
      wf_query q = true ->
      eval_checked q J = Ok (UnicodeExec.eval_exec q J).
  Proof.
    intros q J Hwf.
    unfold eval_checked.
    rewrite Hwf.
    reflexivity.
  Qed.

  Theorem eval_checked_notwf :
    forall q J,
      wf_query q = false ->
      eval_checked q J = Error E_NotWF.
  Proof.
    intros q J Hwf.
    unfold eval_checked.
    rewrite Hwf.
    reflexivity.
  Qed.

  Theorem eval_checked_notwf_iff :
    forall q J,
      eval_checked q J = Error E_NotWF <->
      wf_query q = false.
  Proof.
    intros q J.
    unfold eval_checked.
    destruct (wf_query q) eqn:Hwf.
    - split.
      + discriminate.
      + discriminate.
    - split.
      + intro H.
        reflexivity.
      + intro H.
        reflexivity.
  Qed.

  Corollary eval_checked_never_notwf :
    forall q J,
      wf_query q = true ->
      eval_checked q J <> Error E_NotWF.
  Proof.
    intros q J Hwf H.
    rewrite (eval_checked_exact q J Hwf) in H.
    discriminate H.
  Qed.

  Definition eval_nf_checked (q:uquery) (J:uvalue)
    : result (list unode) exec_error :=
    if UnicodeExec.query_child_only q
    then Ok (UnicodeExec.eval_exec_nf q J)
    else Error E_NotChildOnly.

  Theorem eval_nf_checked_notchildonly_iff :
    forall q J,
      eval_nf_checked q J = Error E_NotChildOnly <->
      UnicodeExec.query_child_only q = false.
  Proof.
    intros q J.
    unfold eval_nf_checked.
    destruct (UnicodeExec.query_child_only q) eqn:Hco.
    - split.
      + discriminate.
      + discriminate.
    - split.
      + intro H. reflexivity.
      + intro H. reflexivity.
  Qed.

  Definition eval_one_linear (q:uquery) (J:uvalue)
    : result unode exec_error :=
    if UnicodeExec.linear_query q then
      match UnicodeExec.eval_exec_nf q J with
      | [n] => Ok n
      | [] => Error E_NotFound
      | _ => Error E_Multiple
      end
    else Error E_NotLinear.

  Theorem eval_one_linear_notlinear_iff :
    forall q J,
      eval_one_linear q J = Error E_NotLinear <->
      UnicodeExec.linear_query q = false.
  Proof.
    intros q J.
    unfold eval_one_linear.
    destruct (UnicodeExec.linear_query q) eqn:Hlin.
    - split.
      + destruct (UnicodeExec.eval_exec_nf q J) as [|n [|n2 rest]]; discriminate.
      + discriminate.
    - split.
      + intro H. reflexivity.
      + intro H. reflexivity.
  Qed.

  Theorem eval_one_linear_notfound_iff :
    forall q J,
      UnicodeExec.linear_query q = true ->
      eval_one_linear q J = Error E_NotFound <->
      UnicodeExec.eval_exec_nf q J = [].
  Proof.
    intros q J Hlin.
    unfold eval_one_linear.
    rewrite Hlin.
    destruct (UnicodeExec.eval_exec_nf q J) as [|n [|n2 rest]] eqn:Hnf.
    - split.
      + intro H. reflexivity.
      + intro H. reflexivity.
    - split; discriminate.
    - split; discriminate.
  Qed.

  Theorem eval_one_linear_multiple_iff :
    forall q J,
      UnicodeExec.linear_query q = true ->
      eval_one_linear q J = Error E_Multiple <->
      exists n1 n2 rest, UnicodeExec.eval_exec_nf q J = n1 :: n2 :: rest.
  Proof.
    intros q J Hlin.
    unfold eval_one_linear.
    rewrite Hlin.
    destruct (UnicodeExec.eval_exec_nf q J) as [|n1 [|n2 rest]] eqn:Hnf.
    - split.
      + discriminate.
      + intros [x1 [x2 [xs Hx]]]. discriminate Hx.
    - split.
      + discriminate.
      + intros [x1 [x2 [xs Hx]]]. discriminate Hx.
    - split.
      + intro H. exists n1, n2, rest. reflexivity.
      + intro H. reflexivity.
  Qed.

  Theorem eval_one_linear_ok_iff :
    forall q J n,
      UnicodeExec.linear_query q = true ->
      eval_one_linear q J = Ok n <->
      UnicodeExec.eval_exec_nf q J = [n].
  Proof.
    intros q J n Hlin.
    unfold eval_one_linear.
    rewrite Hlin.
    destruct (UnicodeExec.eval_exec_nf q J) as [|n1 [|n2 rest]] eqn:Hnf.
    - split.
      + discriminate.
      + discriminate.
    - split.
      + intro H. inversion H; subst. reflexivity.
      + intro H. inversion H; subst. reflexivity.
    - split.
      + discriminate.
      + discriminate.
  Qed.

  Theorem eval_one_linear_error_exclusive :
    forall q J e1 e2,
      eval_one_linear q J = Error e1 ->
      eval_one_linear q J = Error e2 ->
      e1 = e2.
  Proof.
    intros q J e1 e2 H1 H2.
    rewrite H1 in H2.
    inversion H2.
    reflexivity.
  Qed.

  Definition values_of (ns:list unode) : list uvalue := map snd ns.
  Definition paths_of  (ns:list unode) : list upath  := map fst ns.

  Fixpoint map_ascii_nodes_opt (ns:list unode) : option (list JSON.node) :=
    match ns with
    | [] => Some []
    | n::ns' =>
        match UnicodeJSON.to_ascii_node_opt n, map_ascii_nodes_opt ns' with
        | Some n', Some ns'' => Some (n' :: ns'')
        | _, _ => None
        end
    end.

  Definition eval_exec_ascii_bridge
      (q:JSONPath.query) (J:JSON.value) : option (list JSON.node) :=
    map_ascii_nodes_opt
      (UnicodeExec.eval_exec
         (UnicodeJSONPath.of_ascii_query q)
         (UnicodeJSON.of_ascii_value J)).

  Theorem eval_exec_ascii_bridge_empty_query :
    forall J,
      eval_exec_ascii_bridge (JSONPath.Query []) J = Some [([], J)].
  Proof.
    intros J. unfold eval_exec_ascii_bridge. simpl.
    assert (Hnode : UnicodeJSON.to_ascii_node_opt ([], UnicodeJSON.of_ascii_value J) = Some ([], J)).
    {
      unfold UnicodeJSON.to_ascii_node_opt. simpl.
      rewrite UnicodeJSON.to_ascii_value_opt_of_ascii.
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
Set Extraction Output Directory ".".

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
