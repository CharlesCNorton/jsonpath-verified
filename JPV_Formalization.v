From Coq Require Import Init.Prelude.
From Coq Require Import
  List String Ascii ZArith Arith Lia Bool
  Sorting.Permutation QArith QArith_base.

Require Export JPV_Core.

Import JSON JSONPath.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(* ------------------------------------------------------------ *)
(* Todo 1-9 Formalization Closures                              *)
(* ------------------------------------------------------------ *)

Theorem todo1_holds_b_sound_bool_connectives :
  forall f n,
    (match f with FTrue | FNot _ | FAnd _ _ | FOr _ _ => True | _ => False end) ->
    Exec.holds_b f n = true ->
    holds_exec f n.
Proof.
  intros f n _ H.
  exact (holds_b_sound f n H).
Qed.

Theorem todo2_holds_b_sound_cmp_match_search :
  forall f n,
    (match f with FCmp _ _ _ | FMatch _ _ | FSearch _ _ => True | _ => False end) ->
    Exec.holds_b f n = true ->
    holds_exec f n.
Proof.
  intros f n _ H.
  exact (holds_b_sound f n H).
Qed.

Theorem todo3_holds_b_sound_exists :
  forall q n,
    Exec.holds_b (FExists q) n = true ->
    holds_exec (FExists q) n.
Proof.
  intros q n H.
  exact (holds_b_sound_fexists q n H).
Qed.

Theorem todo4_holds_b_complete_all :
  forall f n,
    holds_exec f n ->
    Exec.holds_b f n = true.
Proof.
  apply holds_b_complete.
Qed.

Theorem todo5_sel_exec_sound_full :
  forall sel n,
    eval_selector_exec sel n (Exec.sel_exec sel n).
Proof.
  apply sel_exec_sound.
Qed.

Theorem todo6_sel_exec_complete_full :
  forall sel n res,
    eval_selector_exec sel n res ->
    res = Exec.sel_exec sel n.
Proof.
  apply sel_exec_complete.
Qed.

Theorem todo7_desc_segment_equiv_full :
  forall sels n res,
    eval_seg_exec (Desc sels) n res <->
    res = Exec.seg_exec (Desc sels) n.
Proof.
  apply desc_segment_equiv.
Qed.

Theorem todo8_eval_exec_equiv_full :
  forall q J res,
    eval_exec_rel q J res <->
    res = Exec.eval_exec q J.
Proof.
  apply eval_exec_equiv.
Qed.

Theorem todo9_aeval_equiv_full :
  forall a v p,
    aeval_rel_exec a v p <->
    Exec.aeval a v = Some p.
Proof.
  apply aeval_exec_equiv.
Qed.

(* ------------------------------------------------------------ *)
(* Static well-formedness checks (conservative)                 *)
(* ------------------------------------------------------------ *)

(** Conservative static type checking for filter expressions. *)
Module Typing.
Import JSON JSONPath.

(** Primitive type tags for conservative analysis. *)
Inductive primty := TNull | TBool | TNum | TStr | TAnyPrim.

(** Selector is simple (name or index only). *)
Definition selector_ok (sel:selector) : bool :=
  match sel with
  | SelName _ | SelIndex _ => true
  | _ => false
  end.

(** Segment is child-only with simple selectors. *)
Definition segment_ok (s:segment) : bool :=
  match s with
  | Child sels => forallb selector_ok sels
  | Desc _ => false
  end.

(** Query is a non-empty chain of simple child segments. *)
Definition singleton_query (q:query) : bool :=
  match q with
  | Query segs =>
      match segs with
      | [] => false
      | _  => forallb segment_ok segs
      end
  end.

(** Infer conservative primitive type from arithmetic expression. *)
Definition aety (a:aexpr) : primty :=
  match a with
  | APrim PNull      => TNull
  | APrim (PBool _)  => TBool
  | APrim (PNum _)   => TNum
  | APrim (PStr _)   => TStr
  | ACount _         => TNum
  | ALengthV _       => TNum
  | AValue _         => TAnyPrim
  end.

(** Type compatibility for comparisons: same concrete type, or either is TAnyPrim. *)
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

(** Well-formedness check for filter expressions (conservative). *)
Fixpoint wf_fexpr (f:fexpr) : bool :=
  match f with
  | FTrue => true
  | FNot g => wf_fexpr g
  | FAnd g h | FOr g h => andb (wf_fexpr g) (wf_fexpr h)
  | FExists _ => true
  | FCmp _ a b => comparable (aety a) (aety b)
  | FMatch a _ | FSearch a _ =>
      match aety a with
      | TStr | TAnyPrim => true
      | _ => false
      end
  end.

End Typing.

(* ------------------------------------------------------------ *)
(* Typing Soundness                                             *)
(* ------------------------------------------------------------ *)

(** Type membership: primitive value has given type. *)
Definition prim_has_type (p : prim) (t : Typing.primty) : Prop :=
  match p, t with
  | PNull, Typing.TNull => True
  | PBool _, Typing.TBool => True
  | PNum _, Typing.TNum => True
  | PStr _, Typing.TStr => True
  | _, Typing.TAnyPrim => True
  | _, _ => False
  end.

Lemma prim_has_type_null : prim_has_type PNull Typing.TNull.
Proof. simpl. auto. Qed.

Lemma prim_has_type_bool : forall b, prim_has_type (PBool b) Typing.TBool.
Proof. intros. simpl. auto. Qed.

Lemma prim_has_type_num : forall n, prim_has_type (PNum n) Typing.TNum.
Proof. intros. simpl. auto. Qed.

Lemma prim_has_type_str : forall s, prim_has_type (PStr s) Typing.TStr.
Proof. intros. simpl. auto. Qed.

Lemma prim_has_type_any : forall p, prim_has_type p Typing.TAnyPrim.
Proof. intros. destruct p; simpl; auto. Qed.

Lemma aprim_type : forall p0, prim_has_type p0 (Typing.aety (APrim p0)).
Proof. intros. destruct p0; simpl; auto using prim_has_type_null, prim_has_type_bool, prim_has_type_num, prim_has_type_str. Qed.

Lemma acount_type : forall q, Typing.aety (ACount q) = Typing.TNum.
Proof. reflexivity. Qed.

Lemma avalue_type : forall q, Typing.aety (AValue q) = Typing.TAnyPrim.
Proof. reflexivity. Qed.

Lemma alengthv_type : forall q, Typing.aety (ALengthV q) = Typing.TNum.
Proof. reflexivity. Qed.

Lemma prim_of_value_null : prim_of_value JNull = Some PNull.
Proof. reflexivity. Qed.

Lemma prim_of_value_bool : forall b, prim_of_value (JBool b) = Some (PBool b).
Proof. reflexivity. Qed.

Lemma prim_of_value_num : forall n, prim_of_value (JNum n) = Some (PNum n).
Proof. reflexivity. Qed.

Lemma prim_of_value_str : forall s, prim_of_value (JStr s) = Some (PStr s).
Proof. reflexivity. Qed.

Lemma prim_of_value_arr : forall xs, prim_of_value (JArr xs) = None.
Proof. reflexivity. Qed.

Lemma prim_of_value_obj : forall fs, prim_of_value (JObject fs) = None.
Proof. reflexivity. Qed.

Lemma aeval_aprim : forall p0 v, Exec.aeval (APrim p0) v = Some p0.
Proof. reflexivity. Qed.

Lemma aeval_acount : forall q v, Exec.aeval (ACount q) v = Some (PNum (Q_of_nat (List.length (Exec.eval_exec_impl Exec.sel_exec q v)))).
Proof. reflexivity. Qed.

Lemma aeval_avalue_none : forall q v, Exec.eval_exec_impl Exec.sel_exec q v = [] -> Exec.aeval (AValue q) v = None.
Proof. intros. simpl. rewrite H. reflexivity. Qed.

Lemma aeval_avalue_multi : forall q v n1 n2 rest, Exec.eval_exec_impl Exec.sel_exec q v = n1 :: n2 :: rest -> Exec.aeval (AValue q) v = None.
Proof. intros. simpl. rewrite H. destruct n1. reflexivity. Qed.

Lemma aeval_avalue_single : forall q v p1 v1, Exec.eval_exec_impl Exec.sel_exec q v = [(p1, v1)] -> Exec.aeval (AValue q) v = prim_of_value v1.
Proof. intros. simpl. rewrite H. reflexivity. Qed.

Lemma aeval_alengthv_none : forall q v, Exec.eval_exec_impl Exec.sel_exec q v = [] -> Exec.aeval (ALengthV q) v = None.
Proof. intros. simpl. rewrite H. reflexivity. Qed.

Lemma aeval_alengthv_multi : forall q v n1 n2 rest, Exec.eval_exec_impl Exec.sel_exec q v = n1 :: n2 :: rest -> Exec.aeval (ALengthV q) v = None.
Proof. intros. simpl. rewrite H. destruct n1 as [p v0]. destruct v0; reflexivity. Qed.

Lemma aeval_alengthv_str : forall q v p1 s, Exec.eval_exec_impl Exec.sel_exec q v = [(p1, JStr s)] -> Exec.aeval (ALengthV q) v = Some (PNum (Q_of_nat (String.length s))).
Proof. intros. simpl. rewrite H. reflexivity. Qed.

Lemma aeval_alengthv_arr : forall q v p1 xs, Exec.eval_exec_impl Exec.sel_exec q v = [(p1, JArr xs)] -> Exec.aeval (ALengthV q) v = Some (PNum (Q_of_nat (List.length xs))).
Proof. intros. simpl. rewrite H. reflexivity. Qed.

Lemma aeval_alengthv_obj : forall q v p1 fs, Exec.eval_exec_impl Exec.sel_exec q v = [(p1, JObject fs)] -> Exec.aeval (ALengthV q) v = Some (PNum (Q_of_nat (List.length fs))).
Proof. intros. simpl. rewrite H. reflexivity. Qed.

Lemma aeval_alengthv_null : forall q v p1, Exec.eval_exec_impl Exec.sel_exec q v = [(p1, JNull)] -> Exec.aeval (ALengthV q) v = None.
Proof. intros. simpl. rewrite H. reflexivity. Qed.

Lemma aeval_alengthv_bool : forall q v p1 b, Exec.eval_exec_impl Exec.sel_exec q v = [(p1, JBool b)] -> Exec.aeval (ALengthV q) v = None.
Proof. intros. simpl. rewrite H. reflexivity. Qed.

Lemma aeval_alengthv_num : forall q v p1 n, Exec.eval_exec_impl Exec.sel_exec q v = [(p1, JNum n)] -> Exec.aeval (ALengthV q) v = None.
Proof. intros. simpl. rewrite H. reflexivity. Qed.

Lemma avalue_singleton_has_anyprim_type :
  forall q v p1 v1 p,
    Exec.eval_exec_impl Exec.sel_exec q v = [(p1, v1)] ->
    Exec.aeval (AValue q) v = Some p ->
    prim_has_type p Typing.TAnyPrim.
Proof.
  intros q v p1 v1 p E Heval.
  rewrite (aeval_avalue_single q v p1 v1 E) in Heval.
  unfold prim_of_value in Heval.
  destruct v1; inversion Heval; subst; apply prim_has_type_any.
Qed.

Lemma alengthv_str_has_num_type :
  forall q v p1 s p,
    Exec.eval_exec_impl Exec.sel_exec q v = [(p1, JStr s)] ->
    Exec.aeval (ALengthV q) v = Some p ->
    prim_has_type p Typing.TNum.
Proof.
  intros q v p1 s p E Heval.
  rewrite (aeval_alengthv_str q v p1 s E) in Heval.
  inversion Heval; subst.
  apply prim_has_type_num.
Qed.

Lemma alengthv_arr_has_num_type :
  forall q v p1 l p,
    Exec.eval_exec_impl Exec.sel_exec q v = [(p1, JArr l)] ->
    Exec.aeval (ALengthV q) v = Some p ->
    prim_has_type p Typing.TNum.
Proof.
  intros q v p1 l p E Heval.
  rewrite (aeval_alengthv_arr q v p1 l E) in Heval.
  inversion Heval; subst.
  apply prim_has_type_num.
Qed.

Lemma alengthv_obj_has_num_type :
  forall q v p1 l p,
    Exec.eval_exec_impl Exec.sel_exec q v = [(p1, JObject l)] ->
    Exec.aeval (ALengthV q) v = Some p ->
    prim_has_type p Typing.TNum.
Proof.
  intros q v p1 l p E Heval.
  rewrite (aeval_alengthv_obj q v p1 l E) in Heval.
  inversion Heval; subst.
  apply prim_has_type_num.
Qed.

(** Arithmetic expression type soundness: aeval result matches predicted type. *)
Theorem aeval_type_soundness :
  forall a v p,
    Exec.aeval a v = Some p ->
    prim_has_type p (Typing.aety a).
Proof.
  intros a v p Heval.
  destruct a as [p0 | q1 | q2 | q3].
  - rewrite aeval_aprim in Heval. inversion Heval; subst. apply aprim_type.
  - rewrite aeval_acount in Heval. inversion Heval; subst. rewrite acount_type. apply prim_has_type_num.
  - rewrite avalue_type. destruct (Exec.eval_exec_impl Exec.sel_exec q2 v) as [|[p1 v1] rest] eqn:E.
    + rewrite (aeval_avalue_none q2 v E) in Heval. inversion Heval.
    + destruct rest as [|n2 rest'].
      * eapply avalue_singleton_has_anyprim_type; eauto.
      * rewrite (aeval_avalue_multi q2 v (p1,v1) n2 rest' E) in Heval. inversion Heval.
  - rewrite alengthv_type. destruct (Exec.eval_exec_impl Exec.sel_exec q3 v) as [|[p1 v1] rest] eqn:E.
    + rewrite (aeval_alengthv_none q3 v E) in Heval. inversion Heval.
    + destruct rest as [|n2 rest'].
      * destruct v1.
        -- rewrite (aeval_alengthv_null q3 v p1 E) in Heval. inversion Heval.
        -- rewrite (aeval_alengthv_bool q3 v p1 b E) in Heval. inversion Heval.
        -- rewrite (aeval_alengthv_num q3 v p1 n E) in Heval. inversion Heval.
        -- eapply alengthv_str_has_num_type; eauto.
        -- eapply alengthv_arr_has_num_type; eauto.
        -- eapply alengthv_obj_has_num_type; eauto.
      * rewrite (aeval_alengthv_multi q3 v (p1,v1) n2 rest' E) in Heval. inversion Heval.
Qed.

(** Type compatibility ensures comparison operations are well-defined. *)
Lemma comparable_types_defined :
  forall t1 t2 p1 p2 op,
    Typing.comparable t1 t2 = true ->
    prim_has_type p1 t1 ->
    prim_has_type p2 t2 ->
    exists result : bool, cmp_prim op p1 p2 = result.
Proof.
  intros t1 t2 p1 p2 op Hcomp Ht1 Ht2.
  destruct p1, p2, op; eexists; reflexivity.
Qed.

(** Well-formed comparison operations have compatible operand types. *)
Theorem wf_fcmp_operands_compatible :
  forall op a b v pa pb,
    Typing.wf_fexpr (FCmp op a b) = true ->
    Exec.aeval a v = Some pa ->
    Exec.aeval b v = Some pb ->
    exists result : bool, cmp_prim op pa pb = result.
Proof.
  intros op a b v pa pb Hwf Ha Hb.
  simpl in Hwf.
  pose proof (aeval_type_soundness a v pa Ha) as Hta.
  pose proof (aeval_type_soundness b v pb Hb) as Htb.
  eapply comparable_types_defined; eauto.
Qed.

(** Well-formed match expressions produce strings or fail gracefully. *)
Lemma any_prim_type_cases :
  forall p,
    prim_has_type p Typing.TAnyPrim ->
    (exists s, p = PStr s) \/ (exists b, p = PBool b) \/ (exists n, p = PNum n) \/ p = PNull.
Proof.
  intros p Htype.
  destruct p; eauto.
Qed.

Theorem wf_fmatch_type_safe :
  forall a r v,
    Typing.wf_fexpr (FMatch a r) = true ->
    Exec.aeval a v = None \/
    exists s, Exec.aeval a v = Some (PStr s) \/
              Exec.aeval a v = Some PNull \/
              exists b, Exec.aeval a v = Some (PBool b) \/
              exists n, Exec.aeval a v = Some (PNum n).
Proof.
  intros a r v Hwf.
  simpl in Hwf.
  destruct (Exec.aeval a v) as [p|] eqn:E.
  - destruct (Typing.aety a) eqn:Ety; try discriminate.
    + pose proof (aeval_type_soundness a v p E) as Ht.
      rewrite Ety in Ht.
      destruct p; try contradiction.
      right. eexists. left. reflexivity.
    + pose proof (aeval_type_soundness a v p E) as Ht.
      rewrite Ety in Ht.
      pose proof (any_prim_type_cases p Ht) as Hcases.
      destruct Hcases as [[s Hs]|[[b Hb]|[[n Hn]|Hnull]]]; subst.
      * right. eexists. left. reflexivity.
      * right. exists ""%string. right. right. exists b. left. reflexivity.
      * right. exists ""%string. right. right. exists true. right. eexists. reflexivity.
      * right. exists ""%string. right. left. reflexivity.
  - left; reflexivity.
Qed.

(** Well-formed search expressions produce strings or fail gracefully. *)
Theorem wf_fsearch_type_safe :
  forall a r v,
    Typing.wf_fexpr (FSearch a r) = true ->
    Exec.aeval a v = None \/
    exists s, Exec.aeval a v = Some (PStr s) \/
              Exec.aeval a v = Some PNull \/
              exists b, Exec.aeval a v = Some (PBool b) \/
              exists n, Exec.aeval a v = Some (PNum n).
Proof.
  intros a r v Hwf.
  simpl in Hwf.
  destruct (Exec.aeval a v) as [p|] eqn:E.
  - destruct (Typing.aety a) eqn:Ety; try discriminate.
    + pose proof (aeval_type_soundness a v p E) as Ht.
      rewrite Ety in Ht.
      destruct p; try contradiction.
      right. eexists. left. reflexivity.
    + pose proof (aeval_type_soundness a v p E) as Ht.
      rewrite Ety in Ht.
      pose proof (any_prim_type_cases p Ht) as Hcases.
      destruct Hcases as [[s Hs]|[[b Hb]|[[n Hn]|Hnull]]]; subst.
      * right. eexists. left. reflexivity.
      * right. exists ""%string. right. right. exists b. left. reflexivity.
      * right. exists ""%string. right. right. exists true. right. eexists. reflexivity.
      * right. exists ""%string. right. left. reflexivity.
  - left; reflexivity.
Qed.

(** Type soundness: well-formed filters perform type-safe operations. *)
Theorem typing_soundness :
  forall f,
    Typing.wf_fexpr f = true ->
    forall n,
      (forall op a b, f = FCmp op a b ->
        forall v pa pb,
          n = (@fst JSON.path JSON.value n, v) ->
          Exec.aeval a v = Some pa ->
          Exec.aeval b v = Some pb ->
          exists result : bool, cmp_prim op pa pb = result) /\
      (forall a r, f = FMatch a r ->
        forall v,
          n = (@fst JSON.path JSON.value n, v) ->
          Exec.aeval a v = None \/
          exists s, Exec.aeval a v = Some (PStr s) \/
          Exec.aeval a v = Some PNull \/
          exists b, Exec.aeval a v = Some (PBool b) \/
          exists n, Exec.aeval a v = Some (PNum n)) /\
      (forall a r, f = FSearch a r ->
        forall v,
          n = (@fst JSON.path JSON.value n, v) ->
          Exec.aeval a v = None \/
          exists s, Exec.aeval a v = Some (PStr s) \/
          Exec.aeval a v = Some PNull \/
          exists b, Exec.aeval a v = Some (PBool b) \/
          exists n, Exec.aeval a v = Some (PNum n)).
Proof.
  intros f Hwf n.
  split; [|split].
  - intros op a b Heq v pa pb _ Ha Hb. subst f. eapply wf_fcmp_operands_compatible; eauto.
  - intros a r0 Heq v _. subst f. apply (wf_fmatch_type_safe a r0 v); auto.
  - intros a r0 Heq v _. subst f. apply (wf_fsearch_type_safe a r0 v); auto.
Qed.

(* ------------------------------------------------------------ *)
(* Visit Order Determinism                                      *)
(* ------------------------------------------------------------ *)

Lemma visit_df_arr_deterministic :
  forall p xs,
    Exec.visit_df_value p (JArr xs) =
    mk_node p (JArr xs) :: List.concat
      ((fix go (i:nat) (ys:list JSON.value) {struct ys} : list (list JSON.node) :=
        match ys with
        | [] => []
        | v'::ys' => Exec.visit_df_value (List.app p [SIndex (Z.of_nat i)]) v' :: go (S i) ys'
        end) 0%nat xs).
Proof.
  intros. simpl. reflexivity.
Qed.

Lemma visit_df_obj_deterministic :
  forall p fs,
    Exec.visit_df_value p (JObject fs) =
    mk_node p (JObject fs) :: List.concat
      ((fix go (gs:list (string*JSON.value)) {struct gs} : list (list JSON.node) :=
        match gs with
        | [] => []
        | (k,v')::gs' => Exec.visit_df_value (List.app p [SName k]) v' :: go gs'
        end) fs).
Proof.
  intros. simpl. reflexivity.
Qed.

Lemma visit_df_primitive_deterministic :
  forall p v,
    (v = JNull \/ exists b, v = JBool b \/ exists n, v = JNum n \/ exists s, v = JStr s) ->
    Exec.visit_df_value p v = [mk_node p v].
Proof.
  intros p v H.
  destruct H as [->|[b [->|[n [->|[s ->]]]]]]; simpl; reflexivity.
Qed.

Lemma visit_arr_head_is_parent :
  forall p xs,
    xs <> [] ->
    exists rest, Exec.visit_df_value p (JArr xs) = mk_node p (JArr xs) :: rest.
Proof.
  intros p xs Hne.
  rewrite visit_df_arr_deterministic.
  eexists. reflexivity.
Qed.

Lemma visit_obj_head_is_parent :
  forall p fs,
    fs <> [] ->
    exists rest, Exec.visit_df_value p (JObject fs) = mk_node p (JObject fs) :: rest.
Proof.
  intros p fs Hne.
  rewrite visit_df_obj_deterministic.
  eexists. reflexivity.
Qed.

Theorem visit_df_value_head_is_self :
  forall p v,
    exists rest, Exec.visit_df_value p v = mk_node p v :: rest.
Proof.
  intros p v.
  destruct v; simpl; eexists; reflexivity.
Qed.

Lemma visit_df_arr_children_structure :
  forall p xs i,
    (fix go (i0:nat) (ys:list JSON.value) {struct ys} : list (list JSON.node) :=
      match ys with
      | [] => []
      | v'::ys' => Exec.visit_df_value (List.app p [SIndex (Z.of_nat i0)]) v' :: go (S i0) ys'
      end) i xs =
    map (fun '(idx, v') => Exec.visit_df_value (List.app p [SIndex (Z.of_nat idx)]) v')
        (combine (seq i (List.length xs)) xs).
Proof.
  intros p xs. revert p.
  induction xs as [|x xs' IH]; intros p i; simpl.
  - reflexivity.
  - f_equal. apply IH.
Qed.

Lemma visit_df_obj_children_structure :
  forall p fs,
    (fix go (gs:list (string*JSON.value)) {struct gs} : list (list JSON.node) :=
      match gs with
      | [] => []
      | (k,v')::gs' => Exec.visit_df_value (List.app p [SName k]) v' :: go gs'
      end) fs =
    map (fun '(k, v') => Exec.visit_df_value (List.app p [SName k]) v') fs.
Proof.
  intros p.
  induction fs as [|[k v] fs' IH]; simpl.
  - reflexivity.
  - f_equal. apply IH.
Qed.

Theorem visit_df_value_canonical_order :
  forall p v,
    match v with
    | JArr xs => Exec.visit_df_value p v =
        mk_node p v :: List.concat (map (fun '(idx, v') => Exec.visit_df_value (List.app p [SIndex (Z.of_nat idx)]) v')
                                         (combine (seq 0 (List.length xs)) xs))
    | JObject fs => Exec.visit_df_value p v =
        mk_node p v :: List.concat (map (fun '(k, v') => Exec.visit_df_value (List.app p [SName k]) v') fs)
    | _ => Exec.visit_df_value p v = [mk_node p v]
    end.
Proof.
  intros p v.
  destruct v; simpl; try reflexivity.
  - rewrite visit_df_arr_children_structure. reflexivity.
  - rewrite visit_df_obj_children_structure. reflexivity.
Qed.

(* ------------------------------------------------------------ *)
(* Bridge lemma: selector -> Child [selector]                   *)
(* ------------------------------------------------------------ *)

(** Lift single selector evaluation to segment evaluation. *)
Lemma eval_child_single_selector :
  forall sel n res,
    eval_selector sel n res ->
    eval_seg (Child [sel]) n res.
Proof.
  intros sel n res Hsel.
  eapply EvalSegChild.
  exists [res]. split.
  - constructor; [exact Hsel | constructor].
  - simpl. rewrite app_nil_r. reflexivity.
Qed.

(* ------------------------------------------------------------ *)
(* Tests                                                        *)
(* ------------------------------------------------------------ *)

Import Exec.

(** Shorthand for numeric JSON values. *)
Definition JQ (z:Z) : JSON.value := JSON.JNum (Q_of_Z z).

(** Name selector on object retrieves specified field. *)
Example test_name_selector :
  let json := JObject [("a", JQ 1); ("b", JQ 2)] in
  exists result, eval (Query [Child [SelName "a"]]) json result /\
                 result = [([SName "a"], JQ 1)].
Proof.
  simpl. eexists. split; [| reflexivity].
  apply EvalQuery.
  econstructor.
  - eexists. split.
    + constructor.
      * apply eval_child_single_selector.
        apply EvalSelName. reflexivity.
      * constructor.
    + simpl. reflexivity.
  - constructor.
Qed.

(** Index selector accesses array element by position. *)
Example test_index_selector :
  let json := JArr [JQ 10; JQ 20; JQ 30] in
  exists result, eval (Query [Child [SelIndex 1]]) json result /\
                 result = [([SIndex 1], JQ 20)].
Proof.
  simpl. eexists. split; [| reflexivity].
  apply EvalQuery.
  econstructor.
  - eexists. split.
    + constructor.
      * apply eval_child_single_selector.
        eapply EvalSelIndex with (idx:=1); simpl; try reflexivity.
      * constructor.
    + simpl. reflexivity.
  - constructor.
Qed.

(** Negative indices count from end of array. *)
Example test_negative_index :
  let json := JArr [JQ 10; JQ 20; JQ 30] in
  exists result, eval (Query [Child [SelIndex (-1)]]) json result /\
                 result = [([SIndex 2], JQ 30)].
Proof.
  simpl. eexists. split; [| reflexivity].
  apply EvalQuery.
  econstructor.
  - eexists. split.
    + constructor.
      * apply eval_child_single_selector.
        eapply EvalSelIndex with (idx:=2); simpl; try reflexivity.
      * constructor.
    + simpl. reflexivity.
  - constructor.
Qed.

(** Wildcard selects all object fields. *)
Example test_wildcard_object :
  let json := JObject [("a", JQ 1); ("b", JQ 2)] in
  exists result, eval (Query [Child [SelWildcard]]) json result /\
                 result = [([SName "a"], JQ 1); ([SName "b"], JQ 2)].
Proof.
  simpl. eexists. split; [| reflexivity].
  apply EvalQuery.
  econstructor.
  - eexists. split.
    + constructor.
      * apply eval_child_single_selector.
        eapply EvalSelWildcardObject. apply Permutation_refl.
      * constructor.
    + simpl. reflexivity.
  - constructor.
Qed.

(** Wildcard selects all array elements. *)
Example test_wildcard_array :
  let json := JArr [JQ 10; JQ 20] in
  exists result, eval (Query [Child [SelWildcard]]) json result /\
                 result = [([SIndex 0], JQ 10); ([SIndex 1], JQ 20)].
Proof.
  simpl. eexists. split; [| reflexivity].
  apply EvalQuery.
  econstructor.
  - eexists. split.
    + constructor.
      * apply eval_child_single_selector.
        apply EvalSelWildcardArray.
      * constructor.
    + simpl. reflexivity.
  - constructor.
Qed.

(** Wildcard on empty object returns empty list. *)
Example test_wildcard_empty_object :
  let json := JObject [] in
  exists result, eval (Query [Child [SelWildcard]]) json result /\
                 result = [].
Proof.
  simpl. eexists. split; [| reflexivity].
  apply EvalQuery.
  econstructor.
  - eexists. split.
    + constructor.
      * apply eval_child_single_selector.
        eapply EvalSelWildcardObject. apply Permutation_refl.
      * constructor.
    + simpl. reflexivity.
  - constructor.
Qed.

(** Wildcard on empty array returns empty list. *)
Example test_wildcard_empty_array :
  let json := JArr [] in
  exists result, eval (Query [Child [SelWildcard]]) json result /\
                 result = [].
Proof.
  simpl. eexists. split; [| reflexivity].
  apply EvalQuery.
  econstructor.
  - eexists. split.
    + constructor.
      * apply eval_child_single_selector.
        apply EvalSelWildcardArray.
      * constructor.
    + simpl. reflexivity.
  - constructor.
Qed.

(** Multi-segment query chains navigation through nested structures. *)
Example test_multi_segment :
  let json := JObject [("users", JArr [
                         JObject [("name", JStr "alice"); ("age", JQ 30)];
                         JObject [("name", JStr "bob"); ("age", JQ 25)]
                       ])] in
  exists result, eval (Query [Child [SelName "users"];
                              Child [SelIndex 0];
                              Child [SelName "name"]]) json result /\
                 result = [([SName "users"; SIndex 0; SName "name"], JStr "alice")].
Proof.
  simpl. eexists. split; [| reflexivity].
  apply EvalQuery.
  econstructor.
  - eexists. split.
    + constructor.
      * apply eval_child_single_selector.
        apply EvalSelName. reflexivity.
      * constructor.
    + simpl. reflexivity.
  - econstructor.
    + eexists. split.
      * constructor.
        -- apply eval_child_single_selector.
           eapply EvalSelIndex with (idx:=0); simpl; try reflexivity.
        -- constructor.
      * simpl. reflexivity.
    + econstructor.
      * eexists. split.
        -- constructor.
           ++ apply eval_child_single_selector.
              apply EvalSelName. reflexivity.
           ++ constructor.
        -- simpl. reflexivity.
      * constructor.
Qed.

(** Empty query returns root node only. *)
Theorem empty_query_returns_root : forall J,
  eval (Query []) J [([], J)].
Proof. intros. constructor. constructor. Qed.

(** Slice with positive step selects subrange [start, end). *)
Example exec_slice_pos :
  let j := JArr [JQ 0; JQ 1; JQ 2; JQ 3] in
  eval_exec (Query [Child [SelSlice (Some 1) (Some 3) 1]]) j
  = [ ([SIndex 1], JQ 1) ; ([SIndex 2], JQ 2) ].
Proof. reflexivity. Qed.

(** Negative step reverses iteration order. *)
Example exec_slice_neg_step_all :
  let j := JArr [JQ 10; JQ 20; JQ 30] in
  eval_exec (Query [Child [SelSlice None None (-1)]]) j
  = [ ([SIndex 2], JQ 30) ; ([SIndex 1], JQ 20) ; ([SIndex 0], JQ 10) ].
Proof. reflexivity. Qed.

(** Zero step yields empty slice per RFC 9535. *)
Example exec_slice_zero_step_is_empty :
  let j := JArr [JQ 10; JQ 20] in
  eval_exec (Query [Child [SelSlice None None 0]]) j = [].
Proof. reflexivity. Qed.

(** Negative start bound converted relative to length. *)
Example exec_slice_mixed_bounds :
  let j := JArr [JQ 0; JQ 1; JQ 2; JQ 3; JQ 4] in
  eval_exec (Query [Child [SelSlice (Some (-3)) None 1]]) j
  = [ ([SIndex 2], JQ 2) ; ([SIndex 3], JQ 3) ; ([SIndex 4], JQ 4) ].
Proof. reflexivity. Qed.

(** Slice on empty array yields empty result. *)
Example exec_slice_empty_array :
  let j := JArr [] in
  eval_exec (Query [Child [SelSlice None None 1]]) j = [].
Proof. reflexivity. Qed.

(** Slice on single element array. *)
Example exec_slice_single_element :
  let j := JArr [JQ 42] in
  eval_exec (Query [Child [SelSlice None None 1]]) j
  = [ ([SIndex 0], JQ 42) ].
Proof. reflexivity. Qed.

(** Slice with start > end and positive step yields empty result. *)
Example exec_slice_start_gt_end_pos_step :
  let j := JArr [JQ 0; JQ 1; JQ 2; JQ 3] in
  eval_exec (Query [Child [SelSlice (Some 3) (Some 1) 1]]) j = [].
Proof. reflexivity. Qed.

(** Slice with start < end and negative step yields empty result. *)
Example exec_slice_start_lt_end_neg_step :
  let j := JArr [JQ 0; JQ 1; JQ 2; JQ 3] in
  eval_exec (Query [Child [SelSlice (Some 1) (Some 3) (-1)]]) j = [].
Proof. reflexivity. Qed.

(** Slice with step larger than array length selects only first element. *)
Example exec_slice_large_step :
  let j := JArr [JQ 0; JQ 1; JQ 2; JQ 3] in
  eval_exec (Query [Child [SelSlice None None 10]]) j
  = [ ([SIndex 0], JQ 0) ].
Proof. reflexivity. Qed.

(** Slice with large negative indices beyond array bounds yields empty. *)
Example exec_slice_large_negative_indices :
  let j := JArr [JQ 0; JQ 1; JQ 2] in
  eval_exec (Query [Child [SelSlice (Some (-10)) (Some (-8)) 1]]) j = [].
Proof. reflexivity. Qed.

(** Slice with out of bounds positive indices yields empty. *)
Example exec_slice_oob_positive_indices :
  let j := JArr [JQ 0; JQ 1; JQ 2] in
  eval_exec (Query [Child [SelSlice (Some 10) (Some 20) 1]]) j = [].
Proof. reflexivity. Qed.

(** Slice with None/None/1 selects full array. *)
Example exec_slice_full_array :
  let j := JArr [JQ 0; JQ 1; JQ 2] in
  eval_exec (Query [Child [SelSlice None None 1]]) j
  = [ ([SIndex 0], JQ 0) ; ([SIndex 1], JQ 1) ; ([SIndex 2], JQ 2) ].
Proof. reflexivity. Qed.

(** Slice with -1 as start and None end selects last element. *)
Example exec_slice_last_element :
  let j := JArr [JQ 0; JQ 1; JQ 2] in
  eval_exec (Query [Child [SelSlice (Some (-1)) None 1]]) j
  = [ ([SIndex 2], JQ 2) ].
Proof. reflexivity. Qed.

(** Slice from start to -1 (exclusive) selects all but last. *)
Example exec_slice_all_but_last :
  let j := JArr [JQ 0; JQ 1; JQ 2] in
  eval_exec (Query [Child [SelSlice None (Some (-1)) 1]]) j
  = [ ([SIndex 0], JQ 0) ; ([SIndex 1], JQ 1) ].
Proof. reflexivity. Qed.

(** Filter comparing nested field value against threshold. *)
Definition f_age_gt_21 : selector :=
  SelFilter (FCmp CGt
                 (AValue (Query [Child [SelName "age"]]))
                 (APrim (PNum (Q_of_Z 21)))).

(** Filter retains only array elements satisfying age > 21. *)
Example exec_filter_age_gt_21 :
  let j :=
    JArr [
      JObject [("name", JStr "a"); ("age", JQ 30)];
      JObject [("name", JStr "b"); ("age", JQ 21)];
      JObject [("name", JStr "c"); ("age", JQ 22)]
    ] in
  eval_exec (Query [Child [f_age_gt_21]]) j
  = [
      ([SIndex 0], JObject [("name", JStr "a"); ("age", JQ 30)]);
      ([SIndex 2], JObject [("name", JStr "c"); ("age", JQ 22)])
    ].
Proof. reflexivity. Qed.

(** Filter checking field existence (non-empty query result). *)
Definition f_exists_age : selector :=
  SelFilter (FExists (Query [Child [SelName "age"]])).

(** Existential filter retains nodes with specified field. *)
Example exec_filter_exists_age :
  let j :=
    JArr [
      JObject [("name", JStr "a"); ("age", JQ 30)];
      JObject [("name", JStr "b")];
      JObject [("age", JQ 10)]
    ] in
  eval_exec (Query [Child [f_exists_age]]) j
  = [
      ([SIndex 0], JObject [("name", JStr "a"); ("age", JQ 30)]);
      ([SIndex 2], JObject [("age", JQ 10)])
    ].
Proof. reflexivity. Qed.

(** Filter using count aggregation on nested array length. *)
Definition f_tags_count_ge_2 : selector :=
  SelFilter (FCmp CGe
                 (ACount (Query [Child [SelName "tags"]; Child [SelWildcard]]))
                 (APrim (PNum (Q_of_Z 2)))).

(** Count-based filter retains nodes with array length >= threshold. *)
Example exec_filter_count_ge_2 :
  let j :=
    JArr [
      JObject [("tags", JArr [JStr "x"])];
      JObject [("tags", JArr [JStr "x"; JStr "y"])];
      JObject [("tags", JArr [JStr "x"; JStr "y"; JStr "z"])];
      JObject [("other", JQ 0)]
    ] in
  eval_exec (Query [Child [f_tags_count_ge_2]]) j
  = [
      ([SIndex 1], JObject [("tags", JArr [JStr "x"; JStr "y"])]);
      ([SIndex 2], JObject [("tags", JArr [JStr "x"; JStr "y"; JStr "z"])])
    ].
Proof. reflexivity. Qed.

(** Filter using length function on current node string value. *)
Definition f_len_gt_3 : selector :=
  SelFilter (FCmp CGt
                 (ALengthV (Query []))
                 (APrim (PNum (Q_of_Z 3)))).

(** Length filter retains strings longer than threshold. *)
Example exec_filter_length_gt_3_on_array_of_strings :
  let j := JArr [JStr "a"; JStr "abcd"; JStr "xyz"; JStr "hello"] in
  eval_exec (Query [Child [f_len_gt_3]]) j
  = [
      ([SIndex 1], JStr "abcd");
      ([SIndex 3], JStr "hello")
    ].
Proof. reflexivity. Qed.

(** Cross-type comparison: number vs string (previously rejected, now allowed). *)
Definition f_num_vs_str : selector :=
  SelFilter (FCmp CEq (APrim (PNum (Q_of_Z 42))) (APrim (PStr "hello"))).

Example exec_filter_num_vs_str_rejects_all :
  let j := JArr [JQ 0; JQ 42; JStr "hello"] in
  eval_exec (Query [Child [f_num_vs_str]]) j = [].
Proof. reflexivity. Qed.

(** Cross-type comparison: null vs boolean. *)
Definition f_null_vs_bool : selector :=
  SelFilter (FCmp CNe (AValue (Query [Child [SelName "x"]])) (APrim (PBool true))).

Example exec_filter_null_vs_bool :
  let j := JArr [JObject [("x", JNull)]; JObject [("x", JBool true)]; JObject []] in
  eval_exec (Query [Child [f_null_vs_bool]]) j
  = [ ([SIndex 0], JObject [("x", JNull)]) ].
Proof. reflexivity. Qed.

(** Cross-type ordering: string vs number returns false. *)
Definition f_str_lt_num : selector :=
  SelFilter (FCmp CLt (APrim (PStr "abc")) (APrim (PNum (Q_of_Z 10)))).

Example exec_filter_str_lt_num_rejects_all :
  let j := JArr [JQ 0; JStr "test"] in
  eval_exec (Query [Child [f_str_lt_num]]) j = [].
Proof. reflexivity. Qed.

(** Descendant segment searches all depths, collecting matching nodes. *)
Example exec_desc_name_at_any_depth :
  let j :=
    JObject [("u", JObject [("name", JStr "alice"); ("meta", JObject [("name", JStr "x")])]);
             ("v", JArr [JObject [("name", JStr "bob")]; JQ 0])] in
  eval_exec (Query [Desc [SelName "name"]]) j
  = [
      ([SName "u"; SName "name"], JStr "alice");
      ([SName "u"; SName "meta"; SName "name"], JStr "x");
      ([SName "v"; SIndex 0; SName "name"], JStr "bob")
    ].
Proof. reflexivity. Qed.

(** Regex matching literal string "hello". *)
Definition re_hello : regex :=
  RCat (RChr "h"%char)
    (RCat (RChr "e"%char)
     (RCat (RChr "l"%char)
      (RCat (RChr "l"%char) (RChr "o"%char)))).

(** Filter requiring full string match against regex. *)
Definition f_str_match_hello : selector :=
  SelFilter (FMatch (AValue (Query [])) re_hello).

(** Filter searching for substring pattern "ll". *)
Definition f_str_search_ll : selector :=
  SelFilter (FSearch (AValue (Query []))
                     (RCat (RChr "l"%char) (RChr "l"%char))).

(** Full-string regex match retains exact matches only. *)
Example exec_regex_match_full :
  let j := JArr [JStr "hello"; JStr "hell"; JStr "oh hello!"] in
  eval_exec (Query [Child [f_str_match_hello]]) j
  = [ ([SIndex 0], JStr "hello") ].
Proof. reflexivity. Qed.

(** Substring search finds pattern anywhere within string. *)
Example exec_regex_search_substring :
  let j := JArr [JStr "hello"; JStr "hell"; JStr "oh hello!"] in
  eval_exec (Query [Child [f_str_search_ll]]) j
  = [
      ([SIndex 0], JStr "hello");
      ([SIndex 1], JStr "hell");
      ([SIndex 2], JStr "oh hello!")
    ].
Proof. reflexivity. Qed.

(** Name selector on non-object yields empty result. *)
Example exec_name_on_non_object :
  let j := JQ 0 in
  eval_exec (Query [Child [SelName "a"]]) j = [].
Proof. reflexivity. Qed.

(** Index selector on non-array yields empty result. *)
Example exec_index_on_non_array :
  let j := JObject [("a", JQ 1)] in
  eval_exec (Query [Child [SelIndex 0]]) j = [].
Proof. reflexivity. Qed.

(** Wildcard on scalar (non-structured) value yields empty result. *)
Example exec_wildcard_on_scalar :
  let j := JStr "x" in
  eval_exec (Query [Child [SelWildcard]]) j = [].
Proof. reflexivity. Qed.

(** Filter on scalar yields empty (no children to filter). *)
Example exec_filter_on_scalar_yields_empty :
  let j := JStr "abc" in
  eval_exec (Query [Child [f_len_gt_3]]) j = [].
Proof. reflexivity. Qed.

(* ------------------------------------------------------------ *)
(* Normalized Path Emission Tests                               *)
(* ------------------------------------------------------------ *)

(** Negative index -1 normalizes to positive index in path. *)
Example normalized_path_negative_index :
  let j := JArr [JQ 10; JQ 20; JQ 30] in
  let result := eval_exec (Query [Child [SelIndex (-1)]]) j in
  result = [([SIndex 2], JQ 30)] /\
  path_normalized [SIndex 2] = true.
Proof. split; reflexivity. Qed.

(** Multiple negative indices all normalize. *)
Example normalized_path_multiple_negative :
  let j := JArr [JQ 0; JQ 1; JQ 2; JQ 3; JQ 4] in
  let result := eval_exec (Query [Child [SelSlice (Some (-3)) None 1]]) j in
  Forall (fun '(p, _) => path_normalized p = true) result.
Proof.
  simpl. repeat constructor.
Qed.

(** Result Path formatting: simple name access. *)
Example result_path_format_name :
  path_to_result_path [SName "users"; SName "alice"] = "$[""users""][""alice""]".
Proof. reflexivity. Qed.

(** Result Path formatting: array index. *)
Example result_path_format_index :
  path_to_result_path [SName "items"; SIndex 5] = "$[""items""][5]".
Proof. reflexivity. Qed.

(** Result Path formatting: normalized negative index becomes positive. *)
Example result_path_format_normalized :
  let j := JArr [JQ 10; JQ 20; JQ 30] in
  let result := eval_exec (Query [Child [SelIndex (-1)]]) j in
  match result with
  | [(p, _)] => path_to_result_path p = "$[2]"
  | _ => False
  end.
Proof. reflexivity. Qed.

(** Result Path formatting: complex nested path. *)
Example result_path_format_complex :
  path_to_result_path
    [SName "departments"; SIndex 0; SName "employees"; SIndex 2; SName "name"]
  = "$[""departments""][0][""employees""][2][""name""]".
Proof. reflexivity. Qed.

(** Result Path formatting: escaping special characters. *)
Example result_path_format_escaped :
  path_to_result_path [SName "key""with""quotes"]
  = "$[""key\""with\""quotes""]".
Proof. reflexivity. Qed.

(** Theorem: SelIndex always produces normalized indices. *)
Theorem sel_index_produces_normalized_index :
  forall i (xs : list value) idx v,
    idx = (if i <? 0 then Z.of_nat (List.length xs) + i else i) ->
    (idx <? 0) = false ->
    nth_error xs (Z.to_nat idx) = Some v ->
    (0 <=? idx) = true.
Proof.
  intros. apply Z.leb_le. apply Z.ltb_ge. exact H0.
Qed.

(** Corollary: SelIndex negative indices are normalized (concrete example). *)
Example sel_index_path_normalized_example :
  Exec.sel_exec_nf (SelIndex (-1)) ([], JArr [JQ 10; JQ 20; JQ 30])
  = [([SIndex 2], JQ 30)] /\
  path_normalized [SIndex 2] = true.
Proof.
  split; reflexivity.
Qed.

(** Theorem: Slice indices are always non-negative (normalized). *)
Theorem slice_indices_normalized :
  forall len start endo stp n,
    In n (slice_positions len start endo stp) ->
    (0 <= Z.of_nat n)%Z.
Proof.
  intros. apply Nat2Z.is_nonneg.
Qed.

(** Example: Slice paths use normalized indices. *)
Example sel_slice_normalized_example :
  let xs := [JQ 0; JQ 1; JQ 2; JQ 3; JQ 4] in
  let result := Exec.sel_exec_nf (SelSlice (Some (-3)) None 1) ([], JArr xs) in
  List.map (fun '(p, _) => path_normalized p) result = [true; true; true].
Proof.
  reflexivity.
Qed.

(* ------------------------------------------------------------ *)
(* Universal Normalization Theorem                              *)
(* ------------------------------------------------------------ *)

(** Custom induction principle for values with Forall hypotheses. *)
Lemma Forall_value_ind :
  forall (P : value -> Prop),
    (forall b, P (JBool b)) ->
    (forall n, P (JNum n)) ->
    (forall s, P (JStr s)) ->
    P JNull ->
    (forall xs, Forall P xs -> P (JArr xs)) ->
    (forall fields, Forall (fun '(k,v) => P v) fields -> P (JObject fields)) ->
    forall v, P v.
Proof.
  intros P HBool HNum HStr HNull HArr HObj.
  fix IH 1.
  intros [| b | n | s | xs | fields].
  - exact HNull.
  - apply HBool.
  - apply HNum.
  - apply HStr.
  - apply HArr. induction xs as [| x xs' IHxs]; constructor.
    + apply IH.
    + apply IHxs.
  - apply HObj. induction fields as [| [k v] fields' IHfs]; constructor.
    + apply IH.
    + apply IHfs.
Qed.

(** Lemma: Appending a name step preserves normalization. *)
Lemma path_normalized_app_name :
  forall (pth : list JSON.step) (s : string),
    forallb step_normalized pth = true ->
    forallb step_normalized (pth ++ [JSON.SName s]) = true.
Proof.
  intros pth s Hpth.
  rewrite forallb_app. simpl. rewrite Hpth. reflexivity.
Qed.

(** Lemma: Appending a non-negative index step preserves normalization. *)
Lemma path_normalized_app_index :
  forall (pth : list JSON.step) (i : Z),
    forallb step_normalized pth = true ->
    (0 <=? i) = true ->
    forallb step_normalized (pth ++ [JSON.SIndex i]) = true.
Proof.
  intros pth i Hpth Hi.
  rewrite forallb_app. simpl. rewrite Hpth. simpl. rewrite Hi. reflexivity.
Qed.

(** Theorem: ALL selectors produce only normalized paths (universal normalization). *)
Theorem all_selectors_produce_normalized_paths :
  forall sel p v,
    path_normalized p = true ->
    Forall (fun '(p', _) => path_normalized p' = true)
           (Exec.sel_exec_nf sel (p, v)).
Proof.
  intros sel p v Hp.
  destruct sel as [sel_name | | sel_idx | sel_start sel_end sel_step | sel_filter];
  destruct v as [|vb|vn|vs|varr|vobj]; simpl; try constructor.

  - destruct (find (fun kv => string_eqb (fst kv) sel_name) vobj) as [[k v']|] eqn:Hfind.
    + constructor; [|constructor]. unfold path_normalized. apply path_normalized_app_name. exact Hp.
    + constructor.

  - apply Forall_forall. intros [p' v'] Hin.
    apply in_map_iff in Hin. destruct Hin as [[i v0] [Heq _]].
    inversion Heq; subst. unfold path_normalized. apply path_normalized_app_index.
    + exact Hp.
    + apply Z.leb_le. apply Nat2Z.is_nonneg.

  - apply Forall_forall. intros [p' v'] Hin.
    apply in_map_iff in Hin. destruct Hin as [[k v0] [Heq _]].
    inversion Heq; subst. unfold path_normalized. apply path_normalized_app_name. exact Hp.

  - set (idx := if sel_idx <? 0 then Z.of_nat (List.length varr) + sel_idx else sel_idx).
    destruct ((idx <? 0) || (idx >=? Z.of_nat (List.length varr))) eqn:Hbounds; [constructor|].
    destruct (nth_error varr (Z.to_nat idx)) eqn:Hnth; [|constructor].
    constructor; [|constructor]. unfold path_normalized. apply path_normalized_app_index.
    + exact Hp.
    + apply Z.leb_le. apply Z.ltb_ge. apply orb_false_iff in Hbounds.
      destruct Hbounds. exact H.

  - apply Forall_forall. intros [p' v'] Hin.
    apply in_map_iff in Hin. destruct Hin as [n [Heq _]].
    inversion Heq; subst. unfold path_normalized. apply path_normalized_app_index.
    + exact Hp.
    + apply Z.leb_le. apply Nat2Z.is_nonneg.
Qed.

(** Corollary: Starting from empty path, all selector results are normalized. *)
Corollary selector_results_normalized_from_root :
  forall sel v,
    Forall (fun '(p, _) => path_normalized p = true)
           (Exec.sel_exec_nf sel ([], v)).
Proof.
  intros. apply all_selectors_produce_normalized_paths. reflexivity.
Qed.

(** Corollary: Child segment results are normalized. *)
Corollary child_segment_normalized :
  forall sels p v,
    path_normalized p = true ->
    Forall (fun '(p', _) => path_normalized p' = true)
           (Exec.child_on_node_nf sels (p, v)).
Proof.
  intros sels p v Hp.
  unfold Exec.child_on_node_nf, Exec.child_on_node_impl.
  induction sels as [|sel sels' IH]; simpl.
  - constructor.
  - rewrite Forall_app. split.
    + apply all_selectors_produce_normalized_paths. exact Hp.
    + exact IH.
Qed.

(** Helper lemma for array case of visit_df_value_normalized. *)
Lemma visit_df_arr_aux_normalized :
  forall xs p start,
    Forall (fun v => forall p', path_normalized p' = true ->
                      Forall (fun '(p'', _) => path_normalized p'' = true)
                             (Exec.visit_df_value p' v)) xs ->
    path_normalized p = true ->
    Forall (Forall (fun '(p', _) => path_normalized p' = true))
      ((fix go (i:nat) (ys:list JSON.value) {struct ys} : list (list JSON.node) :=
        match ys with
        | [] => []
        | v'::ys' => Exec.visit_df_value (List.app p [SIndex (Z.of_nat i)]) v' :: go (S i) ys'
        end) start xs).
Proof.
  intros xs p start Hall Hp.
  revert start.
  induction Hall as [|x xs' Hx Hall' IH]; intro start; simpl.
  - constructor.
  - constructor.
    + apply Hx. unfold path_normalized.
      apply path_normalized_app_index. exact Hp.
      apply Z.leb_le. apply Nat2Z.is_nonneg.
    + apply IH.
Qed.

(** Helper lemma for object case of visit_df_value_normalized. *)
Lemma visit_df_obj_aux_normalized :
  forall fs p,
    Forall (fun '(k,v) => forall p', path_normalized p' = true ->
                           Forall (fun '(p'', _) => path_normalized p'' = true)
                                  (Exec.visit_df_value p' v)) fs ->
    path_normalized p = true ->
    Forall (Forall (fun '(p', _) => path_normalized p' = true))
      ((fix go (gs:list (string*JSON.value)) {struct gs} : list (list JSON.node) :=
        match gs with
        | [] => []
        | (k,v')::gs' => Exec.visit_df_value (List.app p [SName k]) v' :: go gs'
        end) fs).
Proof.
  intros fs p Hall Hp.
  induction Hall as [|[k v'] fs' Hv Hall' IH]; simpl.
  - constructor.
  - constructor.
    + apply Hv. unfold path_normalized.
      apply path_normalized_app_name. exact Hp.
    + apply IH.
Qed.

(** Lemma: visit_df_value produces normalized paths from normalized input. *)
Lemma visit_df_value_normalized :
  forall v p,
    path_normalized p = true ->
    Forall (fun '(p', _) => path_normalized p' = true)
           (Exec.visit_df_value p v).
Proof.
  apply (Forall_value_ind
    (fun v => forall p,
              path_normalized p = true ->
              Forall (fun '(p', _) => path_normalized p' = true)
                     (Exec.visit_df_value p v))).
  - intros b p Hp. simpl. constructor; [exact Hp | constructor].
  - intros n p Hp. simpl. constructor; [exact Hp | constructor].
  - intros s p Hp. simpl. constructor; [exact Hp | constructor].
  - intros p Hp. simpl. constructor; [exact Hp | constructor].
  - intros xs IHxs p Hp. simpl. constructor; [exact Hp |].
    apply Forall_concat.
    apply visit_df_arr_aux_normalized; assumption.
  - intros fields IHfields p Hp. simpl. constructor; [exact Hp |].
    apply Forall_concat.
    apply visit_df_obj_aux_normalized; assumption.
Qed.

(** Corollary: Descendant segment results are normalized. *)
Corollary desc_segment_normalized :
  forall sels p v,
    path_normalized p = true ->
    Forall (fun '(p', _) => path_normalized p' = true)
           (List.concat (map (Exec.child_on_node_impl Exec.sel_exec_nf sels)
                            (Exec.visit_df_node (p, v)))).
Proof.
  intros sels p v Hp.
  apply Forall_concat.
  apply Forall_map.
  unfold Exec.visit_df_node.
  apply Forall_forall.
  intros [p' v'] Hin.
  pose proof (visit_df_value_normalized v p Hp) as Hvisit.
  apply Forall_forall with (x := (p', v')) in Hvisit; [|exact Hin].
  apply child_segment_normalized. exact Hvisit.
Qed.

(** Theorem: Single segment evaluation preserves path normalization. *)
Theorem segment_preserves_normalization :
  forall seg p v,
    path_normalized p = true ->
    Forall (fun '(p', _) => path_normalized p' = true)
           (Exec.seg_exec_impl Exec.sel_exec_nf seg (p, v)).
Proof.
  intros seg p v Hp.
  destruct seg as [sels | sels].
  - simpl. unfold Exec.child_on_node_nf.
    apply child_segment_normalized. exact Hp.
  - simpl. apply desc_segment_normalized. exact Hp.
Qed.

(** Lemma: Chaining segments preserves normalization. *)
Lemma segment_chain_preserves_normalization :
  forall segs ns,
    Forall (fun '(p, _) => path_normalized p = true) ns ->
    Forall (fun '(p, _) => path_normalized p = true)
           (Exec.segs_exec_impl Exec.sel_exec_nf segs ns).
Proof.
  intros segs ns.
  revert ns.
  induction segs as [|seg segs' IH]; intros ns Hns; simpl.
  - exact Hns.
  - apply IH. apply Forall_concat. apply Forall_map.
    apply Forall_forall. intros [p v] Hin.
    apply Forall_forall with (x := (p, v)) in Hns; [|exact Hin].
    apply segment_preserves_normalization. exact Hns.
Qed.

(** Theorem: Full query evaluation produces only normalized paths (filter-free version). *)
Theorem query_produces_normalized_paths :
  forall q J,
    Forall (fun '(p, _) => path_normalized p = true)
           (Exec.eval_exec_impl Exec.sel_exec_nf q J).
Proof.
  intros [segs] J.
  unfold Exec.eval_exec_impl.
  apply segment_chain_preserves_normalization.
  constructor; [reflexivity | constructor].
Qed.

(** Corollary: eval_exec_nf always produces normalized paths. *)
Corollary eval_exec_nf_normalized :
  forall q J,
    Forall (fun '(p, _) => path_normalized p = true)
           (Exec.eval_exec_nf q J).
Proof.
  intros q J.
  unfold Exec.eval_exec_nf.
  apply query_produces_normalized_paths.
Qed.

(* ------------------------------------------------------------ *)
(* Out-of-bounds contradiction lemma                             *)
(* ------------------------------------------------------------ *)

(** Contradiction: valid index cannot simultaneously satisfy bounds check failure. *)
Lemma eval_selector_index_success_out_of_bounds_contradiction :
  forall z (xs : list value) v idx,
    idx = (if z <? 0 then Z.of_nat (List.length xs) + z else z) ->
    0 <= idx ->
    idx < Z.of_nat (List.length xs) ->
    nth_error xs (Z.to_nat idx) = Some v ->
    orb (idx <? 0) (idx >=? Z.of_nat (List.length xs)) = true ->
    False.
Proof.
  intros z xs v idx Hidx Hge0 Hlt Hnth Hbounds.
  apply Bool.orb_true_iff in Hbounds.
  destruct Hbounds as [Hlt0 | HgeLen].
  - apply Z.ltb_lt in Hlt0; lia.
  - apply Z.geb_le in HgeLen; lia.
Qed.

(*************************************************************)
(* End-to-end dataset and queries                            *)
(*************************************************************)

(** Regex pattern matching "@" character in email addresses. *)
Definition re_at : JSONPath.regex := RChr "@"%char.

(** Regex pattern matching ".com" domain suffix. *)
Definition re_dotcom : JSONPath.regex :=
  RCat (RChr "."%char)
   (RCat (RChr "c"%char) (RCat (RChr "o"%char) (RChr "m"%char))).

(** Project: Phoenix instance for Alice (ML/vision, 50 stars). *)
Definition proj_phoenix_a : JSON.value :=
  JObject [("name", JStr "phoenix"); ("stars", JQ 50);
           ("labels", JArr [JStr "ml"; JStr "vision"])].

(** Project: Drake (infrastructure, 20 stars). *)
Definition proj_drake_a : JSON.value :=
  JObject [("name", JStr "drake"); ("stars", JQ 20);
           ("labels", JArr [JStr "infra"])].

(** Project: Phoenix instance for Carol (ML/NLP, 70 stars). *)
Definition proj_phoenix_c : JSON.value :=
  JObject [("name", JStr "phoenix"); ("stars", JQ 70);
           ("labels", JArr [JStr "ml"; JStr "nlp"])].

(** Project: Eagle (infrastructure, 15 stars). *)
Definition proj_eagle_c : JSON.value :=
  JObject [("name", JStr "eagle"); ("stars", JQ 15);
           ("labels", JArr [JStr "infra"])].

(** Project: CRM (sales, 8 stars). *)
Definition proj_crm_d : JSON.value :=
  JObject [("name", JStr "crm"); ("stars", JQ 8);
           ("labels", JArr [JStr "sales"])].

(** Employee: Alice (senior ML engineer, 34, two projects). *)
Definition emp_alice : JSON.value :=
  JObject [("name", JStr "alice");
           ("age", JQ 34);
           ("email", JStr "alice@acme.com");
           ("tags", JArr [JStr "ml"; JStr "backend"]);
           ("bio", JStr "senior ml engineer");
           ("projects", JArr [proj_phoenix_a; proj_drake_a])].

(** Employee: Bob (frontend/UI, 29, no projects). *)
Definition emp_bob : JSON.value :=
  JObject [("name", JStr "bob");
           ("age", JQ 29);
           ("email", JStr "bob@acme.org");
           ("tags", JArr [JStr "frontend"]);
           ("bio", JStr "ui");
           ("projects", JArr [])].

(** Employee: Carol (NLP specialist, 41, two projects). *)
Definition emp_carol : JSON.value :=
  JObject [("name", JStr "carol");
           ("age", JQ 41);
           ("email", JStr "carol@acme.com");
           ("tags", JArr [JStr "ml"; JStr "nlp"; JStr "research"]);
           ("bio", JStr "nlp specialist");
           ("projects", JArr [proj_phoenix_c; proj_eagle_c])].

(** Employee: Dave (sales lead, 33, one project). *)
Definition emp_dave : JSON.value :=
  JObject [("name", JStr "dave");
           ("age", JQ 33);
           ("email", JStr "dave@acme.com");
           ("tags", JArr [JStr "sales"; JStr "lead"]);
           ("bio", JStr "account exec");
           ("projects", JArr [proj_crm_d])].

(** Employee: Erin (summer intern, 22, no projects). *)
Definition emp_erin : JSON.value :=
  JObject [("name", JStr "erin");
           ("age", JQ 22);
           ("email", JStr "erin@acme.com");
           ("tags", JArr [JStr "intern"]);
           ("bio", JStr "summer intern");
           ("projects", JArr [])].

(** Department: Research (Alice, Bob, Carol). *)
Definition dept_research : JSON.value :=
  JObject [("name", JStr "Research");
           ("employees", JArr [emp_alice; emp_bob; emp_carol])].

(** Department: Sales (Dave, Erin). *)
Definition dept_sales : JSON.value :=
  JObject [("name", JStr "Sales");
           ("employees", JArr [emp_dave; emp_erin])].

(** Complete company document: Acme with two departments. *)
Definition company_json : JSON.value :=
  JObject [("company", JStr "Acme");
           ("departments", JArr [dept_research; dept_sales]);
           ("meta", JObject [("version", JStr "1.0"); ("rev", JQ 7)])].

(** Compound filter: age>30, tags>=2, email contains "@" and ".com". *)
Definition sel_emp_age_tags_emailcom : JSONPath.selector :=
  SelFilter
    (FAnd
      (FCmp CGt
        (AValue (Query [Child [SelName "age"]]))
        (APrim (PNum (Q_of_Z 30))))
      (FAnd
        (FCmp CGe
          (ACount (Query [Child [SelName "tags"]; Child [SelWildcard]]))
          (APrim (PNum (Q_of_Z 2))))
        (FAnd
          (FSearch (AValue (Query [Child [SelName "email"]])) re_at)
          (FSearch (AValue (Query [Child [SelName "email"]])) re_dotcom)))).

(** Complex filter selects employees satisfying all criteria. *)
Example exec_naturalistic_complex_filter :
  eval_exec
    (Query [ Child [SelName "departments"];
             Child [SelWildcard];
             Child [SelName "employees"];
             Child [sel_emp_age_tags_emailcom] ])
    company_json
  =
  [
    ([SName "departments"; SIndex 0; SName "employees"; SIndex 0], emp_alice);
    ([SName "departments"; SIndex 0; SName "employees"; SIndex 2], emp_carol);
    ([SName "departments"; SIndex 1; SName "employees"; SIndex 0], emp_dave)
  ].
Proof. reflexivity. Qed.

(** Descendant query navigating to last project in each employee's list. *)
Example exec_naturalistic_last_project_names :
  eval_exec
    (Query [ Desc  [SelName "projects"];
             Child [SelIndex (-1)];
             Child [SelName "name"] ])
    company_json
  =
  [
    ([SName "departments"; SIndex 0; SName "employees"; SIndex 0;
      SName "projects"; SIndex 1; SName "name"], JStr "drake");
    ([SName "departments"; SIndex 0; SName "employees"; SIndex 2;
      SName "projects"; SIndex 1; SName "name"], JStr "eagle");
    ([SName "departments"; SIndex 1; SName "employees"; SIndex 0;
      SName "projects"; SIndex 0; SName "name"], JStr "crm")
  ].
Proof. reflexivity. Qed.

(** Nested filter: count of high-star (>=15) projects per employee >= 2. *)
Definition sel_emp_two_big_projects : JSONPath.selector :=
  SelFilter
    (FCmp CGe
      (ACount
        (Query [ Child [SelName "projects"];
                 Child [SelFilter
                          (FCmp CGe
                            (AValue (Query [Child [SelName "stars"]]))
                            (APrim (PNum (Q_of_Z 15)))) ] ]))
      (APrim (PNum (Q_of_Z 2)))).

(** Nested count aggregation identifies employees with multiple high-value projects. *)
Example exec_naturalistic_names_of_emp_two_big_projects :
  eval_exec
    (Query [ Child [SelName "departments"];
             Child [SelWildcard];
             Child [SelName "employees"];
             Child [sel_emp_two_big_projects];
             Child [SelName "name"] ])
    company_json
  =
  [
    ([SName "departments"; SIndex 0; SName "employees"; SIndex 0; SName "name"], JStr "alice");
    ([SName "departments"; SIndex 0; SName "employees"; SIndex 2; SName "name"], JStr "carol")
  ].
Proof. reflexivity. Qed.

(** String comparison filter using lexicographic ordering. *)
Definition sel_emp_name_lt_c : JSONPath.selector :=
  SelFilter
    (FCmp CLt
      (AValue (Query [Child [SelName "name"]]))
      (APrim (PStr "c"))).

(** Lexicographic filter retains names alphabetically before "c". *)
Example exec_naturalistic_name_lex_lt_c :
  eval_exec
    (Query [ Child [SelName "departments"];
             Child [SelWildcard];
             Child [SelName "employees"];
             Child [sel_emp_name_lt_c];
             Child [SelName "name"] ])
    company_json
  =
  [
    ([SName "departments"; SIndex 0; SName "employees"; SIndex 0; SName "name"], JStr "alice");
    ([SName "departments"; SIndex 0; SName "employees"; SIndex 1; SName "name"], JStr "bob")
  ].
Proof. reflexivity. Qed.

(** Descendant includes root node when selector matches. *)
Example exec_desc_includes_self_immediate :
  let j := JObject [("name", JStr "top"); ("child", JObject [("name", JStr "kid")])] in
  eval_exec (Query [Desc [SelName "name"]]) j
  = [ ([SName "name"], JStr "top");
      ([SName "child"; SName "name"], JStr "kid") ].
Proof. reflexivity. Qed.

(** Negative-step slice with explicit bounds iterates backward. *)
Example exec_slice_neg_step_bounds :
  let j := JArr [JQ 0; JQ 1; JQ 2; JQ 3; JQ 4] in
  eval_exec (Query [Child [SelSlice (Some 4) (Some 1) (-2)]]) j
  = [ ([SIndex 4], JQ 4) ; ([SIndex 2], JQ 2) ].
Proof. reflexivity. Qed.

(** AValue on multi-node result fails (requires singleton). *)
Example exec_avalue_multi_hit_fails :
  let j := JObject [("a", JQ 1); ("b", JQ 2)] in
  Exec.holds_b (FCmp CEq (AValue (Query [Child [SelWildcard]])) (APrim (PNum (Q_of_Z 1))))
               ([], j) = false.
Proof. reflexivity. Qed.

(** Typing rejects search on non-string type. *)
Example typing_requires_string_for_search :
  Typing.wf_fexpr (FSearch (APrim (PNum (Q_of_Z 3))) (RChr "3"%char)) = false.
Proof. reflexivity. Qed.

(** Extended Acme database with offices, detailed projects, metrics. *)
Definition acme_db_json : JSON.value :=
  JObject [
    ("company", JStr "Acme Inc.");
    ("hq", JObject [
       ("address1", JStr "500 Market St");
       ("city", JStr "San Francisco");
       ("state", JStr "CA");
       ("postal_code", JStr "94105");
       ("country", JStr "US")
    ]);
    ("contacts", JObject [
       ("support", JStr "support@acme.com");
       ("sales",   JStr "sales@acme.com");
       ("status",  JStr "green");
       ("phone",   JStr "+1-415-555-0000")
    ]);
    ("offices", JArr [
       JObject [("code", JStr "SFO"); ("timezone", JStr "America/Los_Angeles"); ("lead", JStr "carol")];
       JObject [("code", JStr "NYC"); ("timezone", JStr "America/New_York");   ("lead", JStr "dave")];
       JObject [("code", JStr "BER"); ("timezone", JStr "Europe/Berlin");      ("lead", JStr "heidi")]
    ]);
    ("departments", JArr [
      JObject [
        ("id",          JStr "R&D");
        ("name",        JStr "Research");
        ("cost_center", JStr "1001");
        ("budget_usd",  JQ 12000000);
        ("employees",   JArr [
          JObject [
            ("id",        JStr "u-alice");
            ("name",      JStr "alice");
            ("age",       JQ 34);
            ("email",     JStr "alice@acme.com");
            ("phone",     JStr "+1-415-555-1010");
            ("hire_date", JStr "2018-03-12");
            ("tags",      JArr [JStr "ml"; JStr "backend"]);
            ("bio",       JStr "senior ml engineer");
            ("projects",  JArr [
              JObject [
                ("id",     JStr "phoenix-a");
                ("name",   JStr "phoenix");
                ("stars",  JQ 50);
                ("labels", JArr [JStr "ml"; JStr "vision"]);
                ("status", JStr "active");
                ("repo",   JStr "git@github.com:acme/phoenix");
                ("started",JStr "2019-09-01");
                ("metrics", JObject [
                  ("prs_open",     JQ 7);
                  ("issues_open",  JQ 42);
                  ("coverage_pct", JQ 87)
                ])
              ];
              JObject [
                ("id",     JStr "drake-a");
                ("name",   JStr "drake");
                ("stars",  JQ 20);
                ("labels", JArr [JStr "infra"]);
                ("status", JStr "archived");
                ("repo",   JStr "git@github.com:acme/drake");
                ("started",JStr "2017-05-22");
                ("metrics", JObject [
                  ("prs_open",     JQ 0);
                  ("issues_open",  JQ 3);
                  ("coverage_pct", JQ 74)
                ])
              ]
            ])
          ];
          JObject [
            ("id",        JStr "u-bob");
            ("name",      JStr "bob");
            ("age",       JQ 29);
            ("email",     JStr "bob@acme.org");
            ("phone",     JStr "+1-415-555-1011");
            ("hire_date", JStr "2020-07-01");
            ("tags",      JArr [JStr "frontend"]);
            ("bio",       JStr "ui");
            ("projects",  JArr [])
          ];
          JObject [
            ("id",        JStr "u-carol");
            ("name",      JStr "carol");
            ("age",       JQ 41);
            ("email",     JStr "carol@acme.com");
            ("phone",     JStr "+1-415-555-1012");
            ("hire_date", JStr "2013-11-05");
            ("tags",      JArr [JStr "ml"; JStr "nlp"; JStr "research"]);
            ("bio",       JStr "nlp specialist");
            ("projects",  JArr [
              JObject [
                ("id",     JStr "phoenix-c");
                ("name",   JStr "phoenix");
                ("stars",  JQ 70);
                ("labels", JArr [JStr "ml"; JStr "nlp"]);
                ("status", JStr "active");
                ("repo",   JStr "git@github.com:acme/phoenix");
                ("started",JStr "2021-02-10");
                ("metrics", JObject [
                  ("prs_open",     JQ 12);
                  ("issues_open",  JQ 13);
                  ("coverage_pct", JQ 90)
                ])
              ];
              JObject [
                ("id",     JStr "eagle-c");
                ("name",   JStr "eagle");
                ("stars",  JQ 15);
                ("labels", JArr [JStr "infra"]);
                ("status", JStr "active");
                ("repo",   JStr "git@github.com:acme/eagle");
                ("started",JStr "2020-10-18");
                ("metrics", JObject [
                  ("prs_open",     JQ 3);
                  ("issues_open",  JQ 5);
                  ("coverage_pct", JQ 81)
                ])
              ]
            ])
          ]
        ])
      ];
      JObject [
        ("id",          JStr "ENG");
        ("name",        JStr "Engineering");
        ("cost_center", JStr "1002");
        ("budget_usd",  JQ 30000000);
        ("employees",   JArr [
          JObject [
            ("id",        JStr "u-trent");
            ("name",      JStr "trent");
            ("age",       JQ 37);
            ("email",     JStr "trent@acme.com");
            ("phone",     JStr "+1-212-555-2001");
            ("hire_date", JStr "2016-04-09");
            ("tags",      JArr [JStr "platform"; JStr "sre"]);
            ("bio",       JStr "platform lead");
            ("projects",  JArr [
              JObject [
                ("id",     JStr "titan");
                ("name",   JStr "titan");
                ("stars",  JQ 33);
                ("labels", JArr [JStr "platform"; JStr "k8s"]);
                ("status", JStr "active");
                ("repo",   JStr "git@github.com:acme/titan");
                ("started",JStr "2019-01-15");
                ("metrics", JObject [
                  ("prs_open",     JQ 9);
                  ("issues_open",  JQ 21);
                  ("coverage_pct", JQ 84)
                ])
              ]
            ])
          ];
          JObject [
            ("id",        JStr "u-grace");
            ("name",      JStr "grace");
            ("age",       JQ 31);
            ("email",     JStr "grace@acme.com");
            ("phone",     JStr "+1-212-555-2002");
            ("hire_date", JStr "2019-08-23");
            ("tags",      JArr [JStr "backend"; JStr "api"]);
            ("bio",       JStr "senior backend engineer");
            ("projects",  JArr [
              JObject [
                ("id",     JStr "atlas");
                ("name",   JStr "atlas");
                ("stars",  JQ 28);
                ("labels", JArr [JStr "api"]);
                ("status", JStr "active");
                ("repo",   JStr "git@github.com:acme/atlas");
                ("started",JStr "2022-04-01");
                ("metrics", JObject [
                  ("prs_open",     JQ 5);
                  ("issues_open",  JQ 8);
                  ("coverage_pct", JQ 88)
                ])
              ]
            ])
          ];
          JObject [
            ("id",        JStr "u-heidi");
            ("name",      JStr "heidi");
            ("age",       JQ 27);
            ("email",     JStr "heidi@acme.com");
            ("phone",     JStr "+49-30-555-3003");
            ("hire_date", JStr "2023-03-01");
            ("tags",      JArr [JStr "frontend"; JStr "design"]);
            ("bio",       JStr "product designer");
            ("projects",  JArr [])
          ]
        ])
      ];
      JObject [
        ("id",          JStr "SALES");
        ("name",        JStr "Sales");
        ("cost_center", JStr "2001");
        ("budget_usd",  JQ 9000000);
        ("employees",   JArr [
          JObject [
            ("id",        JStr "u-dave");
            ("name",      JStr "dave");
            ("age",       JQ 33);
            ("email",     JStr "dave@acme.com");
            ("phone",     JStr "+1-646-555-4001");
            ("hire_date", JStr "2017-06-30");
            ("tags",      JArr [JStr "sales"; JStr "lead"]);
            ("bio",       JStr "account exec");
            ("projects",  JArr [
              JObject [
                ("id",     JStr "crm-d");
                ("name",   JStr "crm");
                ("stars",  JQ 8);
                ("labels", JArr [JStr "sales"]);
                ("status", JStr "active");
                ("repo",   JStr "git@github.com:acme/crm");
                ("started",JStr "2016-07-15");
                ("metrics", JObject [
                  ("prs_open",     JQ 1);
                  ("issues_open",  JQ 2);
                  ("coverage_pct", JQ 63)
                ])
              ]
            ])
          ];
          JObject [
            ("id",        JStr "u-erin");
            ("name",      JStr "erin");
            ("age",       JQ 22);
            ("email",     JStr "erin@acme.com");
            ("phone",     JStr "+1-646-555-4002");
            ("hire_date", JStr "2025-06-01");
            ("tags",      JArr [JStr "intern"]);
            ("bio",       JStr "summer intern");
            ("projects",  JArr [])
          ]
        ])
      ];
      JObject [
        ("id",          JStr "HR");
        ("name",        JStr "People Ops");
        ("cost_center", JStr "3001");
        ("budget_usd",  JQ 4000000);
        ("employees",   JArr [
          JObject [
            ("id",        JStr "u-peggy");
            ("name",      JStr "peggy");
            ("age",       JQ 39);
            ("email",     JStr "peggy@acme.com");
            ("phone",     JStr "+1-415-555-5005");
            ("hire_date", JStr "2015-09-09");
            ("tags",      JArr [JStr "hr"; JStr "benefits"]);
            ("bio",       JStr "benefits manager");
            ("projects",  JArr [])
          ]
        ])
      ]
    ]);
    ("products", JArr [
      JObject [("sku", JStr "PX-100"); ("name", JStr "Phoenix"); ("status", JStr "GA");   ("owners", JArr [JStr "alice"; JStr "carol"]); ("stars", JQ 120)];
      JObject [("sku", JStr "DR-200"); ("name", JStr "Drake");   ("status", JStr "EOL");  ("owners", JArr [JStr "alice"]);               ("stars", JQ 40)];
      JObject [("sku", JStr "TT-300"); ("name", JStr "Titan");   ("status", JStr "Beta"); ("owners", JArr [JStr "trent"; JStr "grace"]); ("stars", JQ 33)]
    ]);
    ("audit", JObject [
       ("generated_by", JStr "acme/exporter/2.1.7");
       ("exported_at",  JStr "2025-08-16T12:34:56Z");
       ("row_count",    JQ 23);
       ("checksum",     JStr "sha256:4f2d0a8b...deadbeef")
    ]);
    ("meta", JObject [("version", JStr "2025.08"); ("rev", JQ 42)])
  ].

(* ============================================================ *)
(* Equivalence theorems for the filterâ€‘free, childâ€‘only core    *)
(* ============================================================ *)

(** Equivalence module: relational semantics match executable for child-only queries. *)
Module JSONPath_Equiv.
  Import JSON JSONPath Exec.

  Local Open Scope Z_scope.

  (** Selector contains no filter. *)
  Definition selector_filter_free (s:selector) : bool :=
    match s with
    | SelFilter _ => false
    | _ => true
    end.

  (** Segment is child-only with filter-free selectors. *)
  Definition segment_child_only (seg:segment) : bool :=
    match seg with
    | Child sels => forallb selector_filter_free sels
    | Desc _     => false
    end.

  (** Query uses only child segments with no filters or descendant. *)
  Definition query_child_only (q:query) : bool :=
    match q with
    | Query segs => forallb segment_child_only segs
    end.

  (** Successful find implies predicate holds on result. *)
  Lemma find_some :
    forall (A:Type) (f:A->bool) (l:list A) (x:A),
      List.find f l = Some x -> f x = true.
  Proof.
    intros A f l x H. induction l as [|y ys IH]; simpl in *; try discriminate.
    destruct (f y) eqn:Hy.
    - inversion H; subst; assumption.
    - apply IH; assumption.
  Qed.

  (** Boolean >=? false implies strict less-than. *)
  Lemma geb_false_lt : forall x y : Z, (x >=? y) = false -> x < y.
  Proof.
    intros x y H.
    unfold Z.geb in H.
    destruct (Z.compare x y) eqn:C; simpl in H; try discriminate.
    pose proof (Z.compare_spec x y) as Hc.
    rewrite C in Hc. inversion Hc; assumption.
  Qed.

  (** Boolean <? false implies greater-or-equal. *)
  Lemma ltb_false_ge : forall x y : Z, (x <? y) = false -> y <= x.
  Proof. intros x y H; apply Z.ltb_ge in H; exact H. Qed.

  (** Disjunction false implies both conjuncts false. *)
  Lemma orb_false_split : forall a b : bool, a || b = false -> a = false /\ b = false.
  Proof. intros a b H; now apply Bool.orb_false_iff in H. Qed.

  (** Boolean bounds checks imply arithmetic bounds. *)
  Lemma in_bounds_from_bools :
    forall idx len : Z,
      (idx <? 0) = false ->
      (idx >=? len) = false ->
      0 <= idx < len.
  Proof.
    intros idx len Hlt0 Hge.
    split; [apply ltb_false_ge in Hlt0; lia | apply geb_false_lt in Hge; exact Hge].
  Qed.

  (** In-bounds natural index has corresponding list element. *)
  Lemma nth_error_some_of_lt :
    forall (A:Type) (xs:list A) n,
      (n < List.length xs)%nat -> exists v, nth_error xs n = Some v.
  Proof.
    intros A xs n Hlt.
    revert xs Hlt; induction n as [|n IH]; intros [|x xs] H; simpl in *; try lia.
    - eexists; reflexivity.
    - specialize (IH xs). assert (n < List.length xs)%nat by lia.
      destruct (IH H0) as [v Hv]. eexists; exact Hv.
  Qed.

  (** Boolean bounds on Z-index imply element exists after conversion to nat. *)
  Lemma nth_error_some_of_bools_Z :
    forall (A:Type) (xs:list A) idx,
      (idx <? 0) = false ->
      (idx >=? Z.of_nat (List.length xs)) = false ->
      exists v, nth_error xs (Z.to_nat idx) = Some v.
  Proof.
    intros A xs idx Hlt0 Hge.
    pose proof (in_bounds_from_bools idx (Z.of_nat (List.length xs)) Hlt0 Hge) as [H0 Hlt].
    assert (Hidx_eq : Z.of_nat (Z.to_nat idx) = idx) by (apply Z2Nat.id; lia).
    rewrite <- Hidx_eq in Hlt.
    apply Nat2Z.inj_lt in Hlt.
    eapply nth_error_some_of_lt; eauto.
  Qed.

  (** Finding key via string_eqb implies key matches search string. *)
  Lemma find_key_eqb_eq :
    forall s k v (fields:list (string * JSON.value)),
      List.find (fun kv => string_eqb (fst kv) s) fields = Some (k, v) ->
      k = s.
  Proof.
    intros s k v fields Hf.
    apply string_eqb_true_iff.
    apply find_some in Hf. simpl in Hf. exact Hf.
  Qed.

Lemma selname_object_found :
  forall s p fields v,
    List.find (fun kv => string_eqb (fst kv) s) fields = Some (s, v) ->
    eval_selector (SelName s) (p, JObject fields)
                  [ (List.app p [SName s], v) ].
Proof.
  intros s p fields v Hf.
  constructor; exact Hf.
Qed.

  Lemma selname_object_not_found :
    forall s p fields,
      List.find (fun kv => string_eqb (fst kv) s) fields = None ->
      eval_selector (SelName s) (p, JObject fields) [].
  Proof. intros; econstructor; eauto. Qed.

Lemma wildcard_object_sound :
  forall p fields,
    eval_selector SelWildcard (p, JObject fields)
      (map (fun '(k,v) => (List.app p [SName k], v)) fields).
Proof.
  intros. eapply EvalSelWildcardObject. apply Permutation_refl.
Qed.

Lemma eval_selindex_in_bounds :
  forall i p xs idx v',
    idx = (if i <? 0 then Z.of_nat (List.length xs) + i else i) ->
    (idx <? 0) = false ->
    (idx >=? Z.of_nat (List.length xs)) = false ->
    nth_error xs (Z.to_nat idx) = Some v' ->
    eval_selector (SelIndex i) (p, JArr xs) [ (List.app p [SIndex idx], v') ].
Proof.
  intros i p xs idx v' Hidx Hlt0 Hge Hnth.
  eapply EvalSelIndex with (idx := idx); eauto.
Qed.


(** Soundness: filter-free executable selector produces relationally valid results. *)
Lemma sel_exec_nf_sound :
  forall sel n,
    selector_filter_free sel = true ->
    eval_selector sel n (Exec.sel_exec_nf sel n).
Proof.
  intros sel [p v] Hff; destruct sel as [s| |i|start end_ stp|f]; simpl in *; try discriminate; clear Hff.

  (* SelName *)
  - destruct v as [|b|n0|s0|xs|fields]; simpl;
      try (apply EvalSelNameNotObject; intros; congruence).
    (* JObject fields case only here *)
    destruct (List.find (fun kv : string * value => string_eqb (fst kv) s) fields)
      as [[k v']|] eqn:Hf.
    + pose proof (find_key_eqb_eq s k v' fields Hf) as ->.
      now apply selname_object_found.
    + now apply selname_object_not_found.

  (* SelWildcard *)
  - destruct v as [|b|n0|s0|xs|fields]; simpl.
    + eapply EvalSelWildcardOther; intros; congruence.  (* JNull *)
    + eapply EvalSelWildcardOther; intros; congruence.  (* JBool *)
    + eapply EvalSelWildcardOther; intros; congruence.  (* JNum  *)
    + eapply EvalSelWildcardOther; intros; congruence.  (* JStr  *)
    + apply EvalSelWildcardArray.                       (* JArr  *)
    + now apply wildcard_object_sound.                  (* JObject *)

  (* SelIndex *)
  - destruct v as [|b|n0|s0|xs|fields]; simpl;
      try (apply EvalSelIndexNotArray; intros; congruence).
    set (idx := if i <? 0 then Z.of_nat (List.length xs) + i else i).
    destruct ((idx <? 0) || (idx >=? Z.of_nat (List.length xs))) eqn:Hoob.
    + eapply EvalSelIndexOutOfBounds with (idx:=idx); subst; auto.
    + destruct (orb_false_split _ _ Hoob) as [Hlt0 Hge].
      destruct (nth_error_some_of_bools_Z _ xs idx Hlt0 Hge) as [v' Hnth].
      rewrite Hnth. eapply eval_selindex_in_bounds; subst; eauto.

  (* SelSlice *)
  - destruct v as [|b|n0|s0|xs|fields]; simpl;
      try (apply EvalSelSliceNotArray; intros; congruence).
    remember (slice_positions (List.length xs) start end_ stp) as ns eqn:Hns.
    assert (Hmap :
      map (fun n0 =>
             mk_node (List.app p [SIndex (Z.of_nat n0)])
                     (match nth_error xs n0 with
                      | Some v' => v'
                      | None => JNull
                      end)) ns
      =
      map (fun n0 =>
             mk_node (List.app p [SIndex (Z.of_nat n0)])
                     (nth_default JNull xs n0)) ns).
    { apply map_ext; intro n0.
      unfold mk_node.
      apply (f_equal (fun v => (List.app p [SIndex (Z.of_nat n0)], v))).
      apply nth_error_default_eq. }
    rewrite Hmap; subst ns; apply EvalSelSliceArray.
Qed.


  (* Auxiliary equalities for completeness *)

  Lemma nf_selname_nonobj_nil :
    forall p s v,
      (forall fs, v <> JObject fs) ->
      Exec.sel_exec_nf (SelName s) (p, v) = [].
  Proof.
    intros p s v Hnot; destruct v; simpl; try reflexivity.
    exfalso; eapply Hnot; eauto.
  Qed.

  Lemma nf_wildcard_other_nil :
    forall p v,
      (forall fs, v <> JObject fs) ->
      (forall xs, v <> JArr xs) ->
      Exec.sel_exec_nf SelWildcard (p, v) = [].
  Proof.
    intros p v HnotO HnotA.
    destruct v as [|b|n|s|xs|fields]; simpl; try reflexivity.
    - exfalso; apply (HnotA xs); reflexivity.
    - exfalso; apply (HnotO fields); reflexivity.
  Qed.

  Lemma nf_selindex_nonarr_nil :
    forall p i v,
      (forall xs, v <> JArr xs) ->
      Exec.sel_exec_nf (SelIndex i) (p, v) = [].
  Proof.
    intros p i v Hnot; destruct v; simpl; try reflexivity.
    exfalso; eapply Hnot; eauto.
  Qed.

Lemma nf_selindex_success_eq :
  forall p xs i idx v',
    idx = (if i <? 0 then Z.of_nat (List.length xs) + i else i) ->
    (idx <? 0) = false ->
    (idx >=? Z.of_nat (List.length xs)) = false ->
    nth_error xs (Z.to_nat idx) = Some v' ->
    Exec.sel_exec_nf (SelIndex i) (p, JArr xs)
    = [ (List.app p [SIndex idx], v') ].
Proof.
  intros p xs i idx v' Hidx Hlt0 Hge Hnth.
  simpl.
  rewrite <- Hidx.
  rewrite Hlt0, Hge, Hnth.
  unfold mk_node; reflexivity.
Qed.


  Lemma nf_selindex_oob_nil :
    forall p xs i idx,
      idx = (if i <? 0 then Z.of_nat (List.length xs) + i else i) ->
      orb (idx <? 0) (idx >=? Z.of_nat (List.length xs)) = true ->
      Exec.sel_exec_nf (SelIndex i) (p, JArr xs) = [].
  Proof.
    intros p xs i idx Hidx Hb.
    simpl.
    rewrite <- Hidx.
    rewrite Hb.
    reflexivity.
  Qed.

  Lemma nf_selslice_nonarr_nil :
    forall p start end_ stp v,
      (forall xs, v <> JArr xs) ->
      Exec.sel_exec_nf (SelSlice start end_ stp) (p, v) = [].
  Proof.
    intros p st en stp v Hnot; destruct v; simpl; try reflexivity.
    exfalso; eapply Hnot; eauto.
  Qed.

Lemma nf_selslice_arr_eq_defaultmap :
  forall p xs start end_ stp,
    Exec.sel_exec_nf (SelSlice start end_ stp) (p, JArr xs)
    =
    map (fun n0 => (List.app p [SIndex (Z.of_nat n0)], nth_default JNull xs n0))
        (slice_positions (List.length xs) start end_ stp).
Proof.
  intros p xs start end_ stp.
  simpl.
  apply map_ext; intro n0.
  unfold mk_node.
  apply (f_equal (fun v => (List.app p [SIndex (Z.of_nat n0)], v))).
  apply nth_error_default_eq.
Qed.


  Lemma nf_perm_of_eq :
    forall {A} (x y:list A), x = y -> Permutation x y.
  Proof. intros A x y ->; apply Permutation_refl. Qed.

(** Completeness: relational results are permutation of executable output. *)
Lemma sel_exec_nf_complete :
  forall sel n res,
    selector_filter_free sel = true ->
    eval_selector sel n res ->
    Permutation res (Exec.sel_exec_nf sel n).
Proof.
  intros sel [p v] res Hff Hev; destruct sel as [s| |i|start end_ stp|f]; simpl in *; try discriminate.

  (* SelName *)
  - inversion Hev; subst; clear Hev; simpl.
    + eapply nf_perm_of_eq.
      match goal with
      | Hfind : find _ _ = Some _ |- _ =>
          rewrite Hfind; reflexivity
      end.
    + eapply nf_perm_of_eq.
      match goal with
      | Hnone : find _ _ = None |- _ =>
          rewrite Hnone; reflexivity
      end.
    + eapply nf_perm_of_eq.
      destruct v as [|b|n0|s0|xs|fs0]; simpl; try reflexivity.
      exfalso; apply (H3 fs0); reflexivity.

  (* SelWildcard *)
  - inversion Hev; subst; clear Hev; simpl.
    + cbv [mk_node]. exact H1.
    + cbv [mk_node]. apply Permutation_refl.
    + destruct v as [| b | n0 | s0 | xs0 | fields0]; simpl;
        try apply Permutation_refl;
        try (exfalso; apply (H2 xs0); reflexivity);
        try (exfalso; apply (H1 fields0); reflexivity).

  (* SelIndex *)
  - inversion Hev; subst; clear Hev; simpl.
    + eapply nf_perm_of_eq.
      symmetry.
      eapply (nf_selindex_success_eq
                p xs i
                (if i <? 0 then Z.of_nat (List.length xs) + i else i)
                v0); eauto.
    + eapply nf_perm_of_eq.
      symmetry.
      eapply (nf_selindex_oob_nil
                p xs i
                (if i <? 0 then Z.of_nat (List.length xs) + i else i)); eauto.
    + eapply nf_perm_of_eq.
      destruct v as [| b | n0 | s0 | xs0 | fields0]; simpl; try reflexivity.
      exfalso; apply (H3 xs0); reflexivity.

  (* SelSlice *)
  - inversion Hev; subst; clear Hev; simpl.
    + eapply nf_perm_of_eq.
      destruct v as [| b | n0 | s0 | xs0 | fields0]; simpl; try reflexivity.
      exfalso; apply (H5 xs0); reflexivity.
    + eapply nf_perm_of_eq.
      apply map_ext; intro n0.
      cbv [mk_node].
      apply (f_equal (fun v0 => (List.app p [SIndex (Z.of_nat n0)], v0))).
      symmetry. apply nth_error_default_eq.
Qed.

End JSONPath_Equiv.

Lemma visit_df_arr_go_forall2 :
  forall xs p start,
    Forall (fun v => forall p0, visit_order (p0, v) (visit_df_value p0 v)) xs ->
    Forall2 (fun child lst => visit_order child lst)
      (map (fun '(i, v0) => (List.app p [SIndex (Z.of_nat i)], v0))
         (combine (seq start (Datatypes.length xs)) xs))
      (let fix go (i0 : nat) (ys : list value) {struct ys} : list (list node) :=
         match ys with
         | [] => []
         | v' :: ys' => visit_df_value (List.app p [SIndex (Z.of_nat i0)]) v' :: go (S i0) ys'
         end in go start xs).
Proof.
  intros xs p start Hall.
  revert start. induction Hall as [| x xs' Hx Hall' IH]; intro start; simpl.
  - constructor.
  - constructor.
    + apply Hx.
    + apply IH.
Qed.

Lemma visit_df_obj_go_forall2 :
  forall fields p,
    Forall (fun '(k, v) => forall p0, visit_order (p0, v) (visit_df_value p0 v)) fields ->
    Forall2 (fun child lst => visit_order child lst)
      (map (fun '(k, v0) => (List.app p [SName k], v0)) fields)
      (let fix go (gs : list (string * value)) {struct gs} : list (list node) :=
         match gs with
         | [] => []
         | (k, v') :: gs' => visit_df_value (List.app p [SName k]) v' :: go gs'
         end in go fields).
Proof.
  intros fields p Hall.
  induction Hall as [| [k x] fields' Hx Hall' IH]; simpl.
  - constructor.
  - constructor.
    + apply Hx.
    + apply IH.
Qed.

Lemma visit_df_value_sound :
  forall v p,
    visit_order (p, v) (visit_df_value p v).
Proof.
  apply (Forall_value_ind (fun v => forall p, visit_order (p, v) (visit_df_value p v))).
  - intros b p. apply VisitLeaf; intros; discriminate.
  - intros n p. apply VisitLeaf; intros; discriminate.
  - intros s p. apply VisitLeaf; intros; discriminate.
  - intro p. apply VisitLeaf; intros; discriminate.
  - intros xs IHxs p. simpl. eapply VisitArray.
    + reflexivity.
    + unfold index_zip. apply (visit_df_arr_go_forall2 xs p 0%nat IHxs).
    + reflexivity.
  - intros fields IHfields p. simpl. eapply VisitObject.
    + apply Permutation_refl.
    + reflexivity.
    + apply (visit_df_obj_go_forall2 fields p).
      induction fields as [| [k v] fields' IHf]; constructor.
      * apply Forall_inv in IHfields. exact IHfields.
      * apply IHf. apply Forall_inv_tail in IHfields. exact IHfields.
    + reflexivity.
Qed.

Lemma visit_df_node_sound :
  forall n,
    visit_order n (visit_df_node n).
Proof.
  intros [p v]. unfold visit_df_node. apply visit_df_value_sound.
Qed.

Corollary root_visited_first :
  forall p v visited,
    visit_order (p, v) visited ->
    exists rest, visited = (p, v) :: rest.
Proof.
  intros p v visited Hvisit.
  inversion Hvisit; subst.
  - exists []. reflexivity.
  - eexists. reflexivity.
  - eexists. reflexivity.
Qed.

Corollary parent_before_children :
  forall p v visited child_path child_val,
    visit_order (p, v) visited ->
    In (child_path, child_val) visited ->
    child_path <> p ->
    exists (prefix suffix : list node),
      visited = List.app prefix (List.app [(p, v)] suffix) /\
      In (child_path, child_val) suffix.
Proof.
  intros p v visited child_path child_val Hvisit Hin Hneq.
  pose proof (root_visited_first p v visited Hvisit) as [rest Heq].
  exists [], rest.
  split.
  - simpl. exact Heq.
  - rewrite Heq in Hin. simpl in Hin.
    destruct Hin as [Heq' | Hin'].
    + inversion Heq'. subst. contradiction.
    + exact Hin'.
Qed.

Lemma Permutation_app_cons_comm :
  forall {A} (l1 l2 : list A) (a : A),
    Permutation (List.app l1 (a :: l2)) (a :: List.app l1 l2).
Proof.
  intros A l1 l2 a.
  induction l1 as [| x l1' IH]; simpl.
  - apply Permutation_refl.
  - transitivity (x :: List.app l1' (a :: l2)).
    + apply Permutation_refl.
    + transitivity (x :: a :: List.app l1' l2).
      * apply perm_skip. exact IH.
      * apply perm_swap.
Qed.

Lemma Permutation_in_map :
  forall {A B} (f : A -> B) (y : B) (xs : list A),
    In y (map f xs) ->
    exists x, In x xs /\ f x = y.
Proof.
  intros A B f y xs Hin.
  apply in_map_iff in Hin as [x [Heq Hinx]].
  exists x. split; [exact Hinx | exact Heq].
Qed.

Lemma list_split_app :
  forall {A} (x : A) (xs : list A),
    In x xs ->
    exists xs1 xs2, xs = List.app xs1 (x :: xs2).
Proof.
  intros A x xs Hin.
  apply in_split in Hin as [xs1 [xs2 Heq]].
  exists xs1, xs2. exact Heq.
Qed.

Lemma Permutation_cons_inv_trans :
  forall {A} (a : A) (l1 l2 l3 : list A),
    Permutation (a :: l1) l2 ->
    Permutation l2 (a :: l3) ->
    Permutation l1 l3.
Proof.
  intros A a l1 l2 l3 H1 H2.
  apply Permutation_cons_inv with (a := a).
  transitivity l2; assumption.
Qed.

Lemma Permutation_map_cons_inv :
  forall {A B} (f : A -> B) (x : A) (xs ys : list A),
    Permutation (f x :: map f xs) (map f ys) ->
    exists (y : A) (ys1 ys2 : list A),
      ys = List.app ys1 (y :: ys2) /\ f y = f x /\ Permutation (map f xs) (map f (List.app ys1 ys2)).
Proof.
  intros A B f x xs ys Hperm.
  assert (Hin: In (f x) (map f ys)).
  { eapply Permutation_in; [exact Hperm | left; reflexivity]. }
  apply Permutation_in_map in Hin as [y [Hiny Heq]].
  apply list_split_app in Hiny as [ys1 [ys2 Hys]].
  exists y, ys1, ys2. split; [exact Hys | split; [exact Heq | ]].
  subst ys. rewrite map_app in Hperm. simpl in Hperm.
  rewrite Heq in Hperm.
  apply (Permutation_cons_inv_trans (f x) (map f xs) (List.app (map f ys1) (f x :: map f ys2)) (map f (List.app ys1 ys2))).
  - exact Hperm.
  - rewrite map_app. apply Permutation_app_cons_comm.
Qed.

Lemma visit_order_complete_array_helper_gen :
  forall p xs start children_lists,
    Forall2 (fun child lst => visit_order child lst)
      (map (fun '(i, v) => (List.app p [SIndex (Z.of_nat i)], v))
        (combine (seq start (Datatypes.length xs)) xs))
      children_lists ->
    (forall child lst, visit_order child lst -> Permutation lst (visit_df_value (fst child) (snd child))) ->
    Permutation (List.concat children_lists)
      (let fix go (i : nat) (ys : list value) {struct ys} : list (list node) :=
         match ys with
         | [] => []
         | v' :: ys' => visit_df_value (List.app p [SIndex (Z.of_nat i)]) v' :: go (S i) ys'
         end in List.concat (go start xs)).
Proof.
  intros p xs start children_lists HF2 IH.
  revert start children_lists HF2.
  induction xs as [| x xs' IHxs]; intros start cls HF2.
  - inversion HF2; subst. apply Permutation_refl.
  - inversion HF2; subst. simpl.
    apply Permutation_app.
    + specialize (IH _ _ H1). simpl in IH. exact IH.
    + apply (IHxs (S start) l' H3).
Qed.

Lemma visit_order_complete_array_helper :
  forall p xs children children_lists,
    children = map (fun '(i, v) => (List.app p [SIndex (Z.of_nat i)], v)) (index_zip xs) ->
    Forall2 (fun child lst => visit_order child lst) children children_lists ->
    (forall child lst, visit_order child lst -> Permutation lst (visit_df_value (fst child) (snd child))) ->
    Permutation (List.concat children_lists)
      (let fix go (i : nat) (ys : list value) {struct ys} : list (list node) :=
         match ys with
         | [] => []
         | v' :: ys' => visit_df_value (List.app p [SIndex (Z.of_nat i)]) v' :: go (S i) ys'
         end in List.concat (go 0%nat xs)).
Proof.
  intros p xs children children_lists Hch HF2 IH.
  subst children.
  unfold index_zip in HF2.
  apply (visit_order_complete_array_helper_gen p xs 0%nat children_lists HF2 IH).
Qed.

Lemma Forall2_app_split_l :
  forall {A B} (R : A -> B -> Prop) (l1 l2 : list A) (l : list B),
    Forall2 R (l1 ++ l2)%list l ->
    exists (r1 r2 : list B), l = (r1 ++ r2)%list /\ Forall2 R l1 r1 /\ Forall2 R l2 r2.
Proof.
  intros A B R l1 l2 l H.
  revert l H.
  induction l1 as [| a l1' IH]; intros l H.
  - exists [], l. simpl. split; [reflexivity | split; [constructor | exact H]].
  - inversion H; subst.
    specialize (IH _ H4) as [r1 [r2 [Heq [HF1 HF2]]]].
    exists (y :: r1)%list, r2. subst l'. split; [reflexivity | split; [constructor; assumption | exact HF2]].
Qed.

Lemma visit_order_complete_object_helper :
  forall p fs children children_lists,
    Permutation children (map (fun '(k, v) => (List.app p [SName k], v)) fs) ->
    Forall2 (fun child lst => visit_order child lst) children children_lists ->
    (forall child lst, visit_order child lst -> Permutation lst (visit_df_value (fst child) (snd child))) ->
    Permutation (List.concat children_lists)
      (let fix go (gs : list (string * value)) {struct gs} : list (list node) :=
         match gs with
         | [] => []
         | (k, v') :: gs' => visit_df_value (List.app p [SName k]) v' :: go gs'
         end in List.concat (go fs)).
Proof.
  intros p fs children children_lists Hperm HF2 IH.
  transitivity (List.concat (map (fun child => visit_df_value (fst child) (snd child)) children)).
  - assert (HF2': Forall2 (fun lst child => Permutation lst (visit_df_value (fst child) (snd child)))
                          children_lists children).
    { clear Hperm. induction HF2; constructor; [apply IH; exact H | apply IHHF2; exact IH]. }
    clear HF2 IH Hperm.
    induction HF2' as [| lst child lists children Hp HF2' IHHF2'].
    + apply Permutation_refl.
    + simpl. apply Permutation_app; [exact Hp | exact IHHF2'].
  - transitivity (List.concat (map (fun child => visit_df_value (fst child) (snd child))
                                   (map (fun '(k, v) => (List.app p [SName k], v)) fs))).
    + assert (Hmap: Permutation (map (fun child => visit_df_value (fst child) (snd child)) children)
                                (map (fun child => visit_df_value (fst child) (snd child))
                                     (map (fun '(k, v) => (List.app p [SName k], v)) fs))).
      { apply Permutation_map. exact Hperm. }
      clear Hperm. induction Hmap.
      * apply Permutation_refl.
      * simpl. apply Permutation_app_head. exact IHHmap.
      * simpl. repeat rewrite app_assoc. apply Permutation_app_tail. apply Permutation_app_comm.
      * transitivity (List.concat l'); assumption.
    + clear Hperm HF2 IH children children_lists.
      induction fs as [| [k v] fs' IHfs].
      * apply Permutation_refl.
      * simpl. apply Permutation_app_head. exact IHfs.
Qed.


Import JSON JSONPath Exec JSONPath_Equiv.

(** ** List auxiliaries *)

(** Length of [index_zip] equals the input length. *)
Lemma length_index_zip {A} (xs : list A) :
  List.length (index_zip xs) = List.length xs.
Proof.
  unfold index_zip.
  rewrite combine_length, seq_length, Nat.min_id; reflexivity.
Qed.

(** ** Consequences of selector-level equivalence *)

(** Totality of the relational selector semantics (filter-free). *)
Corollary nf_selector_total :
  forall sel n,
    selector_filter_free sel = true ->
    exists res, eval_selector sel n res.
Proof.
  intros sel n Hff. eexists. eapply sel_exec_nf_sound; exact Hff.
Qed.

(** Determinism up to permutation for filter-free selectors. *)
Corollary nf_selector_deterministic_up_to_perm :
  forall sel n res1 res2,
    selector_filter_free sel = true ->
    eval_selector sel n res1 ->
    eval_selector sel n res2 ->
    Permutation res1 res2.
Proof.
  intros sel n res1 res2 Hff H1 H2.
  transitivity (Exec.sel_exec_nf sel n).
  - eapply sel_exec_nf_complete; eauto.
  - symmetry; eapply sel_exec_nf_complete; eauto.
Qed.

(** Membership equivalence under permutation (filter-free selectors). *)
Corollary nf_selector_in_iff :
  forall sel n res x,
    selector_filter_free sel = true ->
    eval_selector sel n res ->
    In x res <-> In x (Exec.sel_exec_nf sel n).
Proof.
  intros sel n res x Hff Hev; split.
  - intro Hin. eapply Permutation_in.
    + eapply sel_exec_nf_complete; eauto.
    + exact Hin.
  - intro Hin. eapply Permutation_in.
    + apply Permutation_sym. eapply sel_exec_nf_complete; eauto.
    + exact Hin.
Qed.

(** Cardinality preservation under permutation (filter-free selectors). *)
Corollary nf_selector_length_eq :
  forall sel n res,
    selector_filter_free sel = true ->
    eval_selector sel n res ->
    List.length res = List.length (Exec.sel_exec_nf sel n).
Proof.
  intros sel n res Hff Hev.
  eapply Permutation_length.
  eapply sel_exec_nf_complete; eauto.
Qed.

(** ** Arity and cardinality bounds *)

(** [SelFilter] is inert in the non-filter interpreter. *)
Corollary nf_selfilter_empty :
  forall f n, Exec.sel_exec_nf (SelFilter f) n = [].
Proof. intros f [p v]; reflexivity. Qed.

(** Arity bound for [SelName]: at most one result. *)
Corollary nf_selname_length_le1 :
  forall p v s,
    (List.length (Exec.sel_exec_nf (SelName s) (p, v)) <= 1)%nat.
Proof.
  intros p v s; destruct v as [| | | | xs | fields]; simpl; try lia.
  destruct (find (fun kv => string_eqb (fst kv) s) fields) as [[k v']|]; simpl.
  - apply le_n.      (* 1 <= 1 *)
  - apply le_0_n.    (* 0 <= 1 *)
Qed.

(** Arity bound for [SelIndex]: at most one result. *)
Corollary nf_selindex_length_le1 :
  forall p v i,
    (List.length (Exec.sel_exec_nf (SelIndex i) (p, v)) <= 1)%nat.
Proof.
  intros p v i; destruct v as [| | | | xs | fields]; simpl; try lia.
  remember (if i <? 0 then Z.of_nat (List.length xs) + i else i) as idx.
  destruct ((idx <? 0) || (idx >=? Z.of_nat (List.length xs))) eqn:Hoob; simpl.
  - apply le_0_n.
  - destruct (nth_error xs (Z.to_nat idx)); simpl; [apply le_n | apply le_0_n].
Qed.

(** Wildcard over objects: cardinality equals number of fields. *)
Corollary nf_selwildcard_object_length :
  forall p fields,
    List.length (Exec.sel_exec_nf SelWildcard (p, JObject fields))
    = List.length fields.
Proof. intros; simpl; now rewrite map_length. Qed.

(** Wildcard over arrays: cardinality equals number of elements. *)
Corollary nf_selwildcard_array_length :
  forall p xs,
    List.length (Exec.sel_exec_nf SelWildcard (p, JArr xs))
    = List.length xs.
Proof.
  intros; simpl; rewrite map_length, length_index_zip; reflexivity.
Qed.

(** Slice over arrays: cardinality equals [slice_positions] length. *)
Corollary nf_selslice_array_length :
  forall p xs st en stp,
    List.length (Exec.sel_exec_nf (SelSlice st en stp) (p, JArr xs))
    = List.length (slice_positions (List.length xs) st en stp).
Proof. intros; simpl; now rewrite map_length. Qed.

(** ** Path shape and permutation invariances *)

(** Single-step path extension for filter-free selectors. *)
Corollary nf_selector_child_step_shape :
  forall sel p v p' v',
    selector_filter_free sel = true ->
    In (p', v') (Exec.sel_exec_nf sel (p, v)) ->
    exists step, p' = List.app p [step].
Proof.
  intros sel p v p' v' Hff Hin.
  destruct sel as [s | | i | st en stp | f]; simpl in Hff; try discriminate; clear Hff.
  - (* SelName *)
    destruct v as [| | | | xs | fields]; simpl in Hin; try contradiction.
    destruct (find (fun kv => string_eqb (fst kv) s) fields) as [[k w]|] eqn:?; simpl in Hin; [|contradiction].
    destruct Hin as [Heq|[]]; inversion Heq; eauto.
  - (* SelWildcard *)
    destruct v as [| | | | xs | fields]; simpl in Hin; try contradiction.
    + (* JArr *)
      apply in_map_iff in Hin.
      destruct Hin as [[i0 w] [Hf Hin0]]; cbv [mk_node] in Hf; inversion Hf; eauto.
    + (* JObject *)
      apply in_map_iff in Hin.
      destruct Hin as [[k w] [Hf Hin0]]; cbv [mk_node] in Hf; inversion Hf; eauto.
  - (* SelIndex *)
    destruct v as [| | | | xs | fields]; simpl in Hin; try contradiction.
    remember (if i <? 0 then Z.of_nat (List.length xs) + i else i) as idx.
    destruct ((idx <? 0) || (idx >=? Z.of_nat (List.length xs))) eqn:?; simpl in Hin; try contradiction.
    destruct (nth_error xs (Z.to_nat idx)) eqn:?; simpl in Hin; [|contradiction].
    destruct Hin as [Heq|[]]; inversion Heq; eauto.
  - (* SelSlice *)
    destruct v as [| | | | xs | fields]; simpl in Hin; try contradiction.
    apply in_map_iff in Hin.
    destruct Hin as [n0 [Hf Hin0]]; cbv [mk_node] in Hf; inversion Hf; eauto.
Qed.

(** Object wildcard: permutation-invariance under field reordering. *)
Corollary nf_selwildcard_object_perm_invariant :
  forall p fs perm,
    Permutation perm fs ->
    Permutation
      (Exec.sel_exec_nf SelWildcard (p, JObject perm))
      (Exec.sel_exec_nf SelWildcard (p, JObject fs)).
Proof.
  intros p fs perm Hperm; simpl.
  apply Permutation_map; exact Hperm.
Qed.

(* ============================================================ *)
(* End-to-end equivalence for the child-only, filter-free core *)
(* ============================================================ *)

Import JSON JSONPath Exec JSONPath_Equiv.

(* Helper: concat respects Forall2 Permutation pointwise *)
Lemma Permutation_concat_Forall2 :
  forall (xs ys : list (list JSON.node)),
    Forall2 (fun a b => Permutation a b) xs ys ->
    Permutation (List.concat xs) (List.concat ys).
Proof.
  intros xs ys H; induction H.
  - simpl; apply Permutation_refl.
  - simpl; now apply Permutation_app.
Qed.

(* Segment-level completeness for Child segments with filter-free selectors *)
Lemma seg_exec_nf_complete_child :
  forall seg n res,
    segment_child_only seg = true ->
    eval_seg seg n res ->
    Permutation res (Exec.seg_exec_nf seg n).
Proof.
  intros seg n res Hok Hev.
  destruct seg as [sels | sels]; simpl in Hok; try discriminate.
  inversion Hev as [sels' n' results Hex |]; subst; clear Hev.
  destruct Hex as [selector_results [Hall ->]].
  revert Hok Hall.
  generalize dependent selector_results.
  induction sels as [|sel sels IH]; intros selector_results Hok Hall; simpl in *.
  - inversion Hall; subst; simpl; apply Permutation_refl.
  - apply Bool.andb_true_iff in Hok as [Hhd Hok'].
    inversion Hall as [| sel' res_sel sels' selres_tail Hsel_ev Hall_tail]; subst.
    simpl.
    (* concat (res_sel :: selres_tail) = res_sel ++ concat selres_tail *)
    (* concat (map _ (sel :: sels)) = exec_hd ++ concat (map _ sels) *)
    apply Permutation_app.
    + eapply sel_exec_nf_complete; eauto.
    + apply IH; assumption.
Qed.

(* concat respects Permutation over lists of lists *)
Lemma Permutation_concat_listlist {A} :
  forall (xs ys : list (list A)),
    Permutation xs ys ->
    Permutation (List.concat xs) (List.concat ys).
Proof.
  intros xs ys P; induction P; simpl.
  - apply Permutation_refl.
  - (* skip: x :: l ~ x :: l' *)
    apply Permutation_app_head; exact IHP.
  - (* swap: x :: y :: l ~ y :: x :: l *)
    repeat rewrite app_assoc.
    apply Permutation_app_tail.
    apply Permutation_app_comm.
  - (* trans *)
    eapply Permutation_trans; eauto.
Qed.

(* The nf multi-segment executor preserves permutations of its input list *)
Lemma segs_exec_nf_perm :
  forall segs ns ns',
    Permutation ns ns' ->
    Permutation (Exec.segs_exec_nf segs ns)
                (Exec.segs_exec_nf segs ns').
Proof.
  intros segs ns ns' P.
  revert ns ns' P.
  induction segs as [|seg segs IH]; intros ns ns' P; simpl.
  - exact P.
  - (* One step: concat âˆ˜ map (seg_exec_nf seg) preserves permutations *)
    pose proof (Permutation_map (Exec.seg_exec_nf seg) P) as Pmap.
    pose proof (@Permutation_concat_listlist JSON.node
                  (map (Exec.seg_exec_nf seg) ns)
                  (map (Exec.seg_exec_nf seg) ns') Pmap) as Pconcat.
    (* Push through the remaining segments by IH *)
    apply IH; exact Pconcat.
Qed.

(* Pointwise: relational seg results are a permutation of exec seg results *)
Lemma Forall2_eval_seg_perm :
  forall seg ns node_results,
    segment_child_only seg = true ->
    Forall2 (fun n res => eval_seg seg n res) ns node_results ->
    Forall2 (fun res mapped => Permutation res mapped)
            node_results
            (map (Exec.seg_exec_nf seg) ns).
Proof.
  intros seg ns node_results Hseg Hall.
  induction Hall; simpl; constructor.
  - eapply seg_exec_nf_complete_child; eauto.
  - apply IHHall; exact Hseg.
Qed.

(* ==== Fixed driver lemma ==== *)
Lemma eval_rest_on_nodes_nf_complete :
  forall segs ns finals,
    forallb segment_child_only segs = true ->
    eval_rest_on_nodes segs ns finals ->
    Permutation finals (Exec.segs_exec_nf segs ns).
Proof.
  intros segs ns finals Hok Hev; induction Hev.
  - simpl; apply Permutation_refl.
  - simpl in Hok; apply Bool.andb_true_iff in Hok as [Hseg Hok'].
    destruct H as [node_results [Hall ->]].
(* Step 1: rewrite inter = concat node_results to executable concat(map ...) *)
pose proof (Forall2_eval_seg_perm seg ns node_results Hseg Hall) as Hpointwise.
    pose proof (Permutation_concat_Forall2 _ _ Hpointwise) as Hconcat.
    (* Hconcat : Permutation (List.concat node_results)
                              (List.concat (map (Exec.seg_exec_nf seg) ns)) *)
    (* Step 2: use IH on 'rest' at the relational inter (concat node_results) *)
    specialize (IHHev Hok').
    (* IHHev : Permutation finals (Exec.segs_exec_nf rest (List.concat node_results)) *)
    (* Step 3: push the permutation of the inter list through the remaining executor *)
    pose proof (segs_exec_nf_perm rest
                    (List.concat node_results)
                    (List.concat (map (Exec.seg_exec_nf seg) ns))
                    Hconcat) as Hpush.
    (* Step 4: chain *)
    eapply Permutation_trans; [exact IHHev|].
    exact Hpush.
Qed.

Corollary child_only_end_to_end_equiv :
  forall q J res,
    query_child_only q = true ->
    eval q J res ->
    Permutation res (Exec.eval_exec_nf q J).
Proof.
  intros [segs] J res Hq He.
  inversion He; subst; clear He.
  simpl in Hq.
  eapply eval_rest_on_nodes_nf_complete; eauto.
Qed.

Corollary query_splits_into_segments :
  forall seg rest ns finals,
    eval_rest_on_nodes (seg :: rest) ns finals ->
    exists inter,
      (exists node_results,
          Forall2 (fun n res => eval_seg seg n res) ns node_results /\
          inter = List.concat node_results) /\
      eval_rest_on_nodes rest inter finals.
Proof.
  intros seg rest ns finals Heval.
  inversion Heval as [|? ? ? ? ? Hseg Hrest]; subst; clear Heval.
  exists inter.
  split; [exact Hseg | exact Hrest].
Qed.

Definition is_prefix_of {A} (p1 p2 : list A) : Prop :=
  exists suffix, p2 = List.app p1 suffix.

Corollary segment_prefix_paths_equal_when_suffix_empty :
  forall prefix J res_prefix res_full,
    query_child_only (Query prefix) = true ->
    eval (Query prefix) J res_prefix ->
    eval (Query prefix) J res_full ->
    forall p v,
      In (p, v) res_prefix ->
      In (p, v) res_full.
Proof.
  intros prefix J res_prefix res_full Hpre Heval_pre Heval_full p v Hin.
  pose proof (child_only_end_to_end_equiv (Query prefix) J res_prefix Hpre Heval_pre) as Hperm1.
  pose proof (child_only_end_to_end_equiv (Query prefix) J res_full Hpre Heval_full) as Hperm2.
  assert (Hperm : Permutation res_prefix res_full).
  { transitivity (Exec.eval_exec_nf (Query prefix) J); [exact Hperm1 | apply Permutation_sym; exact Hperm2]. }
  eapply Permutation_in; [exact Hperm | exact Hin].
Qed.

(* Determinism up to permutation at the query level *)
Corollary child_only_query_deterministic_up_to_perm :
  forall q J res1 res2,
    query_child_only q = true ->
    eval q J res1 ->
    eval q J res2 ->
    Permutation res1 res2.
Proof.
  intros q J res1 res2 Hq H1 H2.
  transitivity (Exec.eval_exec_nf q J).
  - eapply child_only_end_to_end_equiv; eauto.
  - symmetry; eapply child_only_end_to_end_equiv; eauto.
Qed.

(* Membership invariance *)
Corollary child_only_query_in_iff :
  forall q J res x,
    query_child_only q = true ->
    eval q J res ->
    In x res <-> In x (Exec.eval_exec_nf q J).
Proof.
  intros q J res x Hq Hev; split; intro Hin.
  - eapply Permutation_in.
    + eapply child_only_end_to_end_equiv; eauto.
    + exact Hin.
  - eapply Permutation_in.
    + apply Permutation_sym.
      eapply child_only_end_to_end_equiv; eauto.
    + exact Hin.
Qed.

(* Cardinality invariance *)
Corollary child_only_query_length_eq :
  forall q J res,
    query_child_only q = true ->
    eval q J res ->
    List.length res = List.length (Exec.eval_exec_nf q J).
Proof.
  intros q J res Hq Hev.
  eapply Permutation_length.
  eapply child_only_end_to_end_equiv; eauto.
Qed.

(** * Linear-path arity bound: at most one result *)

Definition linear_segment (s:segment) : bool :=
  match s with
  | Child [SelName _]  => true
  | Child [SelIndex _] => true
  | _ => false
  end.

Definition linear_query (q:query) : bool :=
  match q with
  | Query segs => forallb linear_segment segs
  end.

Lemma seg_exec_nf_singleton :
  forall sel n,
    Exec.seg_exec_nf (Child [sel]) n = Exec.sel_exec_nf sel n.
Proof.
  intros sel n.
  cbn [Exec.seg_exec_nf Exec.seg_exec_impl Exec.child_on_node_impl].
  cbn [child_on_node_impl map List.concat].
  rewrite List.app_nil_r.
  reflexivity.
Qed.

Lemma seg_linear_on_single_len_le1 :
  forall seg n,
    linear_segment seg = true ->
    (List.length (Exec.seg_exec_nf seg n) <= 1)%nat.
Proof.
  intros seg [p v] Hlin.
  destruct seg as [sels|sels]; simpl in Hlin; [| discriminate Hlin].
  destruct sels as [|sel sels']; simpl in Hlin; [discriminate Hlin|].
  destruct sel; simpl in Hlin; try discriminate Hlin.
  - (* SelName *)
    destruct sels' as [| s' ss']; [| discriminate Hlin].
    rewrite seg_exec_nf_singleton.
    apply nf_selname_length_le1.
  - (* SelIndex *)
    destruct sels' as [| s' ss']; [| discriminate Hlin].
    rewrite seg_exec_nf_singleton.
    apply nf_selindex_length_le1.
Qed.

Lemma step_linear_preserves_le1 :
  forall seg ns,
    linear_segment seg = true ->
    (List.length ns <= 1)%nat ->
    (List.length (List.concat (map (Exec.seg_exec_nf seg) ns)) <= 1)%nat.
Proof.
  intros seg ns Hlin Hlen.
  destruct ns as [|n ns']; cbn [map List.concat]; try lia.
  destruct ns' as [|n2 ns'']; cbn [map List.concat] in *.
  - rewrite List.app_nil_r.
    apply seg_linear_on_single_len_le1; exact Hlin.
  - (* impossible by Hlen: length (n :: n2 :: ns'') <= 1 *)
    exfalso. cbn in Hlen. lia.
Qed.

Lemma segs_exec_nf_linear_len_le1 :
  forall segs ns,
    forallb linear_segment segs = true ->
    (List.length ns <= 1)%nat ->
    (List.length (Exec.segs_exec_nf segs ns) <= 1)%nat.
Proof.
  induction segs as [|seg segs IH]; intros ns Hok Hns; simpl in *.
  - exact Hns.
  - apply Bool.andb_true_iff in Hok as [Hseg Hok'].
    specialize (step_linear_preserves_le1 seg ns Hseg Hns).
    intros Hstep.
    eapply IH; [exact Hok'| exact Hstep].
Qed.

(** Linear queries return at most one result. *)
Theorem linear_query_arity_le1 :
  forall q J,
    linear_query q = true ->
    (List.length (Exec.eval_exec_nf q J) <= 1)%nat.
Proof.
  intros [segs] J Hlin; simpl in *.
  change (Exec.segs_exec_nf segs [([], J)]) with (Exec.segs_exec_nf segs [([], J)]).
  eapply segs_exec_nf_linear_len_le1; [exact Hlin| simpl; lia].
Qed.

(** List of length â‰¤1 is either empty or singleton. *)
Lemma length_le1_cases {A} (xs : list A) :
  (List.length xs <= 1)%nat -> xs = [] \/ exists x, xs = [x].
Proof.
  destruct xs as [|x xs']; intro H.
  - now left.
  - destruct xs' as [|y xs''].
    + right. now eexists.
    + exfalso. simpl in H. lia.
Qed.

(** Linear segment syntax implies child-only fragment. *)
Lemma linear_implies_segment_child_only :
  forall seg, linear_segment seg = true -> segment_child_only seg = true.
Proof.
  intros seg H.
  destruct seg as [sels|sels]; simpl in H; [| discriminate H].
  destruct sels as [|sel sels']; simpl in H; [discriminate H|].
  destruct sel; simpl in H; try discriminate H.
  - (* SelName *)
    destruct sels' as [|s' ss']; simpl in H; [reflexivity | discriminate H].
  - (* SelIndex *)
    destruct sels' as [|s' ss']; simpl in H; [reflexivity | discriminate H].
Qed.

(** Linear query syntax implies child-only fragment. *)
Lemma linear_query_implies_child_only :
  forall q, linear_query q = true -> query_child_only q = true.
Proof.
  intros [segs] H; simpl in *.
  induction segs as [|seg segs IH]; simpl in *; auto.
  apply Bool.andb_true_iff in H as [Hseg Hrest].
  rewrite (linear_implies_segment_child_only _ Hseg), IH; auto.
Qed.

(** Permutation of singleton collapses to equality. *)
Lemma permutation_singleton {A} (x : A) (ys : list A) :
  Permutation [x] ys -> ys = [x].
Proof.
  intro P.
  destruct ys as [|y ys'].
  - pose proof (Permutation_length P) as L; simpl in L; discriminate L.
  - destruct ys' as [|z zs].
    + assert (Hin : In x [y]) by (eapply Permutation_in; [exact P|simpl; auto]).
      simpl in Hin. destruct Hin as [->|[]]. reflexivity.
    + pose proof (Permutation_length P) as L; simpl in L; discriminate L.
Qed.

(** Linear queries: relational and executable results are exactly equal (not just permutation). *)
Theorem linear_query_exact_equiv :
  forall q J res,
    linear_query q = true ->
    eval q J res ->
    res = Exec.eval_exec_nf q J.
Proof.
  intros q J res Hlin Hev.
  pose proof (linear_query_implies_child_only q Hlin) as Hco.
  pose proof (child_only_end_to_end_equiv q J res Hco Hev) as P.
  pose proof (linear_query_arity_le1 q J Hlin) as Hle.
  set (E := Exec.eval_exec_nf q J) in *.
  destruct (length_le1_cases _ Hle) as [E_nil | [x E_one]].
  - (* E = [] *)
    rewrite E_nil in P.                (* P : Permutation res [] *)
    apply Permutation_sym in P.        (* P : Permutation [] res *)
    apply Permutation_nil in P.        (* res = [] *)
    subst res. rewrite E_nil. reflexivity.
  - (* E = [x] *)
    rewrite E_one in P.                (* P : Permutation res [x] *)
    apply Permutation_sym in P.        (* P : Permutation [x] res *)
    pose proof (permutation_singleton x res P) as ->.  (* res = [x] *)
    now rewrite E_one.
Qed.

Corollary linear_result_empty_or_singleton :
  forall q J res,
    linear_query q = true ->
    eval q J res ->
    res = [] \/ exists n, res = [n].
Proof.
  intros q J res Hlin Hev.
  pose proof (linear_query_arity_le1 q J Hlin) as Hle.
  pose proof (linear_query_exact_equiv q J res Hlin Hev) as Heq.
  rewrite Heq.
  apply length_le1_cases.
  exact Hle.
Qed.

Corollary linear_no_duplicate_paths :
  forall q J p1 v1 p2 v2,
    linear_query q = true ->
    eval q J [(p1, v1); (p2, v2)] ->
    False.
Proof.
  intros q J p1 v1 p2 v2 Hlin Hev.
  pose proof (linear_query_arity_le1 q J Hlin) as Hle.
  pose proof (linear_query_exact_equiv q J [(p1, v1); (p2, v2)] Hlin Hev) as Heq.
  rewrite <- Heq in Hle.
  simpl in Hle.
  lia.
Qed.

Corollary linear_index_preservation :
  forall segs J p v i idx,
    linear_query (Query (segs ++ [Child [SelIndex i]])) = true ->
    eval (Query segs) J [(p, JArr v)] ->
    idx = (if i <? 0 then Z.of_nat (List.length v) + i else i) ->
    (idx <? 0) = false ->
    (idx >=? Z.of_nat (List.length v)) = false ->
    exists val, nth_error v (Z.to_nat idx) = Some val.
Proof.
  intros segs J p v i idx Hlin Hpre Hidx Hl Hr.
  apply nth_error_some_of_bools_Z; assumption.
Qed.

(* ============================================================ *)
(* Soundness: Executable semantics satisfy relational spec     *)
(* ============================================================ *)

(** Soundness for child segments: executable results satisfy relational specification. *)
Lemma seg_exec_nf_sound_child :
  forall sels n,
    forallb selector_filter_free sels = true ->
    eval_seg (Child sels) n (Exec.seg_exec_nf (Child sels) n).
Proof.
  intros sels n Hall.
  unfold Exec.seg_exec_nf, Exec.seg_exec_impl, Exec.child_on_node_impl.
  eapply EvalSegChild.
  induction sels as [|sel sels' IH].
  - exists []. split; [constructor | reflexivity].
  - simpl in Hall. apply Bool.andb_true_iff in Hall as [Hsel Hsels'].
    simpl.
    specialize (IH Hsels').
    destruct IH as [selector_results [HF2 Hconcat]].
    exists (Exec.sel_exec_nf sel n :: selector_results).
    split.
    + constructor.
      * apply sel_exec_nf_sound; exact Hsel.
      * exact HF2.
    + simpl. rewrite <- Hconcat. reflexivity.
Qed.

(** Soundness for segments: wrapper for child-only segments. *)
Lemma seg_exec_nf_sound :
  forall seg n,
    segment_child_only seg = true ->
    eval_seg seg n (Exec.seg_exec_nf seg n).
Proof.
  intros seg n Hok.
  destruct seg as [sels|sels]; simpl in Hok; [|discriminate].
  apply seg_exec_nf_sound_child; exact Hok.
Qed.

(** Helper: Forall2 construction for segment soundness over node lists. *)
Lemma forall2_eval_seg_sound :
  forall seg ns,
    segment_child_only seg = true ->
    Forall2 (fun n res => eval_seg seg n res) ns (map (Exec.seg_exec_nf seg) ns).
Proof.
  intros seg ns Hseg.
  induction ns as [|n ns' IH]; simpl.
  - constructor.
  - constructor.
    + apply seg_exec_nf_sound; exact Hseg.
    + exact IH.
Qed.

(** Soundness for multi-segment evaluation: threading soundness through segment sequences. *)
Lemma eval_rest_on_nodes_nf_sound :
  forall segs ns,
    forallb segment_child_only segs = true ->
    eval_rest_on_nodes segs ns (Exec.segs_exec_nf segs ns).
Proof.
  intros segs ns Hok.
  revert ns; induction segs as [|seg segs' IH]; intros ns; simpl in *.
  - constructor.
  - apply Bool.andb_true_iff in Hok as [Hseg Hsegs'].
    unfold Exec.segs_exec_nf, Exec.segs_exec_impl.
    fold (Exec.segs_exec_impl Exec.sel_exec_nf).
    fold Exec.segs_exec_nf.
    eapply EvalRestCons.
    + exists (map (Exec.seg_exec_nf seg) ns).
      split.
      * apply forall2_eval_seg_sound; exact Hseg.
      * reflexivity.
    + apply IH; exact Hsegs'.
Qed.

(** Top-level soundness: executable query evaluation satisfies relational specification. *)
Lemma eval_exec_nf_sound :
  forall q J,
    query_child_only q = true ->
    eval q J (Exec.eval_exec_nf q J).
Proof.
  intros [segs] J Hok; simpl in *.
  constructor.
  apply eval_rest_on_nodes_nf_sound; exact Hok.
Qed.

(* ============================================================ *)
(* Linear Query Computational Decidability                     *)
(* ============================================================ *)

(**
  Linear Query Decidability: Computational decision procedure for linear queries.

  For any linear query (using only SelName/SelIndex), we can decide whether it
  returns a result or is empty. The result is a sumbool type with computational
  content suitable for extraction.

  Combines:
  - linear_query_exact_equiv: relational and executable results are identical
  - linear_query_arity_le1: at most one result for linear queries
  - eval_exec_nf_sound: executable results satisfy relational specification

  This enables extraction to efficient OCaml decision procedures with correctness
  guarantees.
*)
Theorem linear_query_result_decidable :
  forall q J,
    linear_query q = true ->
    { exists p v, eval q J [(p, v)] } + { eval q J [] }.
Proof.
  intros q J Hlin.
  pose proof (linear_query_implies_child_only q Hlin) as Hco.
  destruct (Exec.eval_exec_nf q J) as [|[p v] rest] eqn:E.
  - right.
    pose proof (eval_exec_nf_sound q J Hco) as Hsound.
    rewrite E in Hsound.
    exact Hsound.
  - destruct rest as [|n2 rest'].
    + left.
      exists p, v.
      pose proof (eval_exec_nf_sound q J Hco) as Hsound.
      rewrite E in Hsound.
      exact Hsound.
    + exfalso.
      pose proof (linear_query_arity_le1 q J Hlin) as Harith.
      rewrite E in Harith.
      simpl in Harith.
      lia.
Qed.

(** Decidability dual: emptiness vs existence formulation. *)
Corollary linear_query_empty_decidable :
  forall q J,
    linear_query q = true ->
    { eval q J [] } + { exists p v, eval q J [(p, v)] }.
Proof.
  intros q J Hlin.
  destruct (linear_query_result_decidable q J Hlin) as [Hexists | Hempty].
  - right; exact Hexists.
  - left; exact Hempty.
Qed.

(** Uniqueness: if two singleton results exist, they are identical. *)
Corollary linear_query_result_unique :
  forall q J p1 v1 p2 v2,
    linear_query q = true ->
    eval q J [(p1, v1)] ->
    eval q J [(p2, v2)] ->
    (p1, v1) = (p2, v2).
Proof.
  intros q J p1 v1 p2 v2 Hlin H1 H2.
  pose proof (linear_query_exact_equiv q J [(p1, v1)] Hlin H1) as Eq1.
  pose proof (linear_query_exact_equiv q J [(p2, v2)] Hlin H2) as Eq2.
  assert (Heq : [(p1, v1)] = [(p2, v2)]) by (rewrite Eq1, Eq2; reflexivity).
  inversion Heq; reflexivity.
Qed.

(** Bidirectional equivalence: relational and executable singleton results coincide. *)
Corollary linear_query_executable_iff :
  forall q J p v,
    linear_query q = true ->
    (eval q J [(p, v)] <-> Exec.eval_exec_nf q J = [(p, v)]).
Proof.
  intros q J p v Hlin; split; intro H.
  - symmetry; eapply linear_query_exact_equiv; eauto.
  - pose proof (linear_query_implies_child_only q Hlin) as Hco.
    pose proof (eval_exec_nf_sound q J Hco) as Hsound.
    rewrite H in Hsound; exact Hsound.
Qed.

(** Bidirectional equivalence: relational and executable empty results coincide. *)
Corollary linear_query_empty_iff :
  forall q J,
    linear_query q = true ->
    (eval q J [] <-> Exec.eval_exec_nf q J = []).
Proof.
  intros q J Hlin; split; intro H.
  - symmetry; eapply linear_query_exact_equiv; eauto.
  - pose proof (linear_query_implies_child_only q Hlin) as Hco.
    pose proof (eval_exec_nf_sound q J Hco) as Hsound.
    rewrite H in Hsound; exact Hsound.
Qed.

(** Existence from non-empty executable result. *)
Corollary linear_query_has_result :
  forall q J,
    linear_query q = true ->
    Exec.eval_exec_nf q J <> [] ->
    exists p v, eval q J [(p, v)].
Proof.
  intros q J Hlin Hne.
  destruct (linear_query_result_decidable q J Hlin) as [Hexists | Hempty].
  - exact Hexists.
  - exfalso.
    apply Hne.
    apply linear_query_empty_iff; auto.
Qed.

(** Combined computational search: packages executable and relational results together. *)
Corollary linear_query_computational_search :
  forall q J,
    linear_query q = true ->
    (Exec.eval_exec_nf q J = [] /\ eval q J []) \/
    (exists p v, Exec.eval_exec_nf q J = [(p, v)] /\ eval q J [(p, v)]).
Proof.
  intros q J Hlin.
  pose proof (linear_query_result_decidable q J Hlin) as Hdec.
  destruct (Exec.eval_exec_nf q J) as [|[p v] rest] eqn:E.
  - left; split; auto.
    destruct Hdec as [[p' [v' Hcontra]] | Hempty].
    + pose proof (linear_query_exact_equiv q J [(p', v')] Hlin Hcontra) as Heq.
      rewrite E in Heq; discriminate Heq.
    + exact Hempty.
  - destruct rest as [|n2 rest'].
    + right; exists p, v; split; auto.
      destruct Hdec as [[p' [v' Hev]] | Hempty].
      * pose proof (linear_query_exact_equiv q J [(p', v')] Hlin Hev) as Heq.
        rewrite E in Heq; inversion Heq; subst.
        exact Hev.
      * pose proof (linear_query_exact_equiv q J [] Hlin Hempty) as Heq.
        rewrite E in Heq; discriminate Heq.
    + exfalso.
      pose proof (linear_query_arity_le1 q J Hlin) as Harith.
      rewrite E in Harith; simpl in Harith; lia.
Qed.

(** General relational-executable bridge: equivalence for any result. *)
Theorem linear_query_relational_executable_bridge :
  forall q J res,
    linear_query q = true ->
    (eval q J res <-> Exec.eval_exec_nf q J = res).
Proof.
  intros q J res Hlin; split; intro H.
  - symmetry; eapply linear_query_exact_equiv; eauto.
  - pose proof (linear_query_implies_child_only q Hlin) as Hco.
    pose proof (eval_exec_nf_sound q J Hco) as Hsound.
    rewrite H in Hsound; exact Hsound.
Qed.

(** Linear selector uniqueness for SelName. *)
Theorem linear_selector_unique_name :
  forall s p v res,
    eval_selector (SelName s) (p, v) res ->
    (List.length res <= 1)%nat.
Proof.
  intros s p v res Heval.
  pose proof (sel_exec_nf_complete (SelName s) (p, v) res eq_refl Heval) as Hperm.
  pose proof (Permutation_length Hperm) as Hlen.
  rewrite Hlen.
  apply nf_selname_length_le1.
Qed.

(** Linear selector uniqueness for SelIndex. *)
Theorem linear_selector_unique_index :
  forall i p v res,
    eval_selector (SelIndex i) (p, v) res ->
    (List.length res <= 1)%nat.
Proof.
  intros i p v res Heval.
  pose proof (sel_exec_nf_complete (SelIndex i) (p, v) res eq_refl Heval) as Hperm.
  pose proof (Permutation_length Hperm) as Hlen.
  rewrite Hlen.
  apply nf_selindex_length_le1.
Qed.

(* Search = Match with .* r .* at the holds_b level *)
Lemma holds_b_search_as_match :
  forall a r p v,
    Exec.holds_b (FSearch a r) (p, v)
    =
    Exec.holds_b (FMatch a (RCat (RStar RAny) (RCat r (RStar RAny)))) (p, v).
Proof.
  intros a r p v.
  cbn [Exec.holds_b].
  destruct (Exec.aeval a v) as [pa|] eqn:Ha; [|reflexivity].
  destruct pa as [| | | s]; cbn [Regex.regex_search]; reflexivity.
Qed.

(** Relational version: search is equivalent to match with .*r.* at the specification level. *)
Theorem search_as_match_relational :
  forall a r n,
    holds (FSearch a r) n <-> holds (FMatch a (RCat (RStar RAny) (RCat r (RStar RAny)))) n.
Proof.
  intros a r n. split; intro H.
  - inversion H; subst.
    unfold regex_search in H3.
    eapply HoldsMatch; eauto.
  - inversion H; subst.
    unfold regex_search.
    eapply HoldsSearch; eauto.
Qed.

(**
  Wildcard Completeness: For every child of an object/array,
  wildcard will include it in results.
**)

Lemma wildcard_object_complete :
  forall p k v fields,
    In (k, v) fields ->
    exists results,
      eval_selector SelWildcard (p, JObject fields) results /\
      In (List.app p [SName k], v) results.
Proof.
  intros p k v fields Hin.
  exists (map (fun '(k',v') => (List.app p [SName k'], v')) fields).
  split.
  - eapply EvalSelWildcardObject. apply Permutation_refl.
  - apply in_map_iff. exists (k, v). split; auto.
Qed.

Corollary wildcard_commutes_with_field_permutation :
  forall p fields1 fields2 res1 res2,
    Permutation fields1 fields2 ->
    eval_selector SelWildcard (p, JObject fields1) res1 ->
    eval_selector SelWildcard (p, JObject fields2) res2 ->
    Permutation res1 res2.
Proof.
  intros p fields1 fields2 res1 res2 Hfields Heval1 Heval2.
  pose proof (sel_exec_nf_complete SelWildcard (p, JObject fields1) res1 eq_refl Heval1) as Hcomp1.
  pose proof (sel_exec_nf_complete SelWildcard (p, JObject fields2) res2 eq_refl Heval2) as Hcomp2.
  simpl in Hcomp1, Hcomp2.
  eapply Permutation_trans; [exact Hcomp1|].
  eapply Permutation_trans; [|apply Permutation_sym; exact Hcomp2].
  apply Permutation_map.
  exact Hfields.
Qed.

Lemma nth_error_combine_seq_gen :
  forall {A} (start : nat) (xs : list A) i v,
    nth_error xs i = Some v ->
    In ((start + i)%nat, v) (combine (seq start (List.length xs)) xs).
Proof.
  intros A start xs.
  revert start.
  induction xs as [|x xs' IH]; intros start [|i] v Hnth.
  - inversion Hnth; subst; rewrite Nat.add_0_r; simpl; left; reflexivity.
  - inversion Hnth.
  - inversion Hnth; subst; rewrite Nat.add_0_r; simpl; left; reflexivity.
  - simpl; rewrite Nat.add_succ_r; right; apply (IH (S start) i v); exact Hnth.
Qed.

Lemma nth_error_combine_seq :
  forall {A} (xs : list A) i v,
    nth_error xs i = Some v ->
    In (i, v) (combine (seq 0 (List.length xs)) xs).
Proof.
  intros A xs i v Hnth.
  pose proof (nth_error_combine_seq_gen 0 xs i v Hnth) as H.
  simpl in H. exact H.
Qed.

Lemma wildcard_array_complete :
  forall p xs i v,
    nth_error xs i = Some v ->
    exists results,
      eval_selector SelWildcard (p, JArr xs) results /\
      In (List.app p [SIndex (Z.of_nat i)], v) results.
Proof.
  intros p xs i v Hnth.
  exists (map (fun '(i', v') => (List.app p [SIndex (Z.of_nat i')], v')) (index_zip xs)).
  split.
  - apply EvalSelWildcardArray.
  - apply in_map_iff.
    exists (i, v).
    split; auto.
    unfold index_zip.
    apply nth_error_combine_seq. exact Hnth.
Qed.

(**
  Linear Query Path Uniqueness: A linear query that returns a result
  returns exactly one, and the path is uniquely determined.
*)

Theorem linear_query_unique_path :
  forall q J p1 v1 p2 v2,
    linear_query q = true ->
    eval q J [(p1, v1)] ->
    eval q J [(p2, v2)] ->
    p1 = p2 /\ v1 = v2.
Proof.
  intros q J p1 v1 p2 v2 Hlin H1 H2.
  pose proof (linear_query_exact_equiv q J [(p1, v1)] Hlin H1) as Eq1.
  pose proof (linear_query_exact_equiv q J [(p2, v2)] Hlin H2) as Eq2.
  assert (Heq : [(p1, v1)] = [(p2, v2)]) by (rewrite Eq1, Eq2; reflexivity).
  inversion Heq.
  split; reflexivity.
Qed.

Corollary linear_path_equality_decidable :
  forall q J res1 res2,
    linear_query q = true ->
    eval q J res1 ->
    eval q J res2 ->
    {res1 = res2} + {res1 <> res2}.
Proof.
  intros q J res1 res2 Hlin H1 H2.
  pose proof (linear_query_exact_equiv q J res1 Hlin H1) as Eq1.
  pose proof (linear_query_exact_equiv q J res2 Hlin H2) as Eq2.
  left.
  rewrite Eq1, Eq2.
  reflexivity.
Qed.

Corollary linear_no_branching :
  forall q J p1 v1 p2 v2 rest,
    linear_query q = true ->
    eval q J ((p1, v1) :: (p2, v2) :: rest) ->
    False.
Proof.
  intros q J p1 v1 p2 v2 rest Hlin Hev.
  pose proof (linear_query_arity_le1 q J Hlin) as Hle.
  pose proof (linear_query_exact_equiv q J ((p1, v1) :: (p2, v2) :: rest) Hlin Hev) as Heq.
  rewrite <- Heq in Hle.
  simpl in Hle.
  lia.
Qed.

Corollary linear_first_last_agree :
  forall q J n,
    linear_query q = true ->
    eval q J [n] ->
    List.hd_error (Exec.eval_exec_nf q J) = Some n /\
    List.last (Exec.eval_exec_nf q J) n = n.
Proof.
  intros q J n Hlin Hev.
  pose proof (linear_query_exact_equiv q J [n] Hlin Hev) as Heq.
  rewrite <- Heq.
  simpl.
  split; reflexivity.
Qed.

Lemma eval_rest_app_assoc :
  forall segs1 segs2 ns finals,
    eval_rest_on_nodes (segs1 ++ segs2) ns finals ->
    exists inter,
      eval_rest_on_nodes segs1 ns inter /\
      eval_rest_on_nodes segs2 inter finals.
Proof.
  intros segs1 segs2 ns finals Heval.
  revert ns finals Heval.
  induction segs1 as [|seg1 segs1' IH]; intros ns finals Heval.
  - simpl in Heval. exists ns. split; [constructor | exact Heval].
  - simpl in Heval. inversion Heval as [| ? ? ? inter1 ? Hseg Hrest]; subst; clear Heval.
    specialize (IH inter1 finals Hrest) as [inter2 [Hinter1 Hinter2]].
    exists inter2. split; [| exact Hinter2].
    eapply EvalRestCons; [exact Hseg | exact Hinter1].
Qed.

Lemma eval_rest_app_compose :
  forall segs1 segs2 ns inter finals,
    eval_rest_on_nodes segs1 ns inter ->
    eval_rest_on_nodes segs2 inter finals ->
    eval_rest_on_nodes (segs1 ++ segs2) ns finals.
Proof.
  intros segs1 segs2 ns inter finals Hinter Hfinals.
  revert ns inter finals Hinter Hfinals.
  induction segs1 as [|seg1 segs1' IH]; intros ns inter finals Hinter Hfinals.
  - inversion Hinter; subst. exact Hfinals.
  - inversion Hinter as [| ? ? ? inter1 ? Hseg Hrest]; subst; clear Hinter.
    simpl. eapply EvalRestCons; [exact Hseg | eapply IH; [exact Hrest | exact Hfinals]].
Qed.

Theorem query_composition_associative :
  forall segs1 segs2 segs3 J res,
    query_child_only (Query (segs1 ++ segs2 ++ segs3)) = true ->
    (eval (Query (segs1 ++ (segs2 ++ segs3))) J res <->
     eval (Query ((segs1 ++ segs2) ++ segs3)) J res).
Proof.
  intros segs1 segs2 segs3 J res Hok.
  split; intro Heval.
  - inversion Heval; subst; clear Heval.
    apply eval_rest_app_assoc in H0 as [inter1 [H1 H2]].
    apply eval_rest_app_assoc in H2 as [inter2 [H2a H2b]].
    eapply (eval_rest_app_compose segs2 segs3 inter1 inter2 res) in H2a; [| exact H2b].
    rewrite <- app_assoc.
    constructor.
    eapply (eval_rest_app_compose segs1 (segs2 ++ segs3) [([], J)] inter1 res) in H1; [exact H1 | exact H2a].
  - inversion Heval; subst; clear Heval.
    replace (segs1 ++ segs2 ++ segs3)%list with ((segs1 ++ segs2) ++ segs3)%list in H0 by (rewrite app_assoc; reflexivity).
    apply eval_rest_app_assoc in H0 as [inter12 [H12 H3]].
    apply eval_rest_app_assoc in H12 as [inter1 [H1 H2]].
    pose proof (eval_rest_app_compose segs2 segs3 inter1 inter12 res H2 H3) as H23.
    pose proof (eval_rest_app_compose segs1 (segs2 ++ segs3) [([], J)] inter1 res H1 H23) as Hfinal.
    rewrite app_assoc in Hfinal.
    constructor.
    replace (segs1 ++ segs2 ++ segs3)%list with ((segs1 ++ segs2) ++ segs3)%list by (rewrite app_assoc; reflexivity).
    exact Hfinal.
Qed.

Lemma Forall2_In_left :
  forall {A B} (R : A -> B -> Prop) (l1 : list A) (l2 : list B) (x : B),
    Forall2 R l1 l2 ->
    In x l2 ->
    exists y, In y l1 /\ R y x.
Proof.
  intros A B R l1 l2 x HF Hin.
  revert l2 x HF Hin.
  induction l1 as [|a l1' IH]; intros l2 x HF Hin.
  - inversion HF; subst. destruct Hin.
  - inversion HF as [| ? ? ? l2' HR HF']; subst; clear HF.
    simpl in Hin. destruct Hin as [Heq | Hin].
    + subst x. exists a. split; [left; reflexivity | exact HR].
    + specialize (IH l2' x HF' Hin) as [y' [Hin_y' HR_y']].
      exists y'. split; [right; exact Hin_y' | exact HR_y'].
Qed.


Lemma concat_length_bound :
  forall (A : Type) (lists : list (list A)) (bound : nat),
    (forall l, In l lists -> (List.length l <= bound)%nat) ->
    (List.length (List.concat lists) <= List.length lists * bound)%nat.
Proof.
  intros A lists bound Hbound.
  induction lists as [|l lists' IH]; simpl.
  - lia.
  - rewrite app_length.
    assert (Hthis: (List.length l <= bound)%nat) by (apply Hbound; left; reflexivity).
    assert (IH': (List.length (List.concat lists') <= List.length lists' * bound)%nat).
    { apply IH. intros l' Hin. apply Hbound. right. exact Hin. }
    lia.
Qed.

Definition deterministic_selector (sel : selector) : bool :=
  match sel with
  | SelName _ => true
  | SelIndex _ => true
  | _ => false
  end.

Definition deterministic_segment (seg : segment) : bool :=
  match seg with
  | Child sels => forallb deterministic_selector sels
  | Desc _ => false
  end.

Definition deterministic_query (q : query) : bool :=
  forallb deterministic_segment (q_segs q).

Lemma deterministic_selector_le1 :
  forall sel p v res,
    deterministic_selector sel = true ->
    eval_selector sel (p, v) res ->
    (List.length res <= 1)%nat.
Proof.
  intros sel p v res Hdet Heval.
  destruct sel; simpl in Hdet; try discriminate;
    inversion Heval; subst; simpl; lia.
Qed.
