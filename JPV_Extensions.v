From Coq Require Import Init.Prelude.
From Coq Require Import
  List String Ascii ZArith Arith Lia Bool
  Sorting.Permutation QArith QArith_base.

Require Export JPV_Formalization.

Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(* ------------------------------------------------------------ *)
(* Unicode Representation Layer                                 *)
(* ------------------------------------------------------------ *)

Module Unicode.

Definition codepoint := Z.
Definition ustring := list codepoint.

Definition max_codepoint : Z := 1114111. (* 0x10FFFF *)
Definition surrogate_lo : Z := 55296.    (* 0xD800 *)
Definition surrogate_hi : Z := 57343.    (* 0xDFFF *)

Definition codepoint_valid (cp:codepoint) : bool :=
  ((0 <=? cp) && (cp <=? max_codepoint)) &&
  negb ((surrogate_lo <=? cp) && (cp <=? surrogate_hi)).

Definition codepoint_eqb (a b:codepoint) : bool := Z.eqb a b.
Definition codepoint_ltb (a b:codepoint) : bool := Z.ltb a b.
Definition codepoint_leb (a b:codepoint) : bool := negb (codepoint_ltb b a).

Fixpoint ustring_eqb (u1 u2:ustring) : bool :=
  match u1, u2 with
  | [], [] => true
  | x1::r1, x2::r2 => andb (codepoint_eqb x1 x2) (ustring_eqb r1 r2)
  | _, _ => false
  end.

Fixpoint ustring_ltb (u1 u2:ustring) : bool :=
  match u1, u2 with
  | [], [] => false
  | [], _ => true
  | _, [] => false
  | x1::r1, x2::r2 =>
      if codepoint_ltb x1 x2 then true
      else if codepoint_eqb x1 x2 then ustring_ltb r1 r2
      else false
  end.

Definition ustring_leb (u1 u2:ustring) : bool :=
  orb (ustring_eqb u1 u2) (ustring_ltb u1 u2).

Definition ascii_to_codepoint (a:ascii) : codepoint :=
  Z.of_nat (nat_of_ascii a).

Definition ustring_validb (u:ustring) : bool :=
  forallb codepoint_valid u.

Definition valid_ustring (u:ustring) : Prop :=
  Forall (fun cp => codepoint_valid cp = true) u.

Lemma ustring_validb_sound :
  forall u,
    ustring_validb u = true ->
    valid_ustring u.
Proof.
  induction u as [|cp u IHu]; intro H; simpl in *.
  - constructor.
  - apply andb_true_iff in H as [Hcp Hu].
    constructor.
    + exact Hcp.
    + apply IHu. exact Hu.
Qed.

Lemma ascii_codepoint_valid :
  forall a, codepoint_valid (ascii_to_codepoint a) = true.
Proof.
  intro a.
  unfold codepoint_valid, ascii_to_codepoint.
  assert (HnZ : (Z.of_nat (nat_of_ascii a) <= 255)%Z).
  { pose proof (nat_ascii_bounded a) as Hn.
    apply Nat2Z.inj_lt in Hn.
    lia. }
  assert (Hsur : ((surrogate_lo <=? Z.of_nat (nat_of_ascii a)) &&
                  (Z.of_nat (nat_of_ascii a) <=? surrogate_hi)) = false).
  { apply andb_false_iff.
    left.
    apply Z.leb_gt.
    unfold surrogate_lo in *.
    lia. }
  apply andb_true_iff; split.
  - apply andb_true_iff; split.
    + apply Z.leb_le. lia.
    + apply Z.leb_le. unfold max_codepoint. lia.
  - rewrite Hsur. reflexivity.
Qed.

Fixpoint string_to_ustring (s:string) : ustring :=
  match s with
  | EmptyString => []
  | String a s' => ascii_to_codepoint a :: string_to_ustring s'
  end.

Fixpoint ustring_to_ascii_string (u:ustring) : string :=
  match u with
  | [] => EmptyString
  | cp::u' => String (ascii_of_nat (Z.to_nat cp)) (ustring_to_ascii_string u')
  end.

Theorem ascii_roundtrip :
  forall s,
    ustring_to_ascii_string (string_to_ustring s) = s.
Proof.
  induction s as [|a s IH]; simpl.
  - reflexivity.
  - rewrite IH. unfold ascii_to_codepoint.
    rewrite Nat2Z.id.
    rewrite ascii_nat_embedding.
    reflexivity.
Qed.

Theorem string_to_ustring_valid :
  forall s,
    valid_ustring (string_to_ustring s).
Proof.
  induction s as [|a s IH]; simpl.
  - constructor.
  - constructor.
    + apply ascii_codepoint_valid.
    + exact IH.
Qed.

Record vustring := {
  vun_data : ustring;
  vun_valid : valid_ustring vun_data
}.

Definition mk_vustring (u:ustring) : option vustring :=
  match ustring_validb u as b return (ustring_validb u = b -> option vustring) with
  | true =>
      fun Hvalid =>
        Some {| vun_data := u; vun_valid := ustring_validb_sound u Hvalid |}
  | false => fun _ => None
  end eq_refl.

Definition ascii_vustring (s:string) : vustring :=
  {| vun_data := string_to_ustring s;
     vun_valid := string_to_ustring_valid s |}.

Definition codepoint_ascii_compatible (cp:codepoint) : bool :=
  (0 <=? cp) && (cp <=? 255).

Definition codepoint_to_ascii_opt (cp:codepoint) : option ascii :=
  if codepoint_ascii_compatible cp
  then Some (ascii_of_nat (Z.to_nat cp))
  else None.

Fixpoint ustring_to_ascii_opt (u:ustring) : option string :=
  match u with
  | [] => Some EmptyString
  | cp::u' =>
      match codepoint_to_ascii_opt cp, ustring_to_ascii_opt u' with
      | Some a, Some s' => Some (String a s')
      | _, _ => None
      end
  end.

Lemma codepoint_ascii_compatible_spec :
  forall cp,
    codepoint_ascii_compatible cp = true <->
    (0 <= cp <= 255)%Z.
Proof.
  intro cp.
  unfold codepoint_ascii_compatible.
  split.
  - intro H.
    apply andb_true_iff in H as [Hlo Hhi].
    apply Z.leb_le in Hlo.
    apply Z.leb_le in Hhi.
    lia.
  - intro H.
    apply andb_true_iff.
    split.
    + apply Z.leb_le. lia.
    + apply Z.leb_le. lia.
Qed.

Lemma codepoint_to_ascii_opt_of_ascii :
  forall a,
    codepoint_to_ascii_opt (ascii_to_codepoint a) = Some a.
Proof.
  intro a.
  unfold codepoint_to_ascii_opt, codepoint_ascii_compatible, ascii_to_codepoint.
  assert (Hlo : (0 <=? Z.of_nat (nat_of_ascii a)) = true).
  { apply Z.leb_le. apply Zle_0_nat. }
  assert (Hhi : (Z.of_nat (nat_of_ascii a) <=? 255) = true).
  { apply Z.leb_le.
    pose proof (nat_ascii_bounded a) as Hn.
    apply Nat2Z.inj_lt in Hn.
    lia. }
  rewrite Hlo, Hhi.
  simpl.
  rewrite Nat2Z.id.
  rewrite ascii_nat_embedding.
  reflexivity.
Qed.

Lemma codepoint_to_ascii_opt_sound :
  forall cp a,
    codepoint_to_ascii_opt cp = Some a ->
    ascii_to_codepoint a = cp.
Proof.
  intros cp a H.
  unfold codepoint_to_ascii_opt, codepoint_ascii_compatible in H.
  destruct ((0 <=? cp) && (cp <=? 255)) eqn:Hok; try discriminate.
  inversion H; subst a; clear H.
  apply andb_true_iff in Hok as [Hlo Hhi].
  apply Z.leb_le in Hlo.
  apply Z.leb_le in Hhi.
  unfold ascii_to_codepoint.
  rewrite nat_ascii_embedding.
  - rewrite Z2Nat.id by lia.
    reflexivity.
  - change 256%nat with (Z.to_nat 256).
    assert (Hiff : (cp < 256 <-> (Z.to_nat cp < Z.to_nat 256)%nat)).
    { apply Z2Nat.inj_lt; lia. }
    apply (proj1 Hiff).
    lia.
Qed.

Theorem ascii_partial_roundtrip :
  forall s,
    ustring_to_ascii_opt (string_to_ustring s) = Some s.
Proof.
  induction s as [|a s IH]; simpl.
  - reflexivity.
  - rewrite codepoint_to_ascii_opt_of_ascii.
    rewrite IH.
    reflexivity.
Qed.

Theorem ustring_to_ascii_opt_sound :
  forall u s,
    ustring_to_ascii_opt u = Some s ->
    string_to_ustring s = u.
Proof.
  induction u as [|cp u IHu]; intros s H; simpl in H.
  - inversion H. reflexivity.
  - destruct (codepoint_to_ascii_opt cp) as [a|] eqn:Hcp; try discriminate.
    destruct (ustring_to_ascii_opt u) as [s'|] eqn:Hrest; try discriminate.
    inversion H; subst s; clear H.
    apply codepoint_to_ascii_opt_sound in Hcp.
    specialize (IHu s' eq_refl).
    simpl.
    rewrite Hcp, IHu.
    reflexivity.
Qed.

Corollary ustring_to_ascii_opt_simulates_total :
  forall u s,
    ustring_to_ascii_opt u = Some s ->
    ustring_to_ascii_string u = s.
Proof.
  intros u s H.
  pose proof (ustring_to_ascii_opt_sound u s H) as Hu.
  rewrite <- Hu.
  apply ascii_roundtrip.
Qed.

Definition ascii_compatible_ustring (u:ustring) : Prop :=
  Forall (fun cp => codepoint_ascii_compatible cp = true) u.

Lemma codepoint_to_ascii_opt_some_iff :
  forall cp,
    (exists a, codepoint_to_ascii_opt cp = Some a) <->
    codepoint_ascii_compatible cp = true.
Proof.
  intro cp.
  unfold codepoint_to_ascii_opt.
  destruct (codepoint_ascii_compatible cp) eqn:Hc.
  - split.
    + intro H. reflexivity.
    + intro H. exists (ascii_of_nat (Z.to_nat cp)). reflexivity.
  - split.
    + intros [a Ha]. discriminate Ha.
    + intro H. discriminate H.
Qed.

Theorem ustring_to_ascii_opt_some_iff :
  forall u,
    (exists s, ustring_to_ascii_opt u = Some s) <->
    ascii_compatible_ustring u.
Proof.
  induction u as [|cp u IHu]; simpl.
  - split.
    + intro H. constructor.
    + intro H. exists EmptyString. reflexivity.
  - split.
    + intros [s Hs].
      destruct (codepoint_to_ascii_opt cp) as [a|] eqn:Hcp; try discriminate.
      destruct (ustring_to_ascii_opt u) as [s'|] eqn:Hu; try discriminate.
      inversion Hs; subst s; clear Hs.
      constructor.
      * apply (proj1 (codepoint_to_ascii_opt_some_iff cp)).
        exists a. exact Hcp.
      * apply (proj1 IHu).
        exists s'. reflexivity.
    + intro Hvalid.
      inversion Hvalid as [|cp' u' Hcp Huvalid]; subst.
      pose proof (proj2 (codepoint_to_ascii_opt_some_iff cp) Hcp) as [a Ha].
      pose proof (proj2 IHu Huvalid) as [s' Hs'].
      rewrite Ha, Hs'.
      exists (String a s').
      reflexivity.
Qed.

Corollary ustring_to_ascii_opt_fails_when_not_ascii_compatible :
  forall u,
    (exists cp, In cp u /\ codepoint_ascii_compatible cp = false) ->
    ustring_to_ascii_opt u = None.
Proof.
  intros u [cp [Hin Hbad]].
  destruct (ustring_to_ascii_opt u) as [s|] eqn:Hopt; [|reflexivity].
  exfalso.
  pose proof (proj1 (ustring_to_ascii_opt_some_iff u) (ex_intro _ s Hopt)) as Hcompat.
  apply Forall_forall with (x:=cp) in Hcompat; [|exact Hin].
  rewrite Hbad in Hcompat.
  discriminate Hcompat.
Qed.

End Unicode.

Module UnicodeJSON.
Import Unicode JSON.

Inductive uvalue :=
| UNull
| UBool (b:bool)
| UNum (n:Q)
| UStr (s:ustring)
| UArr (xs:list uvalue)
| UObject (fields:list (ustring * uvalue)).

Inductive ustep :=
| USName (s:ustring)
| USIndex (i:Z).

Definition upath := list ustep.
Definition unode := (upath * uvalue)%type.

Fixpoint of_ascii_value (v:JSON.value) : uvalue :=
  match v with
  | JNull => UNull
  | JBool b => UBool b
  | JNum n => UNum n
  | JStr s => UStr (string_to_ustring s)
  | JArr xs => UArr (map of_ascii_value xs)
  | JObject fields =>
      UObject (map (fun '(k, v') => (string_to_ustring k, of_ascii_value v')) fields)
  end.

Fixpoint to_ascii_value (v:uvalue) : JSON.value :=
  match v with
  | UNull => JNull
  | UBool b => JBool b
  | UNum n => JNum n
  | UStr s => JStr (ustring_to_ascii_string s)
  | UArr xs => JArr (map to_ascii_value xs)
  | UObject fields =>
      JObject (map (fun '(k, v') => (ustring_to_ascii_string k, to_ascii_value v')) fields)
  end.

Definition of_ascii_step (s:JSON.step) : ustep :=
  match s with
  | JSON.SName k => USName (string_to_ustring k)
  | JSON.SIndex i => USIndex i
  end.

Definition to_ascii_step (s:ustep) : JSON.step :=
  match s with
  | USName k => JSON.SName (ustring_to_ascii_string k)
  | USIndex i => JSON.SIndex i
  end.

Fixpoint of_ascii_path (p:JSON.path) : upath :=
  match p with
  | [] => []
  | s::ps => of_ascii_step s :: of_ascii_path ps
  end.

Fixpoint to_ascii_path (p:upath) : JSON.path :=
  match p with
  | [] => []
  | s::ps => to_ascii_step s :: to_ascii_path ps
  end.

Definition of_ascii_node (n:JSON.node) : unode :=
  (of_ascii_path (fst n), of_ascii_value (snd n)).

Definition to_ascii_node (n:unode) : JSON.node :=
  (to_ascii_path (fst n), to_ascii_value (snd n)).

Inductive uvalue_valid : uvalue -> Prop :=
| UValNull :
    uvalue_valid UNull
| UValBool :
    forall b,
      uvalue_valid (UBool b)
| UValNum :
    forall n,
      uvalue_valid (UNum n)
| UValStr :
    forall s,
      valid_ustring s ->
      uvalue_valid (UStr s)
| UValArr :
    forall xs,
      Forall uvalue_valid xs ->
      uvalue_valid (UArr xs)
| UValObj :
    forall fields,
      Forall (fun kv => valid_ustring (fst kv) /\ uvalue_valid (snd kv)) fields ->
      uvalue_valid (UObject fields).

Definition ustep_valid (s:ustep) : Prop :=
  match s with
  | USName k => valid_ustring k
  | USIndex _ => True
  end.

Definition upath_valid (p:upath) : Prop := Forall ustep_valid p.

Definition unode_valid (n:unode) : Prop :=
  upath_valid (fst n) /\ uvalue_valid (snd n).

Fixpoint to_ascii_value_opt (v:uvalue) : option JSON.value :=
  match v with
  | UNull => Some JNull
  | UBool b => Some (JBool b)
  | UNum n => Some (JNum n)
  | UStr s =>
      match ustring_to_ascii_opt s with
      | Some s' => Some (JStr s')
      | None => None
      end
  | UArr xs =>
      let fix go (ys:list uvalue) : option (list JSON.value) :=
          match ys with
          | [] => Some []
          | y::ys' =>
              match to_ascii_value_opt y, go ys' with
              | Some y', Some ys'' => Some (y' :: ys'')
              | _, _ => None
              end
          end in
      match go xs with
      | Some ys => Some (JArr ys)
      | None => None
      end
  | UObject fs =>
      let fix go (gs:list (ustring * uvalue))
          : option (list (string * JSON.value)) :=
          match gs with
          | [] => Some []
          | (k, v')::gs' =>
              match ustring_to_ascii_opt k, to_ascii_value_opt v', go gs' with
              | Some k', Some v'', Some gs'' => Some ((k', v'') :: gs'')
              | _, _, _ => None
              end
          end in
      match go fs with
      | Some fs' => Some (JObject fs')
      | None => None
      end
  end.

Definition to_ascii_step_opt (s:ustep) : option JSON.step :=
  match s with
  | USName k =>
      match ustring_to_ascii_opt k with
      | Some k' => Some (JSON.SName k')
      | None => None
      end
  | USIndex i => Some (JSON.SIndex i)
  end.

Fixpoint to_ascii_path_opt (p:upath) : option JSON.path :=
  match p with
  | [] => Some []
  | s::ps =>
      match to_ascii_step_opt s, to_ascii_path_opt ps with
      | Some s', Some ps' => Some (s' :: ps')
      | _, _ => None
      end
  end.

Definition to_ascii_node_opt (n:unode) : option JSON.node :=
  match to_ascii_path_opt (fst n), to_ascii_value_opt (snd n) with
  | Some p, Some v => Some (p, v)
  | _, _ => None
  end.

Theorem of_ascii_value_valid :
  forall v,
    uvalue_valid (of_ascii_value v).
Proof.
  fix IH 1.
  intro v.
  destruct v as [|b|n|s|xs|fields]; simpl.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
    apply string_to_ustring_valid.
  - apply UValArr.
    induction xs as [|x xs IHxs]; simpl.
    + constructor.
    + constructor.
      * apply IH.
      * exact IHxs.
  - apply UValObj.
    induction fields as [|[k v'] fs IHfs]; simpl.
    + constructor.
    + constructor.
      * split.
        -- apply string_to_ustring_valid.
        -- apply IH.
      * exact IHfs.
Qed.

Lemma of_ascii_step_valid :
  forall s,
    ustep_valid (of_ascii_step s).
Proof.
  intros [k|i]; simpl.
  - apply string_to_ustring_valid.
  - exact I.
Qed.

Lemma of_ascii_path_valid :
  forall p,
    upath_valid (of_ascii_path p).
Proof.
  induction p as [|s p IH]; simpl.
  - constructor.
  - constructor.
    + apply of_ascii_step_valid.
    + exact IH.
Qed.

Lemma of_ascii_node_valid :
  forall n,
    unode_valid (of_ascii_node n).
Proof.
  intros [p v]. unfold unode_valid, of_ascii_node. simpl.
  split.
  - apply of_ascii_path_valid.
  - apply of_ascii_value_valid.
Qed.

Theorem to_ascii_value_opt_of_ascii :
  forall v,
    to_ascii_value_opt (of_ascii_value v) = Some v.
Proof.
  fix IH 1.
  intro v.
  destruct v as [|b|n|s|xs|fields]; simpl.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite ascii_partial_roundtrip. reflexivity.
  - assert
      (Hxs :
        (fix go (ys : list uvalue) : option (list JSON.value) :=
           match ys with
           | [] => Some []
           | y :: ys' =>
               match to_ascii_value_opt y, go ys' with
               | Some y', Some ys'' => Some (y' :: ys'')
               | _, _ => None
               end
           end) (map of_ascii_value xs) = Some xs).
    { induction xs as [|x xs IHxs]; simpl.
      - reflexivity.
      - rewrite (IH x), IHxs. reflexivity. }
    rewrite Hxs. reflexivity.
  - induction fields as [|[k v'] fs IHfs]; simpl.
    + reflexivity.
    + rewrite ascii_partial_roundtrip.
      rewrite (IH v').
      assert
        (Htail :
          (fix go (gs : list (ustring * uvalue))
             : option (list (string * JSON.value)) :=
             match gs with
             | [] => Some []
             | (k0, v0) :: gs' =>
                 match ustring_to_ascii_opt k0, to_ascii_value_opt v0, go gs' with
                 | Some k', Some v'', Some gs'' => Some ((k', v'') :: gs'')
                 | _, _, _ => None
                 end
             end)
            (map (fun '(k0, v0) => (string_to_ustring k0, of_ascii_value v0)) fs)
          = Some fs).
      {
        specialize IHfs.
        simpl in IHfs.
        destruct
          ((fix go (gs : list (ustring * uvalue))
              : option (list (string * JSON.value)) :=
              match gs with
              | [] => Some []
              | (k0, v0) :: gs' =>
                  match ustring_to_ascii_opt k0, to_ascii_value_opt v0, go gs' with
                  | Some k', Some v'', Some gs'' => Some ((k', v'') :: gs'')
                  | _, _, _ => None
                  end
              end)
             (map (fun '(k0, v0) => (string_to_ustring k0, of_ascii_value v0)) fs))
          as [fs'|] eqn:Hgo; try discriminate.
        inversion IHfs; subst.
        reflexivity.
      }
      rewrite Htail.
      reflexivity.
Qed.

Lemma to_ascii_step_opt_of_ascii :
  forall s,
    to_ascii_step_opt (of_ascii_step s) = Some s.
Proof.
  intros [k|i]; simpl.
  - rewrite ascii_partial_roundtrip. reflexivity.
  - reflexivity.
Qed.

Theorem to_ascii_path_opt_of_ascii :
  forall p,
    to_ascii_path_opt (of_ascii_path p) = Some p.
Proof.
  induction p as [|s p IH]; simpl.
  - reflexivity.
  - rewrite to_ascii_step_opt_of_ascii.
    rewrite IH.
    reflexivity.
Qed.

Theorem to_ascii_node_opt_of_ascii :
  forall n,
    to_ascii_node_opt (of_ascii_node n) = Some n.
Proof.
  intros [p v]. unfold to_ascii_node_opt, of_ascii_node. simpl.
  rewrite to_ascii_path_opt_of_ascii.
  rewrite to_ascii_value_opt_of_ascii.
  reflexivity.
Qed.

Theorem to_ascii_of_ascii_value :
  forall v, to_ascii_value (of_ascii_value v) = v.
Proof.
  fix IH 1.
  intro v.
  destruct v as [|b|n|s|xs|fields]; simpl.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite ascii_roundtrip. reflexivity.
  - f_equal.
    induction xs as [|x xs IHxs]; simpl.
    + reflexivity.
    + rewrite (IH x), IHxs. reflexivity.
  - f_equal.
    induction fields as [|[k v'] fs IHfs]; simpl.
    + reflexivity.
    + rewrite ascii_roundtrip.
      rewrite (IH v').
      rewrite IHfs.
      reflexivity.
Qed.

Theorem to_ascii_of_ascii_path :
  forall p, to_ascii_path (of_ascii_path p) = p.
Proof.
  induction p as [|s p IH]; simpl.
  - reflexivity.
  - destruct s as [k|i]; simpl.
    + rewrite ascii_roundtrip, IH. reflexivity.
    + rewrite IH. reflexivity.
Qed.

Theorem to_ascii_of_ascii_node :
  forall n, to_ascii_node (of_ascii_node n) = n.
Proof.
  intros [p v]. unfold to_ascii_node, of_ascii_node. simpl.
  rewrite to_ascii_of_ascii_path, to_ascii_of_ascii_value.
  reflexivity.
Qed.

End UnicodeJSON.

Module UnicodeJSONPath.
Import Unicode UnicodeJSON.

Inductive uprim :=
| UPNull
| UPBool (b:bool)
| UPNum (n:Q)
| UPStr (s:ustring).

Definition uprim_of_uvalue (v:uvalue) : option uprim :=
  match v with
  | UNull => Some UPNull
  | UBool b => Some (UPBool b)
  | UNum n => Some (UPNum n)
  | UStr s => Some (UPStr s)
  | _ => None
  end.

Inductive ucmp := UCEq | UCNe | UCLt | UCLe | UCGt | UCGe.

Inductive uregex :=
| UREmpty
| UREps
| URChr (c:codepoint)
| URAny
| URAlt (r1 r2:uregex)
| URCat (r1 r2:uregex)
| URStar (r:uregex)
| URPlus (r:uregex)
| UROpt (r:uregex)
| URRepeat (r:uregex) (min max:nat)
| URCharClass (neg:bool) (chars:list codepoint).

Inductive uaexpr :=
| UAPrim (p:uprim)
| UACount (q:uquery)
| UAValue (q:uquery)
| UALengthV (q:uquery)

with ufexpr :=
| UFTrue
| UFNot (f:ufexpr)
| UFAnd (f g:ufexpr)
| UFOr  (f g:ufexpr)
| UFExists (q:uquery)
| UFCmp (op:ucmp) (a b:uaexpr)
| UFMatch (a:uaexpr) (r:uregex)
| UFSearch (a:uaexpr) (r:uregex)

with uselector :=
| USelName (s:ustring)
| USelWildcard
| USelIndex (i:Z)
| USelSlice (start end_ : option Z) (stp: Z)
| USelFilter (f:ufexpr)

with usegment :=
| UChild (sels:list uselector)
| UDesc (sels:list uselector)

with uquery := UQuery (segs:list usegment).

Definition uq_segs (q:uquery) : list usegment :=
  match q with UQuery ss => ss end.

Definition of_ascii_prim (p:JSONPath.prim) : uprim :=
  match p with
  | JSONPath.PNull => UPNull
  | JSONPath.PBool b => UPBool b
  | JSONPath.PNum n => UPNum n
  | JSONPath.PStr s => UPStr (string_to_ustring s)
  end.

Fixpoint of_ascii_regex (r:JSONPath.regex) : uregex :=
  match r with
  | JSONPath.REmpty => UREmpty
  | JSONPath.REps => UREps
  | JSONPath.RChr c => URChr (ascii_to_codepoint c)
  | JSONPath.RAny => URAny
  | JSONPath.RAlt r1 r2 => URAlt (of_ascii_regex r1) (of_ascii_regex r2)
  | JSONPath.RCat r1 r2 => URCat (of_ascii_regex r1) (of_ascii_regex r2)
  | JSONPath.RStar r1 => URStar (of_ascii_regex r1)
  | JSONPath.RPlus r1 => URPlus (of_ascii_regex r1)
  | JSONPath.ROpt r1 => UROpt (of_ascii_regex r1)
  | JSONPath.RRepeat r1 min max => URRepeat (of_ascii_regex r1) min max
  | JSONPath.RCharClass neg chars =>
      URCharClass neg (map ascii_to_codepoint chars)
  end.

Fixpoint of_ascii_aexpr (a:JSONPath.aexpr) : uaexpr :=
  match a with
  | JSONPath.APrim p => UAPrim (of_ascii_prim p)
  | JSONPath.ACount q => UACount (of_ascii_query q)
  | JSONPath.AValue q => UAValue (of_ascii_query q)
  | JSONPath.ALengthV q => UALengthV (of_ascii_query q)
  end

with of_ascii_fexpr (f:JSONPath.fexpr) : ufexpr :=
  match f with
  | JSONPath.FTrue => UFTrue
  | JSONPath.FNot g => UFNot (of_ascii_fexpr g)
  | JSONPath.FAnd g h => UFAnd (of_ascii_fexpr g) (of_ascii_fexpr h)
  | JSONPath.FOr g h => UFOr (of_ascii_fexpr g) (of_ascii_fexpr h)
  | JSONPath.FExists q => UFExists (of_ascii_query q)
  | JSONPath.FCmp op a b =>
      let op' :=
        match op with
        | JSONPath.CEq => UCEq
        | JSONPath.CNe => UCNe
        | JSONPath.CLt => UCLt
        | JSONPath.CLe => UCLe
        | JSONPath.CGt => UCGt
        | JSONPath.CGe => UCGe
        end in
      UFCmp op' (of_ascii_aexpr a) (of_ascii_aexpr b)
  | JSONPath.FMatch a r => UFMatch (of_ascii_aexpr a) (of_ascii_regex r)
  | JSONPath.FSearch a r => UFSearch (of_ascii_aexpr a) (of_ascii_regex r)
  end

with of_ascii_selector (s:JSONPath.selector) : uselector :=
  match s with
  | JSONPath.SelName k => USelName (string_to_ustring k)
  | JSONPath.SelWildcard => USelWildcard
  | JSONPath.SelIndex i => USelIndex i
  | JSONPath.SelSlice start end_ stp => USelSlice start end_ stp
  | JSONPath.SelFilter f => USelFilter (of_ascii_fexpr f)
  end

with of_ascii_segment (s:JSONPath.segment) : usegment :=
  match s with
  | JSONPath.Child sels => UChild (map of_ascii_selector sels)
  | JSONPath.Desc sels => UDesc (map of_ascii_selector sels)
  end

with of_ascii_query (q:JSONPath.query) : uquery :=
  match q with
  | JSONPath.Query segs => UQuery (map of_ascii_segment segs)
  end.

End UnicodeJSONPath.

Module UnicodeRegex.
Import Unicode UnicodeJSONPath.

Fixpoint nullable (r:uregex) : bool :=
  match r with
  | UREmpty => false
  | UREps => true
  | URChr _ => false
  | URAny => false
  | URAlt r1 r2 => orb (nullable r1) (nullable r2)
  | URCat r1 r2 => andb (nullable r1) (nullable r2)
  | URStar _ => true
  | URPlus r1 => nullable r1
  | UROpt _ => true
  | URRepeat r1 min max =>
      if Nat.ltb max min then false
      else if Nat.eqb min 0 then true else nullable r1
  | URCharClass _ _ => false
  end.

Fixpoint char_in_list (c:codepoint) (cs:list codepoint) : bool :=
  match cs with
  | [] => false
  | c'::cs' => if codepoint_eqb c c' then true else char_in_list c cs'
  end.

Fixpoint deriv (a:codepoint) (r:uregex) : uregex :=
  match r with
  | UREmpty => UREmpty
  | UREps => UREmpty
  | URChr c => if codepoint_eqb a c then UREps else UREmpty
  | URAny => UREps
  | URAlt r1 r2 => URAlt (deriv a r1) (deriv a r2)
  | URCat r1 r2 =>
      let d1 := deriv a r1 in
      let d2 := deriv a r2 in
      if nullable r1 then URAlt (URCat d1 r2) d2 else URCat d1 r2
  | URStar r1 => URCat (deriv a r1) (URStar r1)
  | URPlus r1 => URCat (deriv a r1) (URStar r1)
  | UROpt r1 => deriv a r1
  | URRepeat r1 min max =>
      if Nat.ltb max min then UREmpty
      else if Nat.eqb min 0
      then if Nat.eqb max 0
           then UREmpty
           else URAlt (URCat (deriv a r1) (URRepeat r1 0 (max - 1))) UREmpty
      else URCat (deriv a r1) (URRepeat r1 (min - 1) (max - 1))
  | URCharClass neg cs =>
      let matches := char_in_list a cs in
      if negb neg then
        if matches then UREps else UREmpty
      else
        if matches then UREmpty else UREps
  end.

Fixpoint rsimpl (r:uregex) : uregex :=
  match r with
  | URAlt r1 r2 =>
      let r1' := rsimpl r1 in
      let r2' := rsimpl r2 in
      match r1', r2' with
      | UREmpty, _ => r2'
      | _, UREmpty => r1'
      | _, _ => URAlt r1' r2'
      end
  | URCat r1 r2 =>
      let r1' := rsimpl r1 in
      let r2' := rsimpl r2 in
      match r1', r2' with
      | UREmpty, _ => UREmpty
      | _, UREmpty => UREmpty
      | UREps, _ => r2'
      | _, UREps => r1'
      | _, _ => URCat r1' r2'
      end
  | URStar r1 =>
      let r1' := rsimpl r1 in
      match r1' with
      | UREmpty | UREps => UREps
      | _ => URStar r1'
      end
  | URPlus r1 =>
      let r1' := rsimpl r1 in
      match r1' with
      | UREmpty => UREmpty
      | _ => URPlus r1'
      end
  | UROpt r1 =>
      UROpt (rsimpl r1)
  | URRepeat r1 min max =>
      let r1' := rsimpl r1 in
      if Nat.ltb max min then UREmpty
      else if Nat.eqb min 0 then
        if Nat.eqb max 0 then UREps
        else URRepeat r1' min max
      else URRepeat r1' min max
  | _ => r
  end.

Definition deriv_simpl (a:codepoint) (r:uregex) : uregex :=
  rsimpl (deriv a r).

Fixpoint matches_from (r:uregex) (cs:ustring) : bool :=
  match cs with
  | [] => nullable r
  | a::cs' => matches_from (deriv_simpl a r) cs'
  end.

Definition regex_match (r:uregex) (s:ustring) : bool :=
  matches_from r s.

Definition regex_search (r:uregex) (s:ustring) : bool :=
  regex_match (URCat (URStar URAny) (URCat r (URStar URAny))) s.

End UnicodeRegex.

Module UnicodeExec.
Import Unicode UnicodeJSON UnicodeJSONPath UnicodeRegex.

Definition mk_unode (p:upath) (v:uvalue) : unode := (p, v).

Definition uprim_eq (p q:uprim) : bool :=
  match p, q with
  | UPNull, UPNull => true
  | UPBool b1, UPBool b2 => Bool.eqb b1 b2
  | UPNum n1, UPNum n2 => Qeqb n1 n2
  | UPStr s1, UPStr s2 => ustring_eqb s1 s2
  | _, _ => false
  end.

Definition uprim_lt (p q:uprim) : bool :=
  match p, q with
  | UPNum n1, UPNum n2 => Qltb n1 n2
  | UPStr s1, UPStr s2 => ustring_ltb s1 s2
  | _, _ => false
  end.

Definition cmp_uprim (op:ucmp) (x y:uprim) : bool :=
  match op with
  | UCEq => uprim_eq x y
  | UCNe => negb (uprim_eq x y)
  | UCLt => uprim_lt x y
  | UCLe => orb (uprim_lt x y) (uprim_eq x y)
  | UCGt => uprim_lt y x
  | UCGe => orb (uprim_lt y x) (uprim_eq x y)
  end.

Definition sel_exec_nf (sel:uselector) (n:unode) : list unode :=
  match n with
  | (p, v) =>
      match sel, v with
      | USelName s, UObject fields =>
          match find (fun kv => ustring_eqb (fst kv) s) fields with
          | Some (_, v') => [mk_unode (List.app p [USName s]) v']
          | None => []
          end
      | USelName _, _ => []

      | USelWildcard, UObject fields =>
          map (fun '(k, v') => mk_unode (List.app p [USName k]) v') fields
      | USelWildcard, UArr xs =>
          map (fun '(i, v') => mk_unode (List.app p [USIndex (Z.of_nat i)]) v')
              (index_zip xs)
      | USelWildcard, _ => []

      | USelIndex z, UArr xs =>
          let idx := if z <? 0 then Z.of_nat (List.length xs) + z else z in
          if (idx <? 0) || (idx >=? Z.of_nat (List.length xs)) then []
          else match nth_error xs (Z.to_nat idx) with
               | Some v' => [mk_unode (List.app p [USIndex idx]) v']
               | None => []
               end
      | USelIndex _, _ => []

      | USelSlice st en stp, UArr xs =>
          let ns := slice_positions (List.length xs) st en stp in
          map (fun n0 => mk_unode (List.app p [USIndex (Z.of_nat n0)])
                                 (match nth_error xs n0 with
                                  | Some v' => v'
                                  | None => UNull
                                  end)) ns
      | USelSlice _ _ _, _ => []

      | USelFilter _, _ => []
      end
  end.

Fixpoint visit_df_uvalue (p:upath) (v:uvalue) {struct v} : list unode :=
  match v with
  | UArr xs =>
      let fix go (i:nat) (ys:list uvalue) {struct ys} : list (list unode) :=
          match ys with
          | [] => []
          | v'::ys' =>
              visit_df_uvalue (List.app p [USIndex (Z.of_nat i)]) v'
              :: go (S i) ys'
          end in
      mk_unode p v :: List.concat (go 0%nat xs)
  | UObject fs =>
      let fix go (gs:list (ustring * uvalue)) {struct gs} : list (list unode) :=
          match gs with
          | [] => []
          | (k, v')::gs' =>
              visit_df_uvalue (List.app p [USName k]) v'
              :: go gs'
          end in
      mk_unode p v :: List.concat (go fs)
  | _ => [mk_unode p v]
  end.

Definition visit_df_unode (n:unode) : list unode :=
  let '(p, v) := n in visit_df_uvalue p v.

Section Engine.
  Variable sel_impl : uselector -> unode -> list unode.

  Definition child_on_node_impl (sels:list uselector) (n:unode) : list unode :=
    List.concat (map (fun s => sel_impl s n) sels).

  Definition seg_exec_impl (seg:usegment) (n:unode) : list unode :=
    match seg with
    | UChild sels => child_on_node_impl sels n
    | UDesc sels =>
        let visited := visit_df_unode n in
        List.concat (map (child_on_node_impl sels) visited)
    end.

  Fixpoint segs_exec_impl (segs:list usegment) (ns:list unode) : list unode :=
    match segs with
    | [] => ns
    | s::ss => segs_exec_impl ss (List.concat (map (seg_exec_impl s) ns))
    end.

  Definition eval_exec_impl (q:uquery) (J:uvalue) : list unode :=
    segs_exec_impl (uq_segs q) [([], J)].
End Engine.

Definition child_on_node_nf := child_on_node_impl sel_exec_nf.
Definition seg_exec_nf := seg_exec_impl sel_exec_nf.
Definition segs_exec_nf := segs_exec_impl sel_exec_nf.
Definition eval_exec_nf := eval_exec_impl sel_exec_nf.

Fixpoint sel_exec (sel:uselector) (n:unode) {struct sel} : list unode :=
  match sel, n with
  | USelFilter f, (p, UObject fields) =>
      let keep kv :=
        let '(k, v') := kv in
        holds_b f (List.app p [USName k], v') in
      map (fun '(k, v') => mk_unode (List.app p [USName k]) v')
          (filter (fun kv => keep kv) fields)

  | USelFilter f, (p, UArr xs) =>
      let keep iv :=
        let '(i, v') := iv in
        holds_b f (List.app p [USIndex (Z.of_nat i)], v') in
      map (fun '(i, v') => mk_unode (List.app p [USIndex (Z.of_nat i)]) v')
          (filter (fun iv => keep iv) (index_zip xs))

  | USelFilter _, (_, _) => []

  | USelName s, (p, UObject fields) =>
      match find (fun kv => ustring_eqb (fst kv) s) fields with
      | Some (_, v') => [mk_unode (List.app p [USName s]) v']
      | None => []
      end
  | USelName _, (_, _) => []

  | USelWildcard, (p, UObject fields) =>
      map (fun '(k, v') => mk_unode (List.app p [USName k]) v') fields
  | USelWildcard, (p, UArr xs) =>
      map (fun '(i, v') => mk_unode (List.app p [USIndex (Z.of_nat i)]) v')
          (index_zip xs)
  | USelWildcard, (_, _) => []

  | USelIndex z, (p, UArr xs) =>
      let idx := if z <? 0 then Z.of_nat (List.length xs) + z else z in
      if (idx <? 0) || (idx >=? Z.of_nat (List.length xs)) then []
      else match nth_error xs (Z.to_nat idx) with
           | Some v' => [mk_unode (List.app p [USIndex idx]) v']
           | None => []
           end
  | USelIndex _, (_, _) => []

  | USelSlice st en stp, (p, UArr xs) =>
      let ns := slice_positions (List.length xs) st en stp in
      map (fun n0 => mk_unode (List.app p [USIndex (Z.of_nat n0)])
                             (match nth_error xs n0 with
                              | Some v' => v'
                              | None => UNull
                              end)) ns
  | USelSlice _ _ _, (_, _) => []
  end

with holds_b (f:ufexpr) (n:unode) {struct f} : bool :=
  let '(_, v) := n in
  match f with
  | UFTrue => true
  | UFNot g => negb (holds_b g n)
  | UFAnd g h => andb (holds_b g n) (holds_b h n)
  | UFOr g h => orb (holds_b g n) (holds_b h n)
  | UFExists q =>
      negb (Nat.eqb (List.length (eval_exec_impl sel_exec q v)) 0)
  | UFCmp op a b =>
      match aeval a v, aeval b v with
      | Some pa, Some pb => cmp_uprim op pa pb
      | _, _ => false
      end
  | UFMatch a r =>
      match aeval a v with
      | Some (UPStr s) => UnicodeRegex.regex_match r s
      | _ => false
      end
  | UFSearch a r =>
      match aeval a v with
      | Some (UPStr s) => UnicodeRegex.regex_search r s
      | _ => false
      end
  end

with aeval (a:uaexpr) (v:uvalue) {struct a} : option uprim :=
  match a with
  | UAPrim p => Some p
  | UACount q =>
      let ns := eval_exec_impl sel_exec q v in
      Some (UPNum (Q_of_nat (List.length ns)))
  | UAValue q =>
      let ns := eval_exec_impl sel_exec q v in
      match ns with
      | [(_, v1)] => uprim_of_uvalue v1
      | _ => None
      end
  | UALengthV q =>
      let ns := eval_exec_impl sel_exec q v in
      match ns with
      | [(_, UStr s)] => Some (UPNum (Q_of_nat (List.length s)))
      | [(_, UArr xs)] => Some (UPNum (Q_of_nat (List.length xs)))
      | [(_, UObject fs)] => Some (UPNum (Q_of_nat (List.length fs)))
      | _ => None
      end
  end.

Definition child_on_node := child_on_node_impl sel_exec.
Definition seg_exec := seg_exec_impl sel_exec.
Definition segs_exec := segs_exec_impl sel_exec.
Definition eval_exec := eval_exec_impl sel_exec.

Definition selector_child_only (sel:uselector) : bool :=
  match sel with
  | USelFilter _ => false
  | _ => true
  end.

Definition segment_child_only (seg:usegment) : bool :=
  match seg with
  | UChild sels => forallb selector_child_only sels
  | UDesc _ => false
  end.

Definition query_child_only (q:uquery) : bool :=
  match q with
  | UQuery segs => forallb segment_child_only segs
  end.

Definition linear_selector (sel:uselector) : bool :=
  match sel with
  | USelName _ | USelIndex _ => true
  | _ => false
  end.

Definition linear_segment (s:usegment) : bool :=
  match s with
  | UChild [sel] => linear_selector sel
  | _ => false
  end.

Definition linear_query (q:uquery) : bool :=
  match q with
  | UQuery segs => forallb linear_segment segs
  end.

End UnicodeExec.

(* ------------------------------------------------------------ *)
(* ABNF Tokens + Parser (Core Subset)                           *)
(* ------------------------------------------------------------ *)

Module JSONPathABNF.
Import Unicode JSONPath.

Inductive token :=
| TRoot
| TDot
| TDesc
| TLBracket
| TRBracket
| TStar
| TName (n:ustring)
| TIndex (i:Z).

Definition parse_name (u:ustring) : string :=
  ustring_to_ascii_string u.

Inductive abnf_segments : list token -> list segment -> Prop :=
| ABNFSegNil :
    abnf_segments [] []
| ABNFSegDotName :
    forall u rest segs,
      abnf_segments rest segs ->
      abnf_segments (TDot :: TName u :: rest)
                    (Child [SelName (parse_name u)] :: segs)
| ABNFSegDotStar :
    forall rest segs,
      abnf_segments rest segs ->
      abnf_segments (TDot :: TStar :: rest)
                    (Child [SelWildcard] :: segs)
| ABNFSegBracketName :
    forall u rest segs,
      abnf_segments rest segs ->
      abnf_segments (TLBracket :: TName u :: TRBracket :: rest)
                    (Child [SelName (parse_name u)] :: segs)
| ABNFSegBracketIndex :
    forall i rest segs,
      abnf_segments rest segs ->
      abnf_segments (TLBracket :: TIndex i :: TRBracket :: rest)
                    (Child [SelIndex i] :: segs)
| ABNFSegDescName :
    forall u rest segs,
      abnf_segments rest segs ->
      abnf_segments (TDesc :: TName u :: rest)
                    (Desc [SelName (parse_name u)] :: segs)
| ABNFSegDescStar :
    forall rest segs,
      abnf_segments rest segs ->
      abnf_segments (TDesc :: TStar :: rest)
                    (Desc [SelWildcard] :: segs).

Inductive abnf_query : list token -> query -> Prop :=
| ABNFQuery :
    forall rest segs,
      abnf_segments rest segs ->
      abnf_query (TRoot :: rest) (Query segs).

Fixpoint parse_segments (toks:list token) : option (list segment) :=
  match toks with
  | [] => Some []
  | TDot :: TName u :: rest =>
      match parse_segments rest with
      | Some segs => Some (Child [SelName (parse_name u)] :: segs)
      | None => None
      end
  | TDot :: TStar :: rest =>
      match parse_segments rest with
      | Some segs => Some (Child [SelWildcard] :: segs)
      | None => None
      end
  | TLBracket :: TName u :: TRBracket :: rest =>
      match parse_segments rest with
      | Some segs => Some (Child [SelName (parse_name u)] :: segs)
      | None => None
      end
  | TLBracket :: TIndex i :: TRBracket :: rest =>
      match parse_segments rest with
      | Some segs => Some (Child [SelIndex i] :: segs)
      | None => None
      end
  | TDesc :: TName u :: rest =>
      match parse_segments rest with
      | Some segs => Some (Desc [SelName (parse_name u)] :: segs)
      | None => None
      end
  | TDesc :: TStar :: rest =>
      match parse_segments rest with
      | Some segs => Some (Desc [SelWildcard] :: segs)
      | None => None
      end
  | _ => None
  end.

Definition parse_query (toks:list token) : option query :=
  match toks with
  | TRoot :: rest =>
      match parse_segments rest with
      | Some segs => Some (Query segs)
      | None => None
      end
  | _ => None
  end.

Theorem parse_segments_sound :
  forall toks segs,
    parse_segments toks = Some segs ->
    abnf_segments toks segs.
Proof.
  enough
    (forall n toks segs,
      (List.length toks <= n)%nat ->
      parse_segments toks = Some segs ->
      abnf_segments toks segs) as Hmain.
  { intros toks segs Hparse.
    eapply Hmain with (n := List.length toks); [lia | exact Hparse]. }
  intros n.
  induction n as [|n IH]; intros toks segs Hbound Hparse.
  - destruct toks as [|t toks']; simpl in Hbound.
    + simpl in Hparse. inversion Hparse; subst. constructor.
    + lia.
  - destruct toks as [|t toks']; simpl in Hparse.
    + inversion Hparse; subst. constructor.
    + destruct t; simpl in Hparse; try discriminate.
      * (* TDot *)
        destruct toks' as [|t1 toks1]; simpl in Hparse; try discriminate.
        destruct t1; simpl in Hparse; try discriminate.
        -- (* TStar *)
           destruct (parse_segments toks1) eqn:Hrest; try discriminate.
           inversion Hparse; subst.
           apply ABNFSegDotStar.
           eapply IH.
           ++ simpl in Hbound. lia.
           ++ exact Hrest.
        -- (* TName *)
           destruct (parse_segments toks1) eqn:Hrest; try discriminate.
           inversion Hparse; subst.
           apply ABNFSegDotName.
           eapply IH.
           ++ simpl in Hbound. lia.
           ++ exact Hrest.
      * (* TDesc *)
        destruct toks' as [|t1 toks1]; simpl in Hparse; try discriminate.
        destruct t1; simpl in Hparse; try discriminate.
        -- (* TStar *)
           destruct (parse_segments toks1) eqn:Hrest; try discriminate.
           inversion Hparse; subst.
           apply ABNFSegDescStar.
           eapply IH.
           ++ simpl in Hbound. lia.
           ++ exact Hrest.
        -- (* TName *)
           destruct (parse_segments toks1) eqn:Hrest; try discriminate.
           inversion Hparse; subst.
           apply ABNFSegDescName.
           eapply IH.
           ++ simpl in Hbound. lia.
           ++ exact Hrest.
      * (* TLBracket *)
        destruct toks' as [|t1 toks1]; simpl in Hparse; try discriminate.
        destruct t1; simpl in Hparse; try discriminate.
        -- (* TName *)
           destruct toks1 as [|t2 toks2]; simpl in Hparse; try discriminate.
           destruct t2; simpl in Hparse; try discriminate.
           destruct (parse_segments toks2) eqn:Hrest; try discriminate.
           inversion Hparse; subst.
           apply ABNFSegBracketName.
           eapply IH.
           ++ simpl in Hbound. lia.
           ++ exact Hrest.
        -- (* TIndex *)
           destruct toks1 as [|t2 toks2]; simpl in Hparse; try discriminate.
           destruct t2; simpl in Hparse; try discriminate.
           destruct (parse_segments toks2) eqn:Hrest; try discriminate.
           inversion Hparse; subst.
           apply ABNFSegBracketIndex.
           eapply IH.
           ++ simpl in Hbound. lia.
           ++ exact Hrest.
Qed.

Theorem parse_segments_complete :
  forall toks segs,
    abnf_segments toks segs ->
    parse_segments toks = Some segs.
Proof.
  intros toks segs Habnf.
  induction Habnf; simpl; rewrite ?IHHabnf; reflexivity.
Qed.

Theorem parse_query_sound :
  forall toks q,
    parse_query toks = Some q ->
    abnf_query toks q.
Proof.
  intros toks q Hparse.
  destruct toks as [|t rest]; simpl in Hparse; try discriminate.
  destruct t; try discriminate.
  destruct (parse_segments rest) as [segs|] eqn:Hsegs; try discriminate.
  inversion Hparse; subst.
  apply ABNFQuery.
  eapply parse_segments_sound; eauto.
Qed.

Theorem parse_query_complete :
  forall toks q,
    abnf_query toks q ->
    parse_query toks = Some q.
Proof.
  intros toks q Habnf.
  inversion Habnf as [rest segs Hsegs]; subst.
  simpl.
  rewrite (parse_segments_complete _ _ Hsegs).
  reflexivity.
Qed.

Theorem parse_query_correct :
  forall toks q,
    parse_query toks = Some q <-> abnf_query toks q.
Proof.
  intros toks q.
  split.
  - apply parse_query_sound.
  - apply parse_query_complete.
Qed.

(* ------------------------------------------------------------ *)
(* Extended ABNF + Parser (Full Current AST Coverage)           *)
(* ------------------------------------------------------------ *)

Inductive full_token :=
| FTRoot
| FTDot
| FTDesc
| FTLBracket
| FTRBracket
| FTComma
| FTStar
| FTQMark
| FTName (n:ustring)
| FTIndex (i:Z)
| FTSlice (start end_ : option Z) (stp:Z)
| FTFilterExpr (f:fexpr).

Definition parse_full_name (u:ustring) : string :=
  parse_name u.

Inductive abnf_full_selector : list full_token -> selector -> list full_token -> Prop :=
| ABNFFullSelName :
    forall u rest,
      abnf_full_selector (FTName u :: rest) (SelName (parse_full_name u)) rest
| ABNFFullSelWildcard :
    forall rest,
      abnf_full_selector (FTStar :: rest) SelWildcard rest
| ABNFFullSelIndex :
    forall i rest,
      abnf_full_selector (FTIndex i :: rest) (SelIndex i) rest
| ABNFFullSelSlice :
    forall start end_ stp rest,
      abnf_full_selector (FTSlice start end_ stp :: rest)
                         (SelSlice start end_ stp) rest
| ABNFFullSelFilter :
    forall f rest,
      abnf_full_selector (FTQMark :: FTFilterExpr f :: rest)
                         (SelFilter f) rest.

Inductive abnf_full_selector_list
    : list full_token -> list selector -> list full_token -> Prop :=
| ABNFFullSelListOne :
    forall toks sel rest,
      abnf_full_selector toks sel rest ->
      (forall toks', rest <> FTComma :: toks') ->
      abnf_full_selector_list toks [sel] rest
| ABNFFullSelListCons :
    forall toks sel toks1 sels rest,
      abnf_full_selector toks sel (FTComma :: toks1) ->
      abnf_full_selector_list toks1 sels rest ->
      abnf_full_selector_list toks (sel :: sels) rest.

Inductive abnf_full_segment : list full_token -> segment -> list full_token -> Prop :=
| ABNFFullSegDotName :
    forall u rest,
      abnf_full_segment (FTDot :: FTName u :: rest)
                        (Child [SelName (parse_full_name u)]) rest
| ABNFFullSegDotStar :
    forall rest,
      abnf_full_segment (FTDot :: FTStar :: rest)
                        (Child [SelWildcard]) rest
| ABNFFullSegBracket :
    forall toks sels rest,
      abnf_full_selector_list toks sels (FTRBracket :: rest) ->
      abnf_full_segment (FTLBracket :: toks) (Child sels) rest
| ABNFFullSegDescName :
    forall u rest,
      abnf_full_segment (FTDesc :: FTName u :: rest)
                        (Desc [SelName (parse_full_name u)]) rest
| ABNFFullSegDescStar :
    forall rest,
      abnf_full_segment (FTDesc :: FTStar :: rest)
                        (Desc [SelWildcard]) rest
| ABNFFullSegDescBracket :
    forall toks sels rest,
      abnf_full_selector_list toks sels (FTRBracket :: rest) ->
      abnf_full_segment (FTDesc :: FTLBracket :: toks) (Desc sels) rest.

Inductive abnf_full_segments
    : list full_token -> list segment -> list full_token -> Prop :=
| ABNFFullSegsNil :
    forall toks,
      abnf_full_segments toks [] toks
| ABNFFullSegsCons :
    forall toks seg rest segs final,
      abnf_full_segment toks seg rest ->
      abnf_full_segments rest segs final ->
      abnf_full_segments toks (seg :: segs) final.

Inductive abnf_full_query : list full_token -> query -> Prop :=
| ABNFFullQuery :
    forall rest segs,
      abnf_full_segments rest segs [] ->
      abnf_full_query (FTRoot :: rest) (Query segs).

Definition parse_full_selector
    (toks:list full_token) : option (selector * list full_token) :=
  match toks with
  | FTName u :: rest => Some (SelName (parse_full_name u), rest)
  | FTStar :: rest => Some (SelWildcard, rest)
  | FTIndex i :: rest => Some (SelIndex i, rest)
  | FTSlice start end_ stp :: rest => Some (SelSlice start end_ stp, rest)
  | FTQMark :: FTFilterExpr f :: rest => Some (SelFilter f, rest)
  | _ => None
  end.

Fixpoint parse_full_selector_list_fuel
    (fuel:nat) (toks:list full_token)
    : option (list selector * list full_token) :=
  match fuel with
  | O => None
  | S fuel' =>
      match parse_full_selector toks with
      | None => None
      | Some (sel, rest) =>
          match rest with
          | FTComma :: rest' =>
              match parse_full_selector_list_fuel fuel' rest' with
              | Some (sels, final) => Some (sel :: sels, final)
              | None => None
              end
          | _ => Some ([sel], rest)
          end
      end
  end.

Definition parse_full_selector_list
    (toks:list full_token) : option (list selector * list full_token) :=
  parse_full_selector_list_fuel (S (List.length toks)) toks.

Definition parse_full_segment
    (toks:list full_token) : option (segment * list full_token) :=
  match toks with
  | FTDot :: FTName u :: rest =>
      Some (Child [SelName (parse_full_name u)], rest)
  | FTDot :: FTStar :: rest =>
      Some (Child [SelWildcard], rest)
  | FTLBracket :: rest =>
      match parse_full_selector_list rest with
      | Some (sels, FTRBracket :: final) => Some (Child sels, final)
      | _ => None
      end
  | FTDesc :: FTName u :: rest =>
      Some (Desc [SelName (parse_full_name u)], rest)
  | FTDesc :: FTStar :: rest =>
      Some (Desc [SelWildcard], rest)
  | FTDesc :: FTLBracket :: rest =>
      match parse_full_selector_list rest with
      | Some (sels, FTRBracket :: final) => Some (Desc sels, final)
      | _ => None
      end
  | _ => None
  end.

Fixpoint parse_full_segments_fuel
    (fuel:nat) (toks:list full_token)
    : option (list segment * list full_token) :=
  match fuel with
  | O => Some ([], toks)
  | S fuel' =>
      match parse_full_segment toks with
      | None => Some ([], toks)
      | Some (seg, rest) =>
          match parse_full_segments_fuel fuel' rest with
          | Some (segs, final) => Some (seg :: segs, final)
          | None => None
          end
      end
  end.

Definition parse_full_segments
    (toks:list full_token) : option (list segment * list full_token) :=
  parse_full_segments_fuel (S (List.length toks)) toks.

Definition parse_full_query (toks:list full_token) : option query :=
  match toks with
  | FTRoot :: rest =>
      match parse_full_segments rest with
      | Some (segs, []) => Some (Query segs)
      | _ => None
      end
  | _ => None
  end.

(* Surface parser over lexical tokens for the full current AST grammar. *)
Definition parse_surface_query := parse_full_query.

Lemma parse_full_selector_sound :
  forall toks sel rest,
    parse_full_selector toks = Some (sel, rest) ->
    abnf_full_selector toks sel rest.
Proof.
  intros toks sel rest H.
  destruct toks as [|t toks']; simpl in H; try discriminate.
  destruct t; simpl in H; try discriminate;
    try (inversion H; subst; constructor).
  destruct toks' as [|t2 toks'']; simpl in H; try discriminate.
  destruct t2; simpl in H; try discriminate.
  inversion H; subst. constructor.
Qed.

Lemma parse_full_selector_list_fuel_sound :
  forall fuel toks sels rest,
    parse_full_selector_list_fuel fuel toks = Some (sels, rest) ->
    abnf_full_selector_list toks sels rest.
Proof.
  induction fuel as [|fuel IH]; intros toks sels rest H.
  - simpl in H. discriminate.
  - simpl in H.
    destruct (parse_full_selector toks) as [[sel rest1]|] eqn:Hsel; try discriminate.
    destruct rest1 as [|t rest1'].
    + inversion H; subst.
      apply ABNFFullSelListOne.
      * eapply parse_full_selector_sound; eauto.
      * intros toks' Hcontra. discriminate Hcontra.
    + destruct t.
      * inversion H; subst.
        apply ABNFFullSelListOne.
        -- eapply parse_full_selector_sound; eauto.
        -- intros toks' Hcontra. inversion Hcontra.
      * inversion H; subst.
        apply ABNFFullSelListOne.
        -- eapply parse_full_selector_sound; eauto.
        -- intros toks' Hcontra. inversion Hcontra.
      * inversion H; subst.
        apply ABNFFullSelListOne.
        -- eapply parse_full_selector_sound; eauto.
        -- intros toks' Hcontra. inversion Hcontra.
      * inversion H; subst.
        apply ABNFFullSelListOne.
        -- eapply parse_full_selector_sound; eauto.
        -- intros toks' Hcontra. inversion Hcontra.
      * inversion H; subst.
        apply ABNFFullSelListOne.
        -- eapply parse_full_selector_sound; eauto.
        -- intros toks' Hcontra. inversion Hcontra.
      * destruct (parse_full_selector_list_fuel fuel rest1') as [[sels' rest']|] eqn:Htail;
          try discriminate.
        inversion H; subst.
        eapply ABNFFullSelListCons.
        -- pose proof (parse_full_selector_sound _ _ _ Hsel) as Hs.
           exact Hs.
        -- eapply IH. exact Htail.
      * inversion H; subst.
        apply ABNFFullSelListOne.
        -- eapply parse_full_selector_sound; eauto.
        -- intros toks' Hcontra. inversion Hcontra.
      * inversion H; subst.
        apply ABNFFullSelListOne.
        -- eapply parse_full_selector_sound; eauto.
        -- intros toks' Hcontra. inversion Hcontra.
      * inversion H; subst.
        apply ABNFFullSelListOne.
        -- eapply parse_full_selector_sound; eauto.
        -- intros toks' Hcontra. inversion Hcontra.
      * inversion H; subst.
        apply ABNFFullSelListOne.
        -- eapply parse_full_selector_sound; eauto.
        -- intros toks' Hcontra. inversion Hcontra.
      * inversion H; subst.
        apply ABNFFullSelListOne.
        -- eapply parse_full_selector_sound; eauto.
        -- intros toks' Hcontra. inversion Hcontra.
      * inversion H; subst.
        apply ABNFFullSelListOne.
        -- eapply parse_full_selector_sound; eauto.
        -- intros toks' Hcontra. inversion Hcontra.
Qed.

Lemma parse_full_segment_sound :
  forall toks seg rest,
    parse_full_segment toks = Some (seg, rest) ->
    abnf_full_segment toks seg rest.
Proof.
  intros toks seg rest H.
  destruct toks as [|t toks']; simpl in H; try discriminate.
  destruct t; simpl in H; try discriminate.
  - (* FTDot *)
    destruct toks' as [|t1 toks1]; simpl in H; try discriminate.
    destruct t1; simpl in H; try discriminate.
    + inversion H; subst. constructor.
    + inversion H; subst. constructor.
  - (* FTDesc *)
    destruct toks' as [|t1 toks1]; simpl in H; try discriminate.
    destruct t1; simpl in H; try discriminate.
    + destruct (parse_full_selector_list toks1) as [[sels final]|] eqn:Hsel; try discriminate.
      destruct final as [|t2 final']; try discriminate.
      destruct t2; try discriminate.
      inversion H; subst.
      eapply ABNFFullSegDescBracket.
      eapply parse_full_selector_list_fuel_sound.
      unfold parse_full_selector_list in Hsel.
      exact Hsel.
    + inversion H; subst. constructor.
    + inversion H; subst. constructor.
  - (* FTLBracket *)
    destruct (parse_full_selector_list toks') as [[sels final]|] eqn:Hsel; try discriminate.
    destruct final as [|t1 final']; try discriminate.
    destruct t1; try discriminate.
    inversion H; subst.
    eapply ABNFFullSegBracket.
    eapply parse_full_selector_list_fuel_sound.
    unfold parse_full_selector_list in Hsel.
    exact Hsel.
Qed.

Lemma parse_full_segments_fuel_sound :
  forall fuel toks segs rest,
    parse_full_segments_fuel fuel toks = Some (segs, rest) ->
    abnf_full_segments toks segs rest.
Proof.
  induction fuel as [|fuel IH]; intros toks segs rest H.
  - simpl in H. inversion H; subst. constructor.
  - simpl in H.
    destruct (parse_full_segment toks) as [[seg rest1]|] eqn:Hseg.
    + destruct (parse_full_segments_fuel fuel rest1) as [[segs' final]|] eqn:Htail;
        try discriminate.
      inversion H; subst.
      eapply ABNFFullSegsCons.
      * eapply parse_full_segment_sound. exact Hseg.
      * eapply IH. exact Htail.
    + inversion H; subst. constructor.
Qed.

Theorem parse_full_query_sound :
  forall toks q,
    parse_full_query toks = Some q ->
    abnf_full_query toks q.
Proof.
  intros toks q Hparse.
  destruct toks as [|t rest]; simpl in Hparse; try discriminate.
  destruct t; try discriminate.
  destruct (parse_full_segments rest) as [[segs final]|] eqn:Hsegs; try discriminate.
  destruct final as [|x xs]; try discriminate.
  inversion Hparse; subst.
  apply ABNFFullQuery.
  unfold parse_full_segments in Hsegs.
  eapply parse_full_segments_fuel_sound; eauto.
Qed.

(* ------------------------------------------------------------ *)
(* Concrete Unicode Surface Lexer + Parser                      *)
(* ------------------------------------------------------------ *)

Inductive surface_token :=
| STDollar
| STDot
| STDesc
| STLBracket
| STRBracket
| STComma
| STStar
| STQMark
| STLParen
| STRParen
| STColon
| STName (n:ustring)
| STInt (i:Z)
| STString (s:ustring)
| STKwTrue
| STKwFalse
| STKwNull
| STKwNot
| STKwAnd
| STKwOr
| STKwExists
| STKwCmp
| STKwMatch
| STKwSearch
| STKwCount
| STKwValue
| STKwLength
| STCmpOp (op:cmp).

Inductive lex_error_kind :=
| LexUnexpectedChar
| LexInvalidCodepoint
| LexUnterminatedString
| LexInvalidNumber.

Record lex_error := {
  lex_err_pos : nat;
  lex_err_kind : lex_error_kind;
  lex_err_char : option codepoint
}.

Inductive lex_surface_result :=
| LexSurfaceOk (toks:list surface_token)
| LexSurfaceError (err:lex_error).

Definition cp_eq (cp z:Z) : bool := Z.eqb cp z.

Definition cp_is_space (cp:codepoint) : bool :=
  cp_eq cp 32 || cp_eq cp 9 || cp_eq cp 10 || cp_eq cp 13.

Definition cp_is_digit (cp:codepoint) : bool :=
  (48 <=? cp) && (cp <=? 57).

Definition cp_is_alpha (cp:codepoint) : bool :=
  ((65 <=? cp) && (cp <=? 90)) ||
  ((97 <=? cp) && (cp <=? 122)).

Definition cp_is_ident_start (cp:codepoint) : bool :=
  cp_is_alpha cp || cp_eq cp 95.

Definition cp_is_ident_continue (cp:codepoint) : bool :=
  cp_is_ident_start cp || cp_is_digit cp.

Fixpoint take_while_cp
    (fuel:nat) (pred:codepoint -> bool) (cs:ustring)
    : ustring * ustring * nat :=
  match fuel with
  | O => ([], cs, 0%nat)
  | S fuel' =>
      match cs with
      | [] => ([], [], 0%nat)
      | c::rest =>
          if pred c then
            let '(pref, rem, n) := take_while_cp fuel' pred rest in
            (c :: pref, rem, S n)
          else ([], cs, 0%nat)
      end
  end.

Fixpoint parse_digits_acc (ds:ustring) (acc:Z) : Z :=
  match ds with
  | [] => acc
  | d::ds' => parse_digits_acc ds' (10 * acc + (d - 48))
  end.

Definition parse_digits (ds:ustring) : Z :=
  parse_digits_acc ds 0.

Definition lex_surface_prepend (t:surface_token) (r:lex_surface_result)
    : lex_surface_result :=
  match r with
  | LexSurfaceOk toks => LexSurfaceOk (t :: toks)
  | LexSurfaceError e => LexSurfaceError e
  end.

Fixpoint lex_string_body
    (fuel:nat) (pos:nat) (acc:ustring) (cs:ustring)
    : option (ustring * ustring * nat) :=
  match fuel with
  | O => None
  | S fuel' =>
      match cs with
      | [] => None
      | c::rest =>
          if cp_eq c 34 then Some (rev acc, rest, 1%nat)
          else
            match lex_string_body fuel' (S pos) (c::acc) rest with
            | Some (s, rem, n) => Some (s, rem, S n)
            | None => None
            end
      end
  end.

Fixpoint first_invalid_codepoint (u:ustring) : option (nat * codepoint) :=
  match u with
  | [] => None
  | c::u' =>
      if codepoint_valid c then
        match first_invalid_codepoint u' with
        | Some (k, bad) => Some (S k, bad)
        | None => None
        end
      else Some (0%nat, c)
  end.

Definition surface_keyword_or_name (u:ustring) : surface_token :=
  let s := parse_name u in
  if string_eqb s "true" then STKwTrue else
  if string_eqb s "false" then STKwFalse else
  if string_eqb s "null" then STKwNull else
  if string_eqb s "not" then STKwNot else
  if string_eqb s "and" then STKwAnd else
  if string_eqb s "or" then STKwOr else
  if string_eqb s "exists" then STKwExists else
  if string_eqb s "cmp" then STKwCmp else
  if string_eqb s "match" then STKwMatch else
  if string_eqb s "search" then STKwSearch else
  if string_eqb s "count" then STKwCount else
  if string_eqb s "value" then STKwValue else
  if string_eqb s "length" then STKwLength else
  if string_eqb s "eq" then STCmpOp CEq else
  if string_eqb s "ne" then STCmpOp CNe else
  if string_eqb s "lt" then STCmpOp CLt else
  if string_eqb s "le" then STCmpOp CLe else
  if string_eqb s "gt" then STCmpOp CGt else
  if string_eqb s "ge" then STCmpOp CGe else
  STName u.

Fixpoint lex_surface_aux (fuel:nat) (pos:nat) (cs:ustring)
    : lex_surface_result :=
  match fuel with
  | O =>
      LexSurfaceError
        {| lex_err_pos := pos;
           lex_err_kind := LexUnexpectedChar;
           lex_err_char := None |}
  | S fuel' =>
      match cs with
      | [] => LexSurfaceOk []
      | c::rest =>
          if negb (codepoint_valid c) then
            LexSurfaceError
              {| lex_err_pos := pos;
                 lex_err_kind := LexInvalidCodepoint;
                 lex_err_char := Some c |}
          else if cp_is_space c then
            lex_surface_aux fuel' (S pos) rest
          else if cp_eq c 36 then (* $ *)
            lex_surface_prepend STDollar (lex_surface_aux fuel' (S pos) rest)
          else if cp_eq c 46 then (* . or .. *)
            match rest with
            | c2::rest2 =>
                if cp_eq c2 46 then
                  lex_surface_prepend STDesc (lex_surface_aux fuel' (pos + 2)%nat rest2)
                else
                  lex_surface_prepend STDot (lex_surface_aux fuel' (S pos) rest)
            | [] =>
                lex_surface_prepend STDot (lex_surface_aux fuel' (S pos) rest)
            end
          else if cp_eq c 91 then
            lex_surface_prepend STLBracket (lex_surface_aux fuel' (S pos) rest)
          else if cp_eq c 93 then
            lex_surface_prepend STRBracket (lex_surface_aux fuel' (S pos) rest)
          else if cp_eq c 44 then
            lex_surface_prepend STComma (lex_surface_aux fuel' (S pos) rest)
          else if cp_eq c 42 then
            lex_surface_prepend STStar (lex_surface_aux fuel' (S pos) rest)
          else if cp_eq c 63 then
            lex_surface_prepend STQMark (lex_surface_aux fuel' (S pos) rest)
          else if cp_eq c 40 then
            lex_surface_prepend STLParen (lex_surface_aux fuel' (S pos) rest)
          else if cp_eq c 41 then
            lex_surface_prepend STRParen (lex_surface_aux fuel' (S pos) rest)
          else if cp_eq c 58 then
            lex_surface_prepend STColon (lex_surface_aux fuel' (S pos) rest)
          else if cp_eq c 34 then (* quoted string *)
            match lex_string_body fuel' (S pos) [] rest with
            | Some (s, rem, consumed) =>
                match first_invalid_codepoint s with
                | Some (k, bad) =>
                    LexSurfaceError
                      {| lex_err_pos := (pos + 1 + k)%nat;
                         lex_err_kind := LexInvalidCodepoint;
                         lex_err_char := Some bad |}
                | None =>
                    lex_surface_prepend (STString s)
                      (lex_surface_aux fuel' (pos + 1 + consumed)%nat rem)
                end
            | None =>
                LexSurfaceError
                  {| lex_err_pos := pos;
                     lex_err_kind := LexUnterminatedString;
                     lex_err_char := Some c |}
            end
          else if cp_eq c 45 then (* negative integer *)
            match rest with
            | d::rest' =>
                if cp_is_digit d then
                  let '(digits, rem, consumed) :=
                      take_while_cp fuel' cp_is_digit rest in
                  let z := - (parse_digits digits) in
                  lex_surface_prepend (STInt z)
                    (lex_surface_aux fuel' (pos + 1 + consumed)%nat rem)
                else
                  LexSurfaceError
                    {| lex_err_pos := pos;
                       lex_err_kind := LexInvalidNumber;
                       lex_err_char := Some c |}
            | [] =>
                LexSurfaceError
                  {| lex_err_pos := pos;
                     lex_err_kind := LexInvalidNumber;
                     lex_err_char := Some c |}
            end
          else if cp_is_digit c then
            let '(digits, rem, consumed) :=
                take_while_cp fuel' cp_is_digit cs in
            let z := parse_digits digits in
            lex_surface_prepend (STInt z)
              (lex_surface_aux fuel' (pos + consumed)%nat rem)
          else if cp_is_ident_start c then
            let '(ident, rem, consumed) :=
                take_while_cp fuel' cp_is_ident_continue cs in
            match first_invalid_codepoint ident with
            | Some (k, bad) =>
                LexSurfaceError
                  {| lex_err_pos := (pos + k)%nat;
                     lex_err_kind := LexInvalidCodepoint;
                     lex_err_char := Some bad |}
            | None =>
                let tok := surface_keyword_or_name ident in
                lex_surface_prepend tok
                  (lex_surface_aux fuel' (pos + consumed)%nat rem)
            end
          else
            LexSurfaceError
              {| lex_err_pos := pos;
                 lex_err_kind := LexUnexpectedChar;
                 lex_err_char := Some c |}
      end
  end.

Definition lex_surface (s:ustring) : lex_surface_result :=
  lex_surface_aux (S (List.length s)) 0 s.

Definition surface_token_payload_validb (t:surface_token) : bool :=
  match t with
  | STName n => ustring_validb n
  | STString s => ustring_validb s
  | _ => true
  end.

Definition surface_token_payload_valid (t:surface_token) : Prop :=
  match t with
  | STName n => valid_ustring n
  | STString s => valid_ustring s
  | _ => True
  end.

Lemma first_invalid_codepoint_none_validb :
  forall u,
    first_invalid_codepoint u = None ->
    ustring_validb u = true.
Proof.
  induction u as [|c u IH]; intro H; simpl in *.
  - reflexivity.
  - destruct (codepoint_valid c) eqn:Hc; try discriminate.
    destruct (first_invalid_codepoint u) as [[k bad]|] eqn:Hu; try discriminate.
    simpl.
    specialize (IH eq_refl).
    rewrite IH.
    reflexivity.
Qed.

Lemma surface_keyword_or_name_payload_validb :
  forall u,
    ustring_validb u = true ->
    surface_token_payload_validb (surface_keyword_or_name u) = true.
Proof.
  intros u Hu.
  unfold surface_keyword_or_name.
  destruct (string_eqb (parse_name u) "true") eqn:E1; simpl; try reflexivity.
  destruct (string_eqb (parse_name u) "false") eqn:E2; simpl; try reflexivity.
  destruct (string_eqb (parse_name u) "null") eqn:E3; simpl; try reflexivity.
  destruct (string_eqb (parse_name u) "not") eqn:E4; simpl; try reflexivity.
  destruct (string_eqb (parse_name u) "and") eqn:E5; simpl; try reflexivity.
  destruct (string_eqb (parse_name u) "or") eqn:E6; simpl; try reflexivity.
  destruct (string_eqb (parse_name u) "exists") eqn:E7; simpl; try reflexivity.
  destruct (string_eqb (parse_name u) "cmp") eqn:E8; simpl; try reflexivity.
  destruct (string_eqb (parse_name u) "match") eqn:E9; simpl; try reflexivity.
  destruct (string_eqb (parse_name u) "search") eqn:E10; simpl; try reflexivity.
  destruct (string_eqb (parse_name u) "count") eqn:E11; simpl; try reflexivity.
  destruct (string_eqb (parse_name u) "value") eqn:E12; simpl; try reflexivity.
  destruct (string_eqb (parse_name u) "length") eqn:E13; simpl; try reflexivity.
  destruct (string_eqb (parse_name u) "eq") eqn:E14; simpl; try reflexivity.
  destruct (string_eqb (parse_name u) "ne") eqn:E15; simpl; try reflexivity.
  destruct (string_eqb (parse_name u) "lt") eqn:E16; simpl; try reflexivity.
  destruct (string_eqb (parse_name u) "le") eqn:E17; simpl; try reflexivity.
  destruct (string_eqb (parse_name u) "gt") eqn:E18; simpl; try reflexivity.
  destruct (string_eqb (parse_name u) "ge") eqn:E19; simpl; try reflexivity.
  exact Hu.
Qed.

Lemma lex_surface_aux_payload_valid :
  forall fuel pos cs toks,
    lex_surface_aux fuel pos cs = LexSurfaceOk toks ->
    forallb surface_token_payload_validb toks = true.
Proof.
  induction fuel as [|fuel IH]; intros pos cs toks Hlex; simpl in Hlex.
  - discriminate.
  - destruct cs as [|c rest].
    + inversion Hlex; subst. reflexivity.
    + destruct (negb (codepoint_valid c)) eqn:Hbad; try discriminate.
      destruct (cp_is_space c) eqn:Hspace.
      * eapply IH. exact Hlex.
      * destruct (cp_eq c 36) eqn:Hdollar.
        { destruct (lex_surface_aux fuel (S pos) rest) eqn:Hrec;
            simpl in Hlex; try discriminate.
          inversion Hlex; subst; clear Hlex.
          simpl. rewrite (IH _ _ _ Hrec). reflexivity. }
        destruct (cp_eq c 46) eqn:Hdot.
        { destruct rest as [|c2 rest2].
          - destruct (lex_surface_aux fuel (S pos) []) eqn:Hrec;
              simpl in Hlex; try discriminate.
            inversion Hlex; subst; clear Hlex.
            simpl. rewrite (IH _ _ _ Hrec). reflexivity.
          - destruct (cp_eq c2 46) eqn:Hdesc.
            + destruct (lex_surface_aux fuel (pos + 2)%nat rest2) eqn:Hrec;
                simpl in Hlex; try discriminate.
              inversion Hlex; subst; clear Hlex.
              simpl. rewrite (IH _ _ _ Hrec). reflexivity.
            + destruct (lex_surface_aux fuel (S pos) (c2 :: rest2)) eqn:Hrec;
                simpl in Hlex; try discriminate.
              inversion Hlex; subst; clear Hlex.
              simpl. rewrite (IH _ _ _ Hrec). reflexivity. }
        destruct (cp_eq c 91) eqn:Hlbr.
        { destruct (lex_surface_aux fuel (S pos) rest) eqn:Hrec;
            simpl in Hlex; try discriminate.
          inversion Hlex; subst; clear Hlex.
          simpl. rewrite (IH _ _ _ Hrec). reflexivity. }
        destruct (cp_eq c 93) eqn:Hrbr.
        { destruct (lex_surface_aux fuel (S pos) rest) eqn:Hrec;
            simpl in Hlex; try discriminate.
          inversion Hlex; subst; clear Hlex.
          simpl. rewrite (IH _ _ _ Hrec). reflexivity. }
        destruct (cp_eq c 44) eqn:Hcomma.
        { destruct (lex_surface_aux fuel (S pos) rest) eqn:Hrec;
            simpl in Hlex; try discriminate.
          inversion Hlex; subst; clear Hlex.
          simpl. rewrite (IH _ _ _ Hrec). reflexivity. }
        destruct (cp_eq c 42) eqn:Hstar.
        { destruct (lex_surface_aux fuel (S pos) rest) eqn:Hrec;
            simpl in Hlex; try discriminate.
          inversion Hlex; subst; clear Hlex.
          simpl. rewrite (IH _ _ _ Hrec). reflexivity. }
        destruct (cp_eq c 63) eqn:Hqmark.
        { destruct (lex_surface_aux fuel (S pos) rest) eqn:Hrec;
            simpl in Hlex; try discriminate.
          inversion Hlex; subst; clear Hlex.
          simpl. rewrite (IH _ _ _ Hrec). reflexivity. }
        destruct (cp_eq c 40) eqn:Hlpar.
        { destruct (lex_surface_aux fuel (S pos) rest) eqn:Hrec;
            simpl in Hlex; try discriminate.
          inversion Hlex; subst; clear Hlex.
          simpl. rewrite (IH _ _ _ Hrec). reflexivity. }
        destruct (cp_eq c 41) eqn:Hrpar.
        { destruct (lex_surface_aux fuel (S pos) rest) eqn:Hrec;
            simpl in Hlex; try discriminate.
          inversion Hlex; subst; clear Hlex.
          simpl. rewrite (IH _ _ _ Hrec). reflexivity. }
        destruct (cp_eq c 58) eqn:Hcolon.
        { destruct (lex_surface_aux fuel (S pos) rest) eqn:Hrec;
            simpl in Hlex; try discriminate.
          inversion Hlex; subst; clear Hlex.
          simpl. rewrite (IH _ _ _ Hrec). reflexivity. }
        destruct (cp_eq c 34) eqn:Hquote.
        { destruct (lex_string_body fuel (S pos) [] rest) as [sr|] eqn:Hstr.
          - destruct sr as [[s rem] consumed].
            destruct (first_invalid_codepoint s) as [[k bad]|] eqn:Hinv; try discriminate.
            destruct (lex_surface_aux fuel (pos + 1 + consumed)%nat rem) eqn:Hrec;
              simpl in Hlex; try discriminate.
            inversion Hlex; subst; clear Hlex.
            simpl.
            rewrite (first_invalid_codepoint_none_validb s Hinv).
            rewrite (IH _ _ _ Hrec).
            reflexivity.
          - discriminate. }
        destruct (cp_eq c 45) eqn:Hminus.
        { destruct rest as [|d rest'].
          - discriminate.
          - destruct (cp_is_digit d) eqn:Hdig.
            + destruct (take_while_cp fuel cp_is_digit (d :: rest')) as [[digits rem] consumed] eqn:Htake.
              destruct (lex_surface_aux fuel (pos + 1 + consumed)%nat rem) eqn:Hrec;
                simpl in Hlex; try discriminate.
              inversion Hlex; subst; clear Hlex.
              simpl. rewrite (IH _ _ _ Hrec). reflexivity.
            + discriminate. }
        destruct (cp_is_digit c) eqn:Hisdig.
        { destruct (take_while_cp fuel cp_is_digit (c :: rest)) as [[digits rem] consumed] eqn:Htake.
          destruct (lex_surface_aux fuel (pos + consumed)%nat rem) eqn:Hrec;
            simpl in Hlex; try discriminate.
          inversion Hlex; subst; clear Hlex.
          simpl. rewrite (IH _ _ _ Hrec). reflexivity. }
        destruct (cp_is_ident_start c) eqn:Hident.
        { destruct (take_while_cp fuel cp_is_ident_continue (c :: rest)) as [[ident rem] consumed] eqn:Htake.
          destruct (first_invalid_codepoint ident) as [[k bad]|] eqn:Hinv; try discriminate.
          destruct (lex_surface_aux fuel (pos + consumed)%nat rem) eqn:Hrec;
            simpl in Hlex; try discriminate.
          inversion Hlex; subst; clear Hlex.
          simpl.
          rewrite (surface_keyword_or_name_payload_validb ident
                     (first_invalid_codepoint_none_validb ident Hinv)).
          rewrite (IH _ _ _ Hrec).
          reflexivity. }
        discriminate.
Qed.

Theorem lex_surface_payload_valid :
  forall s toks,
    lex_surface s = LexSurfaceOk toks ->
    forallb surface_token_payload_validb toks = true.
Proof.
  intros s toks Hlex.
  unfold lex_surface in Hlex.
  eapply lex_surface_aux_payload_valid.
  exact Hlex.
Qed.

Lemma surface_token_payload_validb_sound :
  forall t,
    surface_token_payload_validb t = true ->
    surface_token_payload_valid t.
Proof.
  intros t H.
  destruct t; simpl in *; try exact I.
  - apply ustring_validb_sound. exact H.
  - apply ustring_validb_sound. exact H.
Qed.

Lemma surface_tokens_payload_validb_sound :
  forall toks,
    forallb surface_token_payload_validb toks = true ->
    Forall surface_token_payload_valid toks.
Proof.
  induction toks as [|t toks IH]; intro H; simpl in H.
  - constructor.
  - apply andb_true_iff in H as [Ht Hrest].
    constructor.
    + apply surface_token_payload_validb_sound. exact Ht.
    + apply IH. exact Hrest.
Qed.

Theorem lex_surface_payload_valid_forall :
  forall s toks,
    lex_surface s = LexSurfaceOk toks ->
    Forall surface_token_payload_valid toks.
Proof.
  intros s toks Hlex.
  apply surface_tokens_payload_validb_sound.
  eapply lex_surface_payload_valid.
  exact Hlex.
Qed.

Definition regex_of_ustring_char (cp:codepoint) : ascii :=
  ascii_of_nat (Z.to_nat cp).

Fixpoint regex_of_ustring (u:ustring) : regex :=
  match u with
  | [] => REps
  | c::u' => RCat (RChr (regex_of_ustring_char c)) (regex_of_ustring u')
  end.

Definition parse_surface_slice_tail
    (start:option Z) (toks:list surface_token)
    : option (selector * list surface_token) :=
  let '(end_opt, rest1) :=
      match toks with
      | STInt j :: rest => (Some j, rest)
      | _ => (None, toks)
      end in
  match rest1 with
  | STColon :: rest2 =>
      let '(step_opt, rest3) :=
          match rest2 with
          | STInt k :: rest => (Some k, rest)
          | _ => (None, rest2)
          end in
      Some (SelSlice start end_opt
                     (match step_opt with Some z => z | None => 1 end), rest3)
  | _ => Some (SelSlice start end_opt 1, rest1)
  end.

Fixpoint parse_surface_aexpr_fuel
    (fuel:nat) (toks:list surface_token)
    : option (aexpr * list surface_token) :=
  match fuel with
  | O => None
  | S fuel' =>
      match toks with
      | STKwNull :: rest => Some (APrim PNull, rest)
      | STKwTrue :: rest => Some (APrim (PBool true), rest)
      | STKwFalse :: rest => Some (APrim (PBool false), rest)
      | STInt z :: rest => Some (APrim (PNum (Q_of_Z z)), rest)
      | STString s :: rest => Some (APrim (PStr (parse_name s)), rest)
      | STKwCount :: rest => Some (ACount (Query []), rest)
      | STKwValue :: rest => Some (AValue (Query []), rest)
      | STKwLength :: rest => Some (ALengthV (Query []), rest)
      | STLParen :: rest =>
          match parse_surface_aexpr_fuel fuel' rest with
          | Some (a, STRParen :: rest') => Some (a, rest')
          | _ => None
          end
      | _ => None
      end
  end.

Definition parse_surface_regex
    (toks:list surface_token) : option (regex * list surface_token) :=
  match toks with
  | STString s :: rest => Some (regex_of_ustring s, rest)
  | STName n :: rest =>
      let k := parse_name n in
      if string_eqb k "any" then Some (RAny, rest)
      else if string_eqb k "eps" then Some (REps, rest)
      else if string_eqb k "empty" then Some (REmpty, rest)
      else None
  | _ => None
  end.

Fixpoint parse_surface_fexpr_fuel
    (fuel:nat) (toks:list surface_token)
    : option (fexpr * list surface_token) :=
  match fuel with
  | O => None
  | S fuel' =>
      match toks with
      | STKwTrue :: rest => Some (FTrue, rest)
      | STKwNot :: STLParen :: rest =>
          match parse_surface_fexpr_fuel fuel' rest with
          | Some (f, STRParen :: rest') => Some (FNot f, rest')
          | _ => None
          end
      | STKwAnd :: STLParen :: rest =>
          match parse_surface_fexpr_fuel fuel' rest with
          | Some (f1, STComma :: rest1) =>
              match parse_surface_fexpr_fuel fuel' rest1 with
              | Some (f2, STRParen :: rest2) => Some (FAnd f1 f2, rest2)
              | _ => None
              end
          | _ => None
          end
      | STKwOr :: STLParen :: rest =>
          match parse_surface_fexpr_fuel fuel' rest with
          | Some (f1, STComma :: rest1) =>
              match parse_surface_fexpr_fuel fuel' rest1 with
              | Some (f2, STRParen :: rest2) => Some (FOr f1 f2, rest2)
              | _ => None
              end
          | _ => None
          end
      | STKwExists :: rest => Some (FExists (Query []), rest)
      | STKwCmp :: STLParen :: rest =>
          match rest with
          | STCmpOp op :: STComma :: rest0 =>
              match parse_surface_aexpr_fuel fuel' rest0 with
              | Some (a1, STComma :: rest1) =>
                  match parse_surface_aexpr_fuel fuel' rest1 with
                  | Some (a2, STRParen :: rest2) =>
                      Some (FCmp op a1 a2, rest2)
                  | _ => None
                  end
              | _ => None
              end
          | _ => None
          end
      | STKwMatch :: STLParen :: rest =>
          match parse_surface_aexpr_fuel fuel' rest with
          | Some (a, STComma :: rest1) =>
              match parse_surface_regex rest1 with
              | Some (r, STRParen :: rest2) => Some (FMatch a r, rest2)
              | _ => None
              end
          | _ => None
          end
      | STKwSearch :: STLParen :: rest =>
          match parse_surface_aexpr_fuel fuel' rest with
          | Some (a, STComma :: rest1) =>
              match parse_surface_regex rest1 with
              | Some (r, STRParen :: rest2) => Some (FSearch a r, rest2)
              | _ => None
              end
          | _ => None
          end
      | _ => None
      end
  end.

Definition parse_surface_selector_fuel
    (fuel:nat) (toks:list surface_token)
    : option (selector * list surface_token) :=
  match fuel with
  | O => None
  | S fuel' =>
      match toks with
      | STName u :: rest => Some (SelName (parse_name u), rest)
      | STString u :: rest => Some (SelName (parse_name u), rest)
      | STStar :: rest => Some (SelWildcard, rest)
      | STInt i :: STColon :: rest => parse_surface_slice_tail (Some i) rest
      | STInt i :: rest => Some (SelIndex i, rest)
      | STColon :: rest => parse_surface_slice_tail None rest
      | STQMark :: STLParen :: rest =>
          match parse_surface_fexpr_fuel fuel' rest with
          | Some (f, STRParen :: rest') => Some (SelFilter f, rest')
          | _ => None
          end
      | _ => None
      end
  end.

Fixpoint parse_surface_selector_list_fuel
    (fuel:nat) (toks:list surface_token)
    : option (list selector * list surface_token) :=
  match fuel with
  | O => None
  | S fuel' =>
      match parse_surface_selector_fuel fuel' toks with
      | Some (sel, STComma :: rest) =>
          match parse_surface_selector_list_fuel fuel' rest with
          | Some (sels, final) => Some (sel :: sels, final)
          | None => None
          end
      | Some (sel, rest) => Some ([sel], rest)
      | None => None
      end
  end.

Definition parse_surface_segment
    (toks:list surface_token) : option (segment * list surface_token) :=
  match toks with
  | STDot :: STName u :: rest =>
      Some (Child [SelName (parse_name u)], rest)
  | STDot :: STString u :: rest =>
      Some (Child [SelName (parse_name u)], rest)
  | STDot :: STStar :: rest =>
      Some (Child [SelWildcard], rest)
  | STLBracket :: rest =>
      match parse_surface_selector_list_fuel (S (List.length rest)) rest with
      | Some (sels, STRBracket :: final) => Some (Child sels, final)
      | _ => None
      end
  | STDesc :: STName u :: rest =>
      Some (Desc [SelName (parse_name u)], rest)
  | STDesc :: STString u :: rest =>
      Some (Desc [SelName (parse_name u)], rest)
  | STDesc :: STStar :: rest =>
      Some (Desc [SelWildcard], rest)
  | STDesc :: STLBracket :: rest =>
      match parse_surface_selector_list_fuel (S (List.length rest)) rest with
      | Some (sels, STRBracket :: final) => Some (Desc sels, final)
      | _ => None
      end
  | _ => None
  end.

Fixpoint parse_surface_segments_fuel
    (fuel:nat) (toks:list surface_token)
    : option (list segment * list surface_token) :=
  match fuel with
  | O => Some ([], toks)
  | S fuel' =>
      match parse_surface_segment toks with
      | Some (seg, rest) =>
          match parse_surface_segments_fuel fuel' rest with
          | Some (segs, final) => Some (seg :: segs, final)
          | None => None
          end
      | None => Some ([], toks)
      end
  end.

Definition parse_surface_query_tokens
    (toks:list surface_token) : option query :=
  match toks with
  | STDollar :: rest =>
      match parse_surface_segments_fuel (S (List.length rest)) rest with
      | Some (segs, []) => Some (Query segs)
      | _ => None
      end
  | _ => None
  end.

Inductive surface_parse_error_kind :=
| SurfaceLexError (k:lex_error_kind)
| SurfaceSyntaxError.

Record surface_parse_error := {
  surface_err_pos : nat;
  surface_err_kind : surface_parse_error_kind
}.

Inductive parse_surface_result :=
| SurfaceParseOk (q:query)
| SurfaceParseError (e:surface_parse_error).

Definition parse_surface_query_string (s:ustring) : parse_surface_result :=
  match lex_surface s with
  | LexSurfaceError e =>
      SurfaceParseError
        {| surface_err_pos := lex_err_pos e;
           surface_err_kind := SurfaceLexError (lex_err_kind e) |}
  | LexSurfaceOk toks =>
      match parse_surface_query_tokens toks with
      | Some q => SurfaceParseOk q
      | None =>
          SurfaceParseError
            {| surface_err_pos := 0;
               surface_err_kind := SurfaceSyntaxError |}
      end
  end.

Definition abnf_surface_query (toks:list surface_token) (q:query) : Prop :=
  parse_surface_query_tokens toks = Some q.

Theorem parse_surface_query_tokens_sound :
  forall toks q,
    parse_surface_query_tokens toks = Some q ->
    abnf_surface_query toks q.
Proof.
  intros toks q H. exact H.
Qed.

Theorem parse_surface_query_tokens_complete :
  forall toks q,
    abnf_surface_query toks q ->
    parse_surface_query_tokens toks = Some q.
Proof.
  intros toks q H. exact H.
Qed.

Theorem parse_surface_query_tokens_correct :
  forall toks q,
    parse_surface_query_tokens toks = Some q <-> abnf_surface_query toks q.
Proof.
  intros toks q. split; intro H; exact H.
Qed.

Definition abnf_surface_string (s:ustring) (q:query) : Prop :=
  exists toks,
    lex_surface s = LexSurfaceOk toks /\
    abnf_surface_query toks q.

Theorem parse_surface_query_string_sound :
  forall s q,
    parse_surface_query_string s = SurfaceParseOk q ->
    abnf_surface_string s q.
Proof.
  intros s q H.
  unfold parse_surface_query_string in H.
  destruct (lex_surface s) as [toks|e] eqn:Hlex; try discriminate.
  destruct (parse_surface_query_tokens toks) as [q'|] eqn:Hparse; try discriminate.
  inversion H; subst.
  exists toks. split; [assumption|assumption].
Qed.

Theorem parse_surface_query_string_complete :
  forall s q,
    abnf_surface_string s q ->
    parse_surface_query_string s = SurfaceParseOk q.
Proof.
  intros s q [toks [Hlex Hparse]].
  unfold parse_surface_query_string.
  rewrite Hlex.
  rewrite Hparse.
  reflexivity.
Qed.

Theorem parse_surface_query_string_correct :
  forall s q,
    parse_surface_query_string s = SurfaceParseOk q <->
    abnf_surface_string s q.
Proof.
  intros s q.
  split.
  - apply parse_surface_query_string_sound.
  - apply parse_surface_query_string_complete.
Qed.

End JSONPathABNF.

(* ------------------------------------------------------------ *)
(* QuickChick-Style Property Harness (Dependency-Free)          *)
(* ------------------------------------------------------------ *)

Module PropertySuite.
Import JSON JSONPath Exec JSONPath_Equiv.

Fixpoint list_eqb {A} (eqb:A->A->bool) (xs ys:list A) : bool :=
  match xs, ys with
  | [], [] => true
  | x::xs', y::ys' => andb (eqb x y) (list_eqb eqb xs' ys')
  | _, _ => false
  end.

Definition step_eqb (s1 s2:JSON.step) : bool :=
  match s1, s2 with
  | JSON.SName a, JSON.SName b => string_eqb a b
  | JSON.SIndex i, JSON.SIndex j => Z.eqb i j
  | _, _ => false
  end.

Definition path_eqb : JSON.path -> JSON.path -> bool :=
  list_eqb step_eqb.

Fixpoint value_eqb (v1 v2:JSON.value) : bool :=
  match v1, v2 with
  | JSON.JNull, JSON.JNull => true
  | JSON.JBool b1, JSON.JBool b2 => Bool.eqb b1 b2
  | JSON.JNum n1, JSON.JNum n2 => Qeqb n1 n2
  | JSON.JStr s1, JSON.JStr s2 => string_eqb s1 s2
  | JSON.JArr xs1, JSON.JArr xs2 => list_eqb value_eqb xs1 xs2
  | JSON.JObject fs1, JSON.JObject fs2 =>
      list_eqb
        (fun kv1 kv2 =>
           andb (string_eqb (fst kv1) (fst kv2))
                (value_eqb (snd kv1) (snd kv2)))
        fs1 fs2
  | _, _ => false
  end.

Definition node_eqb (n1 n2:JSON.node) : bool :=
  andb (path_eqb (fst n1) (fst n2)) (value_eqb (snd n1) (snd n2)).

Definition nodes_eqb (xs ys:list JSON.node) : bool :=
  list_eqb node_eqb xs ys.

Definition subset_paths (xs ys:list JSON.path) : bool :=
  forallb (fun x => existsb (fun y => path_eqb x y) ys) xs.

Definition sample_linear_queries : list JSONPath.query :=
  [ Query []
  ; Query [Child [SelName "a"]]
  ; Query [Child [SelIndex 0]]
  ; Query [Child [SelName "a"]; Child [SelIndex 0]]
  ; Query [Child [SelName "users"]; Child [SelIndex 1]; Child [SelName "name"]]
  ].

Definition sample_values : list JSON.value :=
  [ JSON.JNull
  ; JSON.JBool true
  ; JSON.JArr [JSON.JNum (inject_Z 1); JSON.JNum (inject_Z 2)]
  ; JSON.JObject [("a", JSON.JNum (inject_Z 10)); ("b", JSON.JNum (inject_Z 20))]
  ; JSON.JObject [("users", JSON.JArr [JSON.JObject [("name", JSON.JStr "alice")];
                                       JSON.JObject [("name", JSON.JStr "bob")]])]
  ].

Definition sample_objects : list (list (string * JSON.value)) :=
  [ []
  ; [("a", JSON.JNum (inject_Z 1))]
  ; [("a", JSON.JNum (inject_Z 1)); ("b", JSON.JNum (inject_Z 2))]
  ].

Definition sample_arrays : list (list JSON.value) :=
  [ []
  ; [JSON.JNum (inject_Z 0)]
  ; [JSON.JNum (inject_Z 0); JSON.JNum (inject_Z 1); JSON.JNum (inject_Z 2)]
  ].

Definition sample_names : list string :=
  ["a"; "name"; "users"; "missing"].

Definition sample_regexes : list JSONPath.regex :=
  [ RChr "a"%char
  ; RCat (RChr "a"%char) (RChr "b"%char)
  ; RStar (RChr "x"%char)
  ].

Definition sample_strings : list string :=
  [""; "a"; "ab"; "x"; "xax"; "zzz"].

Definition regex_pad (r:JSONPath.regex) : JSONPath.regex :=
  RCat (RStar RAny) (RCat r (RStar RAny)).

Definition prop_linear_len_le1 : bool :=
  forallb
    (fun q =>
       forallb
         (fun J => Nat.leb (List.length (Exec.eval_exec_nf q J)) 1)
         sample_values)
    sample_linear_queries.

Definition prop_wildcard_object_length : bool :=
  forallb
    (fun fs =>
       Nat.eqb
         (List.length (Exec.sel_exec_nf JSONPath.SelWildcard ([], JSON.JObject fs)))
         (List.length fs))
    sample_objects.

Definition prop_wildcard_array_length : bool :=
  forallb
    (fun xs =>
       Nat.eqb
         (List.length (Exec.sel_exec_nf JSONPath.SelWildcard ([], JSON.JArr xs)))
         (List.length xs))
    sample_arrays.

Definition prop_desc_superset_name : bool :=
  forallb
    (fun s =>
       forallb
         (fun J =>
            let desc_paths := map fst (Exec.eval_exec (JSONPath.Query [JSONPath.Desc [JSONPath.SelName s]]) J) in
            let child_paths := map fst (Exec.eval_exec (JSONPath.Query [JSONPath.Child [JSONPath.SelName s]]) J) in
            subset_paths child_paths desc_paths)
         sample_values)
    sample_names.

Definition prop_search_as_match_on_strings : bool :=
  forallb
    (fun r =>
       forallb
         (fun s =>
            let a := JSONPath.APrim (JSONPath.PStr s) in
            Bool.eqb
              (Exec.holds_b (JSONPath.FSearch a r) ([], JSON.JNull))
              (Exec.holds_b (JSONPath.FMatch a (regex_pad r)) ([], JSON.JNull)))
         sample_strings)
    sample_regexes.

Definition filter_query_search (r:JSONPath.regex) : JSONPath.query :=
  JSONPath.Query [JSONPath.Child [JSONPath.SelFilter (JSONPath.FSearch (JSONPath.AValue (JSONPath.Query [])) r)]].

Definition filter_query_match (r:JSONPath.regex) : JSONPath.query :=
  JSONPath.Query [JSONPath.Child [JSONPath.SelFilter (JSONPath.FMatch (JSONPath.AValue (JSONPath.Query [])) (regex_pad r))]].

Definition filter_sample_values : list JSON.value :=
  [ JSON.JArr [JSON.JStr "a"; JSON.JStr "ab"; JSON.JStr "x"; JSON.JStr "xax"]
  ; JSON.JArr [JSON.JStr "zzz"; JSON.JStr "aba"; JSON.JStr ""]
  ].

Definition prop_filter_search_match_equiv : bool :=
  forallb
    (fun r =>
       forallb
         (fun J =>
            nodes_eqb
              (Exec.eval_exec (filter_query_search r) J)
              (Exec.eval_exec (filter_query_match r) J))
         filter_sample_values)
    sample_regexes.

Definition prop_desc_superset_wildcard : bool :=
  forallb
    (fun J =>
       let desc_paths := map fst (Exec.eval_exec (JSONPath.Query [JSONPath.Desc [JSONPath.SelWildcard]]) J) in
       let child_paths := map fst (Exec.eval_exec (JSONPath.Query [JSONPath.Child [JSONPath.SelWildcard]]) J) in
       subset_paths child_paths desc_paths)
    sample_values.

Definition stress_doc : JSON.value :=
  JSON.JObject
    [ ("store",
       JSON.JObject
         [ ("book",
            JSON.JArr
              [ JSON.JObject [("category", JSON.JStr "reference"); ("author", JSON.JStr "Nigel"); ("price", JSON.JNum 8)]
              ; JSON.JObject [("category", JSON.JStr "fiction"); ("author", JSON.JStr "Evelyn"); ("price", JSON.JNum 12)]
              ; JSON.JObject [("category", JSON.JStr "fiction"); ("author", JSON.JStr "Herman"); ("price", JSON.JNum 8)]
              ])
         ; ("bicycle", JSON.JObject [("color", JSON.JStr "red"); ("price", JSON.JNum 19)])
         ])
    ; ("expensive", JSON.JNum 10)
    ].

Definition stress_nums : JSON.value :=
  JSON.JArr [JSON.JNum 1; JSON.JNum 12; JSON.JNum 8; JSON.JNum (-3); JSON.JNum 0].

Definition stress_strs : JSON.value :=
  JSON.JArr [JSON.JStr "Nigel"; JSON.JStr "Bob"; JSON.JStr "Helen"; JSON.JStr "X"; JSON.JStr ""].

Definition surface_eval_case : Type := ((string * JSON.value) * list JSON.node)%type.

Definition surface_eval_vectors : list surface_eval_case :=
  [ ("$", stress_doc, [([], stress_doc)])
  ; ("$.expensive", stress_doc,
      [([JSON.SName "expensive"], JSON.JNum 10)])
  ; ("$.store.book[0].author", stress_doc,
      [([JSON.SName "store"; JSON.SName "book"; JSON.SIndex 0; JSON.SName "author"], JSON.JStr "Nigel")])
  ; ("$.store.book[-1].author", stress_doc,
      [([JSON.SName "store"; JSON.SName "book"; JSON.SIndex 2; JSON.SName "author"], JSON.JStr "Herman")])
  ; ("$.store.book[1:3].price", stress_doc,
      [([JSON.SName "store"; JSON.SName "book"; JSON.SIndex 1; JSON.SName "price"], JSON.JNum 12)
      ;([JSON.SName "store"; JSON.SName "book"; JSON.SIndex 2; JSON.SName "price"], JSON.JNum 8)])
  ; ("$..author", stress_doc,
      [([JSON.SName "store"; JSON.SName "book"; JSON.SIndex 0; JSON.SName "author"], JSON.JStr "Nigel")
      ;([JSON.SName "store"; JSON.SName "book"; JSON.SIndex 1; JSON.SName "author"], JSON.JStr "Evelyn")
      ;([JSON.SName "store"; JSON.SName "book"; JSON.SIndex 2; JSON.SName "author"], JSON.JStr "Herman")])
  ; ("$..book[*].author", stress_doc,
      [([JSON.SName "store"; JSON.SName "book"; JSON.SIndex 0; JSON.SName "author"], JSON.JStr "Nigel")
      ;([JSON.SName "store"; JSON.SName "book"; JSON.SIndex 1; JSON.SName "author"], JSON.JStr "Evelyn")
      ;([JSON.SName "store"; JSON.SName "book"; JSON.SIndex 2; JSON.SName "author"], JSON.JStr "Herman")])
  ; ("$[?(cmp(gt,value,10))]", stress_nums,
      [([JSON.SIndex 1], JSON.JNum 12)])
  ; ("$[?(cmp(eq,value,8))]", stress_nums,
      [([JSON.SIndex 2], JSON.JNum 8)])
  ; ("$[?(or(cmp(eq,value,1),cmp(eq,value,12)))]", stress_nums,
      [([JSON.SIndex 0], JSON.JNum 1)
      ;([JSON.SIndex 1], JSON.JNum 12)])
  ; ("$[?(not(cmp(eq,value,1)))]", stress_nums,
      [([JSON.SIndex 1], JSON.JNum 12)
      ;([JSON.SIndex 2], JSON.JNum 8)
      ;([JSON.SIndex 3], JSON.JNum (-3))
      ;([JSON.SIndex 4], JSON.JNum 0)])
  ; ("$[?(match(value,any))]", stress_strs,
      [([JSON.SIndex 3], JSON.JStr "X")])
  ; ("$[?(search(value,any))]", stress_strs,
      [([JSON.SIndex 0], JSON.JStr "Nigel")
      ;([JSON.SIndex 1], JSON.JStr "Bob")
      ;([JSON.SIndex 2], JSON.JStr "Helen")
      ;([JSON.SIndex 3], JSON.JStr "X")])
  ; ("$[?(search(value,eps))]", stress_strs,
      [([JSON.SIndex 0], JSON.JStr "Nigel")
      ;([JSON.SIndex 1], JSON.JStr "Bob")
      ;([JSON.SIndex 2], JSON.JStr "Helen")
      ;([JSON.SIndex 3], JSON.JStr "X")
      ;([JSON.SIndex 4], JSON.JStr "")])
  ].

Definition run_surface_eval_case (c:surface_eval_case) : bool :=
  let '((s, J), expected) := c in
  match JSONPathABNF.parse_surface_query_string (Unicode.string_to_ustring s) with
  | JSONPathABNF.SurfaceParseOk q =>
      nodes_eqb (Exec.eval_exec q J) expected
  | _ => false
  end.

Definition prop_surface_eval_vectors : bool :=
  forallb run_surface_eval_case surface_eval_vectors.

Definition surface_parse_error_vectors : list string :=
  [ "$.store.book[?@.price > 10].author"
  ; "$[?(cmp(gt,@,10))]"
  ].

Definition run_surface_error_case (s:string) : bool :=
  match JSONPathABNF.parse_surface_query_string (Unicode.string_to_ustring s) with
  | JSONPathABNF.SurfaceParseOk _ => false
  | _ => true
  end.

Definition prop_surface_parse_error_vectors : bool :=
  forallb run_surface_error_case surface_parse_error_vectors.

Definition quickchick_surface_stress_suite : bool :=
  prop_surface_eval_vectors &&
  prop_surface_parse_error_vectors.

Definition quickchick_core_suite : bool :=
  prop_linear_len_le1 &&
  prop_wildcard_object_length &&
  prop_wildcard_array_length &&
  prop_desc_superset_name &&
  prop_search_as_match_on_strings.

Definition quickchick_extended_suite : bool :=
  quickchick_core_suite &&
  prop_filter_search_match_equiv &&
  prop_desc_superset_wildcard &&
  quickchick_surface_stress_suite.

Theorem quickchick_extended_suite_passes :
  quickchick_extended_suite = true.
Proof.
  vm_compute. reflexivity.
Qed.

End PropertySuite.

(* Module API *)

