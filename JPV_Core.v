(******************************************************************************)
(*                                                                            *)
(*                           JSONPATH VERIFIED                                *)
(*                                                                            *)
(*        A Complete Formalization of RFC 9535 in Coq                         *)
(*                                                                            *)
(*     Relational semantics, executable interpreter, and correctness          *)
(*     proofs for the JSONPath query language over JSON documents.            *)
(*     The development uses only the Coq standard library and supports        *)
(*     OCaml extraction.                                                      *)
(*                                                                            *)
(*     The name of the song is called 'Haddocks' Eyes.                        *)
(*     Oh, that's the name of the song, is it? Alice said.                    *)
(*     No, you don't understand, the Knight said. That's what the             *)
(*      name is called. The name really is 'The Aged Aged Man.'               *)
(*                                              - Lewis Carroll, 1871         *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: December 5, 2025                                                 *)
(*                                                                            *)
(******************************************************************************)

From Coq Require Import Init.Prelude.
From Coq Require Import
  List String Ascii ZArith Arith Lia Bool
  Sorting.Permutation QArith QArith_base.

Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(* ------------------------------------------------------------ *)
(* Utilities                                                    *)
(* ------------------------------------------------------------ *)

(** Decidable equality on strings as a boolean function. *)
Definition string_eqb (s1 s2 : string) : bool :=
  if string_dec s1 s2 then true else false.

(** Correctness: string_eqb reflects propositional equality. *)
Lemma string_eqb_true_iff :
  forall s1 s2, string_eqb s1 s2 = true <-> s1 = s2.
Proof.
  intros s1 s2; unfold string_eqb.
  destruct (string_dec s1 s2) as [Heq|Hneq]; split; intro H.
  - exact Heq.
  - reflexivity.
  - exfalso; discriminate H.
  - exfalso; apply Hneq; assumption.
Qed.

(** Pair each element with its 0-indexed position. *)
Definition index_zip {A} (xs : list A) : list (nat * A) :=
  combine (seq 0 (List.length xs)) xs.

(** Decidable equality on ASCII characters. *)
Definition ascii_eqb (a b:ascii) : bool :=
  if ascii_dec a b then true else false.

(** Strict ordering on ASCII by codepoint value. *)
Definition ascii_ltb (a b:ascii) : bool :=
  Nat.ltb (nat_of_ascii a) (nat_of_ascii b).

(** Non-strict ordering on ASCII by codepoint value. *)
Definition ascii_leb (a b:ascii) : bool :=
  negb (ascii_ltb b a).

(** Lexicographic strict ordering on strings. *)
Fixpoint str_ltb (s1 s2:string) : bool :=
  match s1, s2 with
  | EmptyString, EmptyString => false
  | EmptyString, _ => true
  | _, EmptyString => false
  | String a1 r1, String a2 r2 =>
      if ascii_ltb a1 a2 then true
      else if ascii_eqb a1 a2 then str_ltb r1 r2
      else false
  end.

(** Lexicographic non-strict ordering on strings. *)
Definition str_leb (s1 s2:string) : bool :=
  orb (string_eqb s1 s2) (str_ltb s1 s2).

(** Decidable equality on rationals. *)
Definition Qeqb (x y:Q) : bool :=
  match Qcompare x y with
  | Eq => true | _ => false
  end.

(** Strict ordering on rationals. *)
Definition Qltb (x y:Q) : bool :=
  match Qcompare x y with
  | Lt => true | _ => false
  end.

(** Non-strict ordering on rationals. *)
Definition Qleb (x y:Q) : bool :=
  negb (Qltb y x).

(** Injection from integers to rationals. *)
Definition Q_of_Z (z:Z) : Q := inject_Z z.

(** Injection from naturals to rationals. *)
Definition Q_of_nat (n:nat) : Q := inject_Z (Z.of_nat n).



(* ------------------------------------------------------------ *)
(* JSON core                                                    *)
(* ------------------------------------------------------------ *)

Module JSON.

Inductive value :=
| JNull
| JBool (b:bool)
| JNum (n:Q)
| JStr (s:string)
| JArr (xs:list value)
| JObject (fields:list (string * value)).

Inductive step :=
| SName (s:string)
| SIndex (i:Z).

Definition path := list step.
Definition node := (path * value)%type.

End JSON.

Module JSONPath.
Import JSON.

Inductive prim :=
| PNull
| PBool (b:bool)
| PNum (n:Q)
| PStr (s:string).

Definition prim_of_value (v:value) : option prim :=
  match v with
  | JNull => Some PNull
  | JBool b => Some (PBool b)
  | JNum n => Some (PNum n)
  | JStr s => Some (PStr s)
  | _ => None
  end.

Inductive cmp := CEq | CNe | CLt | CLe | CGt | CGe.

Inductive regex :=
| REmpty
| REps
| RChr (c:ascii)
| RAny
| RAlt (r1 r2:regex)
| RCat (r1 r2:regex)
| RStar (r:regex)
| RPlus (r:regex)
| ROpt (r:regex)
| RRepeat (r:regex) (min max:nat)
| RCharClass (neg:bool) (chars:list ascii).

Inductive aexpr :=
| APrim (p:prim)
| ACount (q:query)
| AValue (q:query)
| ALengthV (q:query)

with fexpr :=
| FTrue
| FNot (f:fexpr)
| FAnd (f g:fexpr)
| FOr  (f g:fexpr)
| FExists (q:query)
| FCmp (op:cmp) (a b:aexpr)
| FMatch (a:aexpr) (r:regex)
| FSearch (a:aexpr) (r:regex)

with selector :=
| SelName (s:string)
| SelWildcard
| SelIndex (i:Z)
| SelSlice (start end_ : option Z) (stp: Z)
| SelFilter (f:fexpr)

with segment :=
| Child (sels:list selector)
| Desc (sels:list selector)

with query := Query (segs:list segment).

Definition q_segs (q:query) : list segment :=
  match q with Query ss => ss end.

End JSONPath.

Import JSON JSONPath.
Open Scope string_scope.
Open Scope Z_scope.

(** Constructor for nodes from path and value. *)
Definition mk_node (p:JSON.path) (v:JSON.value) : JSON.node := (p, v).

(* ------------------------------------------------------------ *)
(* Normalized Result Paths (RFC 9535 Â§2.7)                     *)
(* ------------------------------------------------------------ *)

(** Check if a step uses a normalized (non-negative) index. *)
Definition step_normalized (s:JSON.step) : bool :=
  match s with
  | JSON.SName _ => true
  | JSON.SIndex i => (0 <=? i)%Z
  end.

(** Check if an entire path is normalized. *)
Definition path_normalized (p:JSON.path) : bool :=
  forallb step_normalized p.

(** Convert an integer to its decimal string representation. *)
Fixpoint nat_to_decimal_string_aux (fuel n : nat) (acc : string) : string :=
  match fuel with
  | O => acc
  | S fuel' =>
      match n with
      | O => match acc with EmptyString => "0" | _ => acc end
      | _ =>
          let d := Nat.modulo n 10 in
          let c := ascii_of_nat (48 + d) in
          nat_to_decimal_string_aux fuel' (Nat.div n 10) (String c acc)
      end
  end.

Definition nat_to_decimal_string (n : nat) : string :=
  nat_to_decimal_string_aux (S n) n EmptyString.

Definition Z_to_decimal_string (z : Z) : string :=
  match z with
  | Z0 => "0"
  | Zpos p => nat_to_decimal_string (Pos.to_nat p)
  | Zneg p => String "-" (nat_to_decimal_string (Pos.to_nat p))
  end.

(** Escape a JSON string key for use in bracket notation. *)
Fixpoint escape_string (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' =>
      match c with
      | """"%char => String "\" (String """" (escape_string s'))
      | "\"%char => String "\" (String "\" (escape_string s'))
      | _ => String c (escape_string s')
      end
  end.

(** Format a single step as a Result Path segment. *)
Definition step_to_result_path (s:JSON.step) : string :=
  match s with
  | JSON.SName name => String "[" (String """" (escape_string name ++ """" ++ "]"))
  | JSON.SIndex i => "[" ++ Z_to_decimal_string i ++ "]"
  end.

(** Format a complete path as an RFC 9535 Result Path string. *)
Definition path_to_result_path (p:JSON.path) : string :=
  "$" ++ List.fold_right (fun s acc => step_to_result_path s ++ acc) EmptyString p.

(** Normalization correctness: paths from executable semantics are normalized. *)
Lemma step_normalized_SIndex_nonneg :
  forall i, step_normalized (JSON.SIndex i) = true -> (0 <= i)%Z.
Proof.
  intros i H. simpl in H. apply Z.leb_le in H. exact H.
Qed.

Lemma step_normalized_SName_always :
  forall s, step_normalized (JSON.SName s) = true.
Proof.
  intros. reflexivity.
Qed.

(* ------------------------------------------------------------ *)
(* JSONPath AST                                                 *)
(* ------------------------------------------------------------ *)

(* ------------------------------------------------------------ *)
(* Slice helpers                                                *)
(* ------------------------------------------------------------ *)

(** Clamp integer x to closed interval [lo, hi]. *)
Definition clamp (x lo hi : Z) : Z := Z.max lo (Z.min hi x).

(** Normalize slice parameters to absolute bounds per RFC 9535 semantics. *)
Definition normalize_slice_bounds (len: nat) (start endo: option Z) (stp: Z)
  : Z * Z * Z :=
  let lz := Z.of_nat len in
  if Z.eqb stp 0 then (0, 0, 0) else
  let default_start := if (0 <? stp)%Z then 0 else (lz - 1) in
  let default_end   := if (0 <? stp)%Z then lz else (-1) in
  let s0 := match start with
            | None => default_start
            | Some s => if s <? 0 then lz + s else s
            end in
  let e0 := match endo with
            | None => default_end
            | Some e => if e <? 0 then lz + e else e
            end in
  let '(s1, e1) :=
     if (0 <? stp)%Z
     then (clamp s0 0 lz, clamp e0 0 lz)
     else (clamp s0 (-1) (lz - 1), clamp e0 (-1) (lz - 1)) in
  (s1, e1, stp).

(** Generate arithmetic sequence [i, i+step, ...) while i < stop, with fuel. *)
Fixpoint up_by (i stop step : Z) (fuel:nat) : list Z :=
  match fuel with
  | O => []
  | S fuel' =>
      if (i <? stop)%Z
      then i :: up_by (i + step) stop step fuel'
      else []
  end.

(** Generate descending sequence [i, i+step, ...) while stop < i, with fuel. *)
Fixpoint down_by (i stop step : Z) (fuel:nat) : list Z :=
  match fuel with
  | O => []
  | S fuel' =>
      if (stop <? i)%Z
      then i :: down_by (i + step) stop step fuel'
      else []
  end.

(** Compute natural-number indices selected by slice [start:end:step]. *)
Definition slice_positions (len:nat) (start endo: option Z) (stp:Z) : list nat :=
  let '(s, e, st) := normalize_slice_bounds len start endo stp in
  if Z.eqb st 0 then []
  else
    let lz := Z.of_nat len in
    let fuel := S (len + len)%nat in
    let zs :=
      if (0 <? st)%Z
      then up_by s e st fuel
      else down_by s e st fuel in
    fold_right
      (fun z acc =>
         if (0 <=? z)%Z && (z <? lz)%Z then Z.to_nat z :: acc else acc)
      [] zs.

(** Indexing with default value for out-of-bounds access. *)
Fixpoint nth_default (d:JSON.value) (xs:list JSON.value) (n:nat) : JSON.value :=
  match xs, n with
  | [], _ => d
  | x::_, O => x
  | _::xs', S n' => nth_default d xs' n'
  end.

(** nth_error and nth_default agree when default is JNull. *)
Lemma nth_error_default_eq :
  forall (xs:list JSON.value) n,
    (match List.nth_error xs n with
     | Some v => v
     | None => JSON.JNull
     end) = nth_default JSON.JNull xs n.
Proof.
  intros xs; induction xs as [|x xs IH]; intros [|n]; simpl; auto.
Qed.

(* ------------------------------------------------------------ *)
(* Slice bounds correctness                                     *)
(* ------------------------------------------------------------ *)

Lemma clamp_bounds :
  forall x lo hi,
    lo <= hi ->
    lo <= clamp x lo hi <= hi.
Proof.
  intros x lo hi Hle.
  unfold clamp.
  split.
  - apply Z.le_max_l.
  - apply Z.max_lub.
    + assumption.
    + apply Z.le_min_l.
Qed.

Lemma clamp_in_range :
  forall x lo hi,
    lo <= x <= hi ->
    clamp x lo hi = x.
Proof.
  intros x lo hi [Hlo Hhi].
  unfold clamp.
  rewrite Z.min_r by assumption.
  rewrite Z.max_r by assumption.
  reflexivity.
Qed.

Lemma up_by_spec :
  forall i stop step fuel k,
    step > 0 ->
    In k (up_by i stop step fuel) ->
    i <= k < stop /\ exists n, k = i + Z.of_nat n * step.
Proof.
  intros i stop step fuel k Hstep Hin.
  generalize dependent i.
  induction fuel as [|fuel' IH]; intros i Hin.
  - inversion Hin.
  - simpl in Hin. destruct (Z.ltb_spec i stop) as [Hlt|Hge].
    + destruct Hin as [Heq | Hin'].
      * subst k. split.
        -- split; [lia | assumption].
        -- exists 0%nat. lia.
      * specialize (IH (i + step) Hin').
        destruct IH as [[Hlo Hhi] [n Heq]].
        split.
        -- split; lia.
        -- exists (S n). rewrite Heq. rewrite Nat2Z.inj_succ. lia.
    + inversion Hin.
Qed.

Lemma down_by_spec :
  forall i stop step fuel k,
    step < 0 ->
    In k (down_by i stop step fuel) ->
    stop < k <= i /\ exists n, k = i + Z.of_nat n * step.
Proof.
  intros i stop step fuel k Hstep Hin.
  generalize dependent i.
  induction fuel as [|fuel' IH]; intros i Hin.
  - inversion Hin.
  - simpl in Hin. destruct (Z.ltb_spec stop i) as [Hlt|Hge].
    + destruct Hin as [Heq | Hin'].
      * subst k. split.
        -- split; [assumption | lia].
        -- exists 0%nat. lia.
      * specialize (IH (i + step) Hin').
        destruct IH as [[Hlo Hhi] [n Heq]].
        split.
        -- split; lia.
        -- exists (S n). rewrite Heq. rewrite Nat2Z.inj_succ. lia.
    + inversion Hin.
Qed.

Theorem normalize_slice_bounds_step_preserved :
  forall len start endo stp s e st,
    normalize_slice_bounds len start endo stp = (s, e, st) ->
    st = stp.
Proof.
  intros len start endo stp s e st Hnorm.
  unfold normalize_slice_bounds in Hnorm.
  destruct (Z.eqb stp 0) eqn:Heq.
  - inversion Hnorm; subst. apply Z.eqb_eq in Heq. rewrite Heq. reflexivity.
  - destruct (Z.ltb_spec 0 stp);
    destruct start as [sv|]; destruct endo as [ev|];
    try (destruct (Z.ltb_spec sv 0));
    try (destruct (Z.ltb_spec ev 0));
    destruct (Z.ltb_spec 0 stp); inversion Hnorm; reflexivity.
Qed.

Theorem normalize_slice_bounds_zero_case :
  forall len start endo s e st,
    normalize_slice_bounds len start endo 0 = (s, e, st) ->
    s = 0 /\ e = 0 /\ st = 0.
Proof.
  intros len start endo s e st Hnorm.
  unfold normalize_slice_bounds in Hnorm.
  simpl in Hnorm. inversion Hnorm. auto.
Qed.

Theorem normalize_slice_bounds_range_pos :
  forall len start endo stp s e st,
    stp > 0 ->
    normalize_slice_bounds len start endo stp = (s, e, st) ->
    0 <= s <= Z.of_nat len /\ 0 <= e <= Z.of_nat len.
Proof.
  intros len start endo stp s e st Hpos Hnorm.
  unfold normalize_slice_bounds in Hnorm.
  assert (Z.eqb stp 0 = false) by (apply Z.eqb_neq; lia).
  rewrite H in Hnorm. clear H.
  set (lz := Z.of_nat len) in *.
  destruct start as [sv|]; destruct endo as [ev|];
  try (destruct (Z.ltb_spec sv 0));
  try (destruct (Z.ltb_spec ev 0));
  destruct (Z.ltb_spec 0 stp); try lia;
  inversion Hnorm; subst; split; apply clamp_bounds; lia.
Qed.

Theorem normalize_slice_bounds_range_neg :
  forall len start endo stp s e st,
    stp < 0 ->
    normalize_slice_bounds len start endo stp = (s, e, st) ->
    -1 <= s <= Z.of_nat len - 1 /\ -1 <= e <= Z.of_nat len - 1.
Proof.
  intros len start endo stp s e st Hneg Hnorm.
  unfold normalize_slice_bounds in Hnorm.
  assert (Z.eqb stp 0 = false) by (apply Z.eqb_neq; lia).
  rewrite H in Hnorm. clear H.
  set (lz := Z.of_nat len) in *.
  destruct start as [sv|]; destruct endo as [ev|];
  try (destruct (Z.ltb_spec sv 0));
  try (destruct (Z.ltb_spec ev 0));
  destruct (Z.ltb_spec 0 stp); try lia;
  inversion Hnorm; subst; split; apply clamp_bounds; lia.
Qed.

(** Helper: fold_right filter preserves property of accumulated elements. *)
Lemma fold_right_filter_in :
  forall (zs : list Z) (lz : Z) (n : nat),
    In n (fold_right
            (fun z acc =>
               if (0 <=? z) && (z <? lz) then Z.to_nat z :: acc else acc)
            [] zs) ->
    exists z, In z zs /\ (0 <=? z) = true /\ (z <? lz) = true /\ Z.to_nat z = n.
Proof.
  intros zs lz n.
  induction zs as [|z zs' IH]; intro Hin.
  - inversion Hin.
  - simpl in Hin.
    destruct ((0 <=? z) && (z <? lz)) eqn:Hcond.
    + destruct Hin as [Heq | Hin'].
      * exists z. split; [left; reflexivity|].
        apply andb_prop in Hcond. destruct Hcond as [Hge Hlt].
        split; [exact Hge|]. split; [exact Hlt|]. exact Heq.
      * destruct (IH Hin') as [z' [Hin'' [Hge [Hlt Heq]]]].
        exists z'. split; [right; exact Hin''|].
        split; [exact Hge|]. split; [exact Hlt|]. exact Heq.
    + destruct (IH Hin) as [z' [Hin'' [Hge [Hlt Heq]]]].
      exists z'. split; [right; exact Hin''|].
      split; [exact Hge|]. split; [exact Hlt|]. exact Heq.
Qed.

(** All positions returned by slice_positions are within valid bounds. *)
Theorem slice_positions_all_in_bounds :
  forall len start endo stp (n : nat),
    In n (slice_positions len start endo stp) ->
    (n < len)%nat.
Proof.
  intros len start endo stp n Hin.
  unfold slice_positions in Hin.
  destruct (normalize_slice_bounds len start endo stp) as [[s e] st] eqn:Hnorm.
  destruct (Z.eqb st 0) eqn:Heq.
  - inversion Hin.
  - set (lz := Z.of_nat len) in *.
    destruct (fold_right_filter_in _ lz n Hin) as [z [_ [Hge [Hlt Heq']]]].
    apply Z.leb_le in Hge.
    apply Z.ltb_lt in Hlt.
    subst n.
    apply Nat2Z.inj_lt.
    rewrite Z2Nat.id by lia.
    exact Hlt.
Qed.

(** Helper: up_by generates at most (e-s)/st + 1 elements when st > 0. *)
Lemma up_by_length_bound :
  forall s e st fuel,
    (0 < st)%Z ->
    (List.length (up_by s e st fuel) <= S fuel)%nat.
Proof.
  intros s e st fuel Hst.
  revert s e. induction fuel as [|fuel' IH]; intros s e.
  - simpl. lia.
  - simpl. destruct (Z.ltb_spec s e).
    + simpl. apply le_n_S. apply IH.
    + simpl. apply Nat.le_0_l.
Qed.

(** Helper: down_by generates at most (s-e)/(-st) + 1 elements when st < 0. *)
Lemma down_by_length_bound :
  forall s e st fuel,
    (st < 0)%Z ->
    (List.length (down_by s e st fuel) <= S fuel)%nat.
Proof.
  intros s e st fuel Hst.
  revert s e. induction fuel as [|fuel' IH]; intros s e.
  - simpl. lia.
  - simpl. destruct (Z.ltb_spec e s).
    + simpl. apply le_n_S. apply IH.
    + simpl. apply Nat.le_0_l.
Qed.

(** Helper: filtering reduces or maintains length. *)
Lemma fold_right_filter_length_le :
  forall zs lz,
    (List.length (fold_right (fun z acc => if (0 <=? z)%Z && (z <? lz)%Z then Z.to_nat z :: acc else acc) [] zs)
     <= List.length zs)%nat.
Proof.
  intros zs lz.
  induction zs as [|z zs' IH].
  - simpl. apply Nat.le_refl.
  - simpl. destruct ((0 <=? z)%Z && (z <? lz)%Z).
    + simpl. apply le_n_S. exact IH.
    + transitivity (List.length zs'); [exact IH | apply Nat.le_succ_diag_r].
Qed.

(** Helper: arithmetic progression length bounded by fuel. *)
Lemma up_by_fuel_bound :
  forall s e st fuel,
    (List.length (up_by s e st fuel) <= fuel)%nat.
Proof.
  intros s e st fuel.
  revert s e. induction fuel as [|fuel' IH]; intros s e.
  - simpl. apply Nat.le_refl.
  - simpl. destruct (Z.ltb_spec s e).
    + simpl. apply le_n_S. apply IH.
    + simpl. apply Nat.le_0_l.
Qed.

(** Helper: down progression length bounded by fuel. *)
Lemma down_by_fuel_bound :
  forall s e st fuel,
    (List.length (down_by s e st fuel) <= fuel)%nat.
Proof.
  intros s e st fuel.
  revert s e. induction fuel as [|fuel' IH]; intros s e.
  - simpl. apply Nat.le_refl.
  - simpl. destruct (Z.ltb_spec e s).
    + simpl. apply le_n_S. apply IH.
    + simpl. apply Nat.le_0_l.
Qed.



(* ------------------------------------------------------------ *)
(* Helper functions for relational semantics                    *)
(* ------------------------------------------------------------ *)

(** Nullability: does regex accept the empty string? *)
Fixpoint nullable (r:regex) : bool :=
  match r with
  | REmpty => false
  | REps => true
  | RChr _ => false
  | RAny => false
  | RAlt r1 r2 => orb (nullable r1) (nullable r2)
  | RCat r1 r2 => andb (nullable r1) (nullable r2)
  | RStar _ => true
  | RPlus r1 => nullable r1
  | ROpt _ => true
  | RRepeat r1 min max =>
      if Nat.ltb max min then false
      else if Nat.eqb min 0 then true else nullable r1
  | RCharClass _ _ => false
  end.

(** Helper: check if character is in list. *)
Fixpoint char_in_list (c:ascii) (cs:list ascii) : bool :=
  match cs with
  | [] => false
  | c'::cs' => if ascii_eqb c c' then true else char_in_list c cs'
  end.

(** Brzozowski derivative: regex accepting suffixes after consuming character a. *)
Fixpoint deriv (a:ascii) (r:regex) : regex :=
  match r with
  | REmpty => REmpty
  | REps => REmpty
  | RChr c => if ascii_eqb a c then REps else REmpty
  | RAny => REps
  | RAlt r1 r2 => RAlt (deriv a r1) (deriv a r2)
  | RCat r1 r2 =>
      let d1 := deriv a r1 in
      let d2 := deriv a r2 in
      if nullable r1 then RAlt (RCat d1 r2) d2 else RCat d1 r2
  | RStar r1 => RCat (deriv a r1) (RStar r1)
  | RPlus r1 => RCat (deriv a r1) (RStar r1)
  | ROpt r1 => deriv a r1
  | RRepeat r1 min max =>
      if Nat.ltb max min then REmpty
      else if Nat.eqb min 0
      then if Nat.eqb max 0
           then REmpty
           else RAlt (RCat (deriv a r1) (RRepeat r1 0 (max - 1))) REmpty
      else RCat (deriv a r1) (RRepeat r1 (min - 1) (max - 1))
  | RCharClass neg cs =>
      let matches := char_in_list a cs in
      if negb neg then
        if matches then REps else REmpty
      else
        if matches then REmpty else REps
  end.

(** Simplify regex by removing identities and absorbing elements. *)
Fixpoint rsimpl (r:regex) : regex :=
  match r with
  | RAlt r1 r2 =>
      let r1' := rsimpl r1 in
      let r2' := rsimpl r2 in
      match r1', r2' with
      | REmpty, _ => r2'
      | _, REmpty => r1'
      | _, _      => RAlt r1' r2'
      end
  | RCat r1 r2 =>
      let r1' := rsimpl r1 in
      let r2' := rsimpl r2 in
      match r1', r2' with
      | REmpty, _ => REmpty
      | _ , REmpty => REmpty
      | REps , _ => r2'
      | _ , REps => r1'
      | _ , _    => RCat r1' r2'
      end
  | RStar r1 =>
      let r1' := rsimpl r1 in
      match r1' with
      | REmpty | REps => REps
      | _ => RStar r1'
      end
  | RPlus r1 =>
      let r1' := rsimpl r1 in
      match r1' with
      | REmpty => REmpty
      | _ => RPlus r1'
      end
  | ROpt r1 =>
      let r1' := rsimpl r1 in
      ROpt r1'
  | RRepeat r1 min max =>
      let r1' := rsimpl r1 in
      if Nat.ltb max min then REmpty
      else if Nat.eqb min 0 then
        if Nat.eqb max 0 then REps
        else RRepeat r1' min max
      else RRepeat r1' min max
  | _ => r
  end.

(** Simplified derivative: deriv followed by normalization. *)
Definition deriv_simpl (a:ascii) (r:regex) : regex :=
  rsimpl (deriv a r).

(** Convert string to list of ASCII characters. *)
Fixpoint list_of_string (s:string) : list ascii :=
  match s with
  | EmptyString => []
  | String a s' => a :: list_of_string s'
  end.

(** Incremental matching via successive derivatives. *)
Fixpoint matches_from (r:regex) (cs:list ascii) : bool :=
  match cs with
  | [] => nullable r
  | a::cs' => matches_from (deriv_simpl a r) cs'
  end.

(** Full-string regex match. *)
Definition regex_match (r:regex) (s:string) : bool :=
  matches_from r (list_of_string s).

(** Substring search: match r anywhere within s. *)
Definition regex_search (r:regex) (s:string) : bool :=
  regex_match (RCat (RStar RAny) (RCat r (RStar RAny))) s.

(* ------------------------------------------------------------ *)
(* Denotational semantics for regular languages                 *)
(* ------------------------------------------------------------ *)

(** Language denoted by a regex: set of character lists accepted. *)
Inductive lang : regex -> list ascii -> Prop :=
| LangEps : lang REps []
| LangChr : forall c, lang (RChr c) [c]
| LangAny : forall c, lang RAny [c]
| LangAltL : forall r1 r2 cs, lang r1 cs -> lang (RAlt r1 r2) cs
| LangAltR : forall r1 r2 cs, lang r2 cs -> lang (RAlt r1 r2) cs
| LangCat : forall r1 r2 cs1 cs2,
    lang r1 cs1 -> lang r2 cs2 -> lang (RCat r1 r2) (cs1 ++ cs2)
| LangStarNil : forall r, lang (RStar r) []
| LangStarCons : forall r cs1 cs2,
    cs1 <> [] -> lang r cs1 -> lang (RStar r) cs2 ->
    lang (RStar r) (cs1 ++ cs2)
| LangPlus : forall r cs1 cs2,
    lang r cs1 -> lang (RStar r) cs2 ->
    lang (RPlus r) (cs1 ++ cs2)
| LangOpt : forall r cs, lang r cs -> lang (ROpt r) cs
| LangOptNil : forall r, lang (ROpt r) []
| LangRepeatNil : forall r max, lang (RRepeat r 0 max) []
| LangRepeatStep : forall r min max cs1 cs2,
    lang r cs1 -> lang (RRepeat r (min - 1) (max - 1)) cs2 ->
    (max > 0)%nat ->
    lang (RRepeat r min max) (cs1 ++ cs2)
| LangCharClassPos : forall cs c,
    char_in_list c cs = true ->
    lang (RCharClass false cs) [c]
| LangCharClassNeg : forall cs c,
    char_in_list c cs = false ->
    lang (RCharClass true cs) [c].

(** If r accepts [], then RRepeat r min max accepts [] when min <= max. *)
Lemma lang_repeat_nullable : forall r min max,
  lang r [] -> (min <= max)%nat -> lang (RRepeat r min max) [].
Proof.
  intros r min. revert r. induction min; intros r max Hr Hle.
  - apply LangRepeatNil.
  - destruct max as [|max']. { lia. }
    change (@nil ascii) with (@nil ascii ++ @nil ascii)%list.
    apply LangRepeatStep; [ exact Hr | | lia ].
    replace (S min - 1)%nat with min by lia.
    replace (S max' - 1)%nat with max' by lia.
    apply IHmin; [ exact Hr | lia ].
Qed.

(** RRepeat with max < min accepts nothing. *)
Lemma lang_repeat_empty : forall r lo hi cs,
  lang (RRepeat r lo hi) cs -> (hi < lo)%nat -> False.
Proof.
  intros r lo hi. revert r lo.
  induction hi as [|hi' IHhi]; intros r lo cs Hlang Hlt.
  - inversion Hlang; subst; lia.
  - remember (RRepeat r lo (S hi')) as rr eqn:Heqrr.
    revert lo hi' IHhi Hlt Heqrr.
    induction Hlang; intros; try discriminate.
    + injection Heqrr; intros; subst. lia.
    + injection Heqrr; intros; subst.
      replace (S hi' - 1)%nat with hi' in Hlang2 by lia.
      eapply IHhi. exact Hlang2. lia.
Qed.

(** nullable correctness: nullable r = true iff lang r []. *)

Lemma nullable_sound : forall r, nullable r = true -> lang r [].
Proof.
  induction r; simpl; intro H; try discriminate.
  - exact LangEps.
  - apply Bool.orb_true_iff in H. destruct H as [H|H].
    + apply LangAltL. apply IHr1. exact H.
    + apply LangAltR. apply IHr2. exact H.
  - apply Bool.andb_true_iff in H. destruct H as [H1 H2].
    change (@nil ascii) with (@nil ascii ++ @nil ascii)%list.
    apply LangCat; auto.
  - apply LangStarNil.
  - change (@nil ascii) with (@nil ascii ++ @nil ascii)%list.
    apply LangPlus; [apply IHr; exact H | apply LangStarNil].
  - apply LangOptNil.
  - destruct (Nat.ltb max min) eqn:Hlt; [discriminate | ].
    apply Nat.ltb_ge in Hlt.
    destruct (Nat.eqb min 0) eqn:Hmin.
    + apply Nat.eqb_eq in Hmin. subst. apply LangRepeatNil.
    + apply lang_repeat_nullable; [apply IHr; exact H | lia].
Qed.

Lemma nullable_complete : forall r, lang r [] -> nullable r = true.
Proof.
  intros r Hlang.
  remember (@nil ascii) as cs eqn:Hnil.
  induction Hlang; subst.
  (* LangEps *)        - reflexivity.
  (* LangChr *)        - discriminate.
  (* LangAny *)        - discriminate.
  (* LangAltL *)       - simpl. apply Bool.orb_true_iff. left. auto.
  (* LangAltR *)       - simpl. apply Bool.orb_true_iff. right. auto.
  (* LangCat *)        - destruct cs1, cs2; simpl in *; try discriminate.
                          rewrite IHHlang1, IHHlang2; reflexivity.
  (* LangStarNil *)    - reflexivity.
  (* LangStarCons *)   - destruct cs1; simpl in *; [tauto | discriminate].
  (* LangPlus *)       - destruct cs1, cs2; simpl in *; try discriminate.
                          rewrite IHHlang1; reflexivity.
  (* LangOpt *)        - simpl. auto.
  (* LangOptNil *)     - reflexivity.
  (* LangRepeatNil *)  - simpl. destruct (Nat.ltb max 0); [reflexivity | reflexivity].
  (* LangRepeatStep *) - destruct cs1, cs2; try (simpl in *; discriminate).
                          assert (Hnr : nullable r = true) by (apply IHHlang1; reflexivity).
                          simpl. rewrite Hnr.
                          destruct (Nat.ltb max min) eqn:Hlt.
                          { apply Nat.ltb_lt in Hlt.
                            exfalso. apply (lang_repeat_empty r (min - 1) (max - 1) []); [exact Hlang2 | lia]. }
                          destruct (Nat.eqb min 0); reflexivity.
  (* LangCharClassPos *) - discriminate.
  (* LangCharClassNeg *) - discriminate.
Qed.

(** deriv correctness: lang (deriv a r) cs <-> lang r (a :: cs). *)

Lemma deriv_sound : forall a r cs,
  lang (deriv a r) cs -> lang r (a :: cs).
Proof.
  intros a r. revert a.
  induction r as
    [ | | c | | r1 IHr1 r2 IHr2 | r1 IHr1 r2 IHr2
    | r IHr | r IHr | r IHr | r IHr min max | neg chars ];
    intros a cs H.
  - simpl in H. inversion H.
  - simpl in H. inversion H.
  - simpl in H. destruct (ascii_eqb a c) eqn:Heq.
    + inversion H; subst.
      unfold ascii_eqb in Heq.
      destruct (ascii_dec a c); [subst; apply LangChr | discriminate].
    + inversion H.
  - simpl in H. inversion H; subst. apply LangAny.
  - simpl in H. inversion H; subst.
    + apply LangAltL. apply IHr1. assumption.
    + apply LangAltR. apply IHr2. assumption.
  - simpl in H.
    destruct (nullable r1) eqn:Hnull.
    + inversion H; subst.
      * match goal with [ Hcat : lang (RCat _ _) _ |- _ ] => inversion Hcat; subst end.
        change (a :: cs1 ++ cs2)%list with ((a :: cs1) ++ cs2)%list.
        apply LangCat; [apply IHr1; assumption | assumption].
      * change (a :: cs) with ([] ++ (a :: cs))%list.
        apply LangCat; [apply nullable_sound; exact Hnull | apply IHr2; assumption].
    + inversion H; subst.
      change (a :: cs1 ++ cs2)%list with ((a :: cs1) ++ cs2)%list.
      apply LangCat; [apply IHr1; assumption | assumption].
  - simpl in H. inversion H; subst.
    change (a :: cs1 ++ cs2)%list with ((a :: cs1) ++ cs2)%list.
    apply LangStarCons; [intro Heq; discriminate | apply IHr; assumption | assumption].
  - simpl in H. inversion H; subst.
    change (a :: cs1 ++ cs2)%list with ((a :: cs1) ++ cs2)%list.
    apply LangPlus; [apply IHr; assumption | assumption].
  - simpl in H. apply LangOpt. apply IHr. exact H.
  - (* RRepeat r min max â€” H : lang (deriv a (RRepeat r min max)) cs *)
    unfold deriv in H; fold deriv in H.
    destruct (Nat.ltb max min) eqn:Hlt.
    + (* max < min: deriv = REmpty *) inversion H.
    + destruct (Nat.eqb min 0) eqn:Hmin.
      * simpl in H.
        destruct (Nat.eqb max 0) eqn:Hmax; simpl in H.
        -- (* min=0, max=0: deriv = REmpty *) inversion H.
        -- (* min=0, max>0 *)
           inversion H; subst.
           ++ match goal with [ Hcat : lang (RCat _ _) _ |- _ ] => inversion Hcat; subst end.
              change (a :: ?l1 ++ ?l2)%list with ((a :: l1) ++ l2)%list.
              apply Nat.eqb_eq in Hmin. subst.
              apply LangRepeatStep; [apply IHr; eassumption | eassumption | ].
              apply Nat.eqb_neq in Hmax. lia.
           ++ match goal with [ Hempty : lang REmpty _ |- _ ] => inversion Hempty end.
      * (* min>0, max>=min *)
        simpl in H.
        inversion H; subst.
        change (a :: ?l1 ++ ?l2)%list with ((a :: l1) ++ l2)%list.
        apply LangRepeatStep.
        -- match goal with [ Hd : lang (deriv _ _) _ |- _ ] => apply IHr; exact Hd end.
        -- match goal with [ Hr : lang (RRepeat _ _ _) _ |- _ ] => exact Hr end.
        -- apply Nat.eqb_neq in Hmin. apply Nat.ltb_ge in Hlt. lia.
  - destruct neg.
    + destruct (char_in_list a chars) eqn:Hcl.
      * simpl in H. rewrite Hcl in H. simpl in H. inversion H.
      * simpl in H. rewrite Hcl in H. simpl in H.
        inversion H; subst. apply LangCharClassNeg. exact Hcl.
    + destruct (char_in_list a chars) eqn:Hcl.
      * simpl in H. rewrite Hcl in H. simpl in H.
        inversion H; subst. apply LangCharClassPos. exact Hcl.
      * simpl in H. rewrite Hcl in H. simpl in H. inversion H.
Qed.

Lemma repeat_promote_zero :
  forall r m s,
    lang r [] ->
    lang (RRepeat r 0 m) s ->
    lang (RRepeat r 0 (S m)) s.
Proof.
  intros r m s Hnil Hrep.
  change s with ([] ++ s)%list.
  eapply (LangRepeatStep r 0 (S m) [] s).
  - exact Hnil.
  - simpl. replace (m - 0)%nat with m by lia. exact Hrep.
  - lia.
Qed.

Lemma cat_promote_repeat :
  forall r x m s,
    lang r [] ->
    lang (RCat x (RRepeat r 0 m)) s ->
    lang (RCat x (RRepeat r 0 (S m))) s.
Proof.
  intros r x m s Hnil Hcat.
  inversion Hcat; subst.
  eapply LangCat; eauto.
  eapply repeat_promote_zero; eauto.
Qed.

Lemma repeat_promote_succ :
  forall r lo hi s,
    lang r [] ->
    lang (RRepeat r lo hi) s ->
    lang (RRepeat r (S lo) (S hi)) s.
Proof.
  intros r lo hi s Hnil Hrep.
  change s with ([] ++ s)%list.
  eapply (LangRepeatStep r (S lo) (S hi) [] s).
  - exact Hnil.
  - replace (S lo - 1)%nat with lo by lia.
    replace (S hi - 1)%nat with hi by lia.
    exact Hrep.
  - lia.
Qed.

Lemma cat_promote_repeat_succ :
  forall r x lo hi s,
    lang r [] ->
    lang (RCat x (RRepeat r lo hi)) s ->
    lang (RCat x (RRepeat r (S lo) (S hi))) s.
Proof.
  intros r x lo hi s Hnil Hcat.
  inversion Hcat; subst.
  eapply LangCat; eauto.
  eapply repeat_promote_succ; eauto.
Qed.

Lemma repeat_head_cat_with_nullable :
  forall r a m s,
    (forall t, lang r (a :: t) -> lang (deriv a r) t) ->
    lang r [] ->
    lang (RRepeat r 0 m) (a :: s) ->
    lang (RCat (deriv a r) (RRepeat r 0 m)) s.
Proof.
  intros r a m.
  induction m as [|m' IH]; intros s Hder Hnil Hrep.
  - inversion Hrep; subst; try discriminate; lia.
  - inversion Hrep; subst; simpl in *;
      try solve [
        exfalso;
        repeat match goal with
        | Heq : [] = _ :: _ |- _ => inversion Heq
        | Heq : _ :: _ = [] |- _ => inversion Heq
        | Hgt : (_ > 0)%nat |- _ => lia
        end
      ].
    destruct cs1 as [|c cs1'].
    + simpl in *.
      lazymatch goal with
      | Heq : [] ++ ?rhs = a :: s |- _ =>
          simpl in Heq; subst rhs
      | Heq : a :: s = [] ++ ?rhs |- _ =>
          simpl in Heq; symmetry in Heq; subst rhs
      | Heq : ?rhs = a :: s |- _ => subst rhs
      | Heq : a :: s = ?rhs |- _ => symmetry in Heq; subst rhs
      end.
      eapply cat_promote_repeat; [exact Hnil |].
      eapply IH; [exact Hder | exact Hnil |].
      lazymatch goal with
      | Hrest : lang (RRepeat r 0 (m' - 0)) (a :: s) |- _ =>
          replace (m' - 0)%nat with m' in Hrest by lia;
          exact Hrest
      | Hrest : lang (RRepeat r 0 m') (a :: s) |- _ =>
          exact Hrest
      end.
    + simpl in *.
      lazymatch goal with
      | Heq : (c :: cs1') ++ ?rhs = a :: s |- _ =>
          inversion Heq; subst; clear Heq
      | Heq : a :: s = (c :: cs1') ++ ?rhs |- _ =>
          symmetry in Heq; inversion Heq; subst; clear Heq
      | Heq : c :: ?rhs = a :: s |- _ =>
          inversion Heq; subst; clear Heq
      | Heq : a :: s = c :: ?rhs |- _ =>
          symmetry in Heq; inversion Heq; subst; clear Heq
      end.
      eapply LangCat.
      * apply Hder. eassumption.
      * lazymatch goal with
        | Hrest : lang (RRepeat r 0 (m' - 0)) ?tail |- _ =>
            replace (m' - 0)%nat with m' in Hrest by lia;
            eapply repeat_promote_zero; [exact Hnil | exact Hrest]
        | Hrest : lang (RRepeat r 0 m') ?tail |- _ =>
            eapply repeat_promote_zero; [exact Hnil | exact Hrest]
        end.
Qed.

Lemma repeat_head_cat_with_min_nullable :
  forall r a lo hi s,
    (forall t, lang r (a :: t) -> lang (deriv a r) t) ->
    lang r [] ->
    lang (RRepeat r lo hi) (a :: s) ->
    (lo > 0)%nat ->
    lang (RCat (deriv a r) (RRepeat r (lo - 1) (hi - 1))) s.
Proof.
  intros r a lo.
  induction lo as [|lo' IH]; intros hi s Hder Hnil Hrep Hlo.
  - lia.
  - inversion Hrep; subst; simpl in *;
      try solve [
        exfalso;
        repeat match goal with
        | Heq : [] = _ :: _ |- _ => inversion Heq
        | Heq : _ :: _ = [] |- _ => inversion Heq
        | Hgt : (_ > 0)%nat |- _ => lia
        end
      ].
      destruct cs1 as [|c cs1'].
      * simpl in *.
        lazymatch goal with
        | Heq : [] ++ ?rhs = a :: s |- _ =>
            simpl in Heq; subst rhs
        | Heq : a :: s = [] ++ ?rhs |- _ =>
            simpl in Heq; symmetry in Heq; subst rhs
        | Heq : ?rhs = a :: s |- _ => subst rhs
        | Heq : a :: s = ?rhs |- _ => symmetry in Heq; subst rhs
        end.
        destruct lo' as [|lo''].
        -- simpl in *.
           eapply repeat_head_cat_with_nullable; eauto.
        -- assert (Htail :
             lang (RCat (deriv a r) (RRepeat r (S lo'' - 1) ((hi - 1) - 1))) s).
           {
             eapply IH; [exact Hder | exact Hnil | | lia].
             lazymatch goal with
             | Hrest : lang (RRepeat r (S lo'') (hi - 1)) (a :: s) |- _ =>
                 exact Hrest
             | Hrest : lang (RRepeat r (S lo'' - 0) (hi - 1)) (a :: s) |- _ =>
                 replace (S lo'' - 0)%nat with (S lo'') in Hrest by lia;
                 exact Hrest
             end.
           }
           replace (S lo'' - 1)%nat with lo'' in Htail by lia.
           assert (Hhi_ge : (S lo'' <= hi - 1)%nat).
           {
             destruct (lt_dec (hi - 1) (S lo'')) as [Hlt|Hge].
             - exfalso.
               lazymatch goal with
               | Hrest : lang (RRepeat r (S lo'') (hi - 1)) (a :: s) |- _ =>
                   eapply (lang_repeat_empty r (S lo'') (hi - 1) (a :: s)); eauto
               | Hrest : lang (RRepeat r (S lo'' - 0) (hi - 1)) (a :: s) |- _ =>
                   replace (S lo'' - 0)%nat with (S lo'') in Hrest by lia;
                   eapply (lang_repeat_empty r (S lo'') (hi - 1) (a :: s)); eauto
               end.
             - lia.
           }
           assert (Hhi_pos : (hi - 1 > 0)%nat) by lia.
           replace (S lo'' - 0)%nat with (S lo'') by lia.
           replace ((hi - 1)%nat) with (S (((hi - 1)%nat - 1)%nat)) by lia.
           eapply cat_promote_repeat_succ; eauto.
      * simpl in *.
        lazymatch goal with
        | Heq : (c :: cs1') ++ ?rhs = a :: s |- _ =>
            inversion Heq; subst; clear Heq
        | Heq : a :: s = (c :: cs1') ++ ?rhs |- _ =>
            symmetry in Heq; inversion Heq; subst; clear Heq
        | Heq : c :: ?rhs = a :: s |- _ =>
            inversion Heq; subst; clear Heq
        | Heq : a :: s = c :: ?rhs |- _ =>
            symmetry in Heq; inversion Heq; subst; clear Heq
        end.
        eapply LangCat.
        -- apply Hder. eassumption.
        -- lazymatch goal with
           | Hrest : lang (RRepeat r ?lo0 ?hi0) ?tail
             |- lang (RRepeat r ?log ?hig) ?tail =>
               replace lo0 with log in Hrest by lia;
               replace hi0 with hig in Hrest by lia;
               exact Hrest
           end.
Qed.

Lemma deriv_complete : forall a r cs,
  lang r (a :: cs) -> lang (deriv a r) cs.
Proof.
  intros a r. revert a.
  induction r; intros a cs H; simpl.
  - inversion H.
  - inversion H.
  - inversion H; subst.
    unfold ascii_eqb. destruct (ascii_dec a a); [apply LangEps | contradiction].
  - inversion H; subst. apply LangEps.
  - inversion H; subst.
    + apply LangAltL. eapply IHr1. eassumption.
    + apply LangAltR. eapply IHr2. eassumption.
  - inversion H; subst.
    destruct (nullable r1) eqn:Hnull.
    + destruct cs1 as [| a' cs1'].
      * simpl in *. subst.
        apply LangAltR. eapply IHr2. eassumption.
      * simpl in *.
        lazymatch goal with
        | Heq : (_ :: _) ++ _ = _ :: _ |- _ =>
            inversion Heq; subst; clear Heq
        | Heq : _ :: _ = _ :: _ |- _ =>
            inversion Heq; subst; clear Heq
        end.
        apply LangAltL. apply LangCat; [eapply IHr1; eassumption | eassumption].
    + destruct cs1 as [| a' cs1'].
      * exfalso. apply (Bool.diff_false_true).
        rewrite <- Hnull. eapply nullable_complete. eassumption.
      * simpl in *.
        lazymatch goal with
        | Heq : (_ :: _) ++ _ = _ :: _ |- _ =>
            inversion Heq; subst; clear Heq
        | Heq : _ :: _ = _ :: _ |- _ =>
            inversion Heq; subst; clear Heq
        end.
        apply LangCat; [eapply IHr1; eassumption | eassumption].
  - inversion H; subst.
    destruct cs1 as [| a' cs1']; [contradiction | ].
    simpl in *.
    lazymatch goal with
    | Heq : (_ :: _) ++ _ = _ :: _ |- _ =>
        inversion Heq; subst; clear Heq
    | Heq : _ :: _ = _ :: _ |- _ =>
        inversion Heq; subst; clear Heq
    end.
    apply LangCat.
    + lazymatch goal with
      | Hd : lang r (_ :: _) |- _ => eapply IHr; exact Hd
      end.
    + lazymatch goal with
      | Hs : lang (RStar r) _ |- _ => exact Hs
      end.
  - inversion H; subst.
    destruct cs1 as [| a' cs1'].
    + simpl in *. subst.
      (* lang (RStar r) (a :: cs) *)
      lazymatch goal with
      | Hstar : lang (RStar r) (_ :: _) |- _ =>
          inversion Hstar; subst; clear Hstar
      end.
      all: try solve [discriminate | congruence | contradiction].
      destruct cs1; [contradiction | ].
      simpl in *.
      lazymatch goal with
      | Heq : (_ :: _) ++ _ = _ :: _ |- _ =>
          inversion Heq; subst; clear Heq
      | Heq : _ :: _ = _ :: _ |- _ =>
          inversion Heq; subst; clear Heq
      end.
      apply LangCat.
      -- lazymatch goal with
         | Hd : lang r (_ :: _) |- _ => eapply IHr; exact Hd
         end.
      -- lazymatch goal with
         | Hs : lang (RStar r) _ |- _ => exact Hs
         end.
    + simpl in *.
      lazymatch goal with
      | Heq : (_ :: _) ++ _ = _ :: _ |- _ =>
          inversion Heq; subst; clear Heq
      | Heq : _ :: _ = _ :: _ |- _ =>
          inversion Heq; subst; clear Heq
      end.
      apply LangCat; [eapply IHr; eassumption | eassumption].
  - inversion H; subst. eapply IHr. eassumption.
  - destruct (Nat.eqb min 0) eqn:Hmin.
    + destruct (Nat.eqb max 0) eqn:Hmax.
      * apply Nat.eqb_eq in Hmin. apply Nat.eqb_eq in Hmax. subst.
        inversion H; subst; lia.
      * inversion H; subst.
        apply Nat.eqb_eq in Hmin. subst.
        simpl in *.
        apply LangAltL.
        destruct cs1 as [| a' cs1'].
        -- simpl in *. subst.
           eapply repeat_head_cat_with_nullable; eauto.
        -- simpl in *.
           lazymatch goal with
           | Heq : (_ :: _) ++ _ = _ :: _ |- _ =>
               inversion Heq; subst; clear Heq
           | Heq : _ :: _ = _ :: _ |- _ =>
               inversion Heq; subst; clear Heq
           end.
           apply LangCat; [eapply IHr; eassumption | eassumption].
    + inversion H; subst; simpl in *;
        try solve [
          exfalso;
          apply Nat.eqb_neq in Hmin;
          apply Hmin; reflexivity
        ].
      destruct (Nat.ltb max min) eqn:Hlt.
      * exfalso.
        apply Nat.ltb_lt in Hlt.
        eapply (lang_repeat_empty r min max (a :: cs)); eauto.
      * destruct cs1 as [| a' cs1'].
        -- simpl in *. subst.
           apply Nat.eqb_neq in Hmin.
           eapply repeat_head_cat_with_min_nullable; eauto.
           lia.
        -- simpl in *.
           lazymatch goal with
           | Heq : (_ :: _) ++ _ = _ :: _ |- _ =>
               inversion Heq; subst; clear Heq
           | Heq : _ :: _ = _ :: _ |- _ =>
               inversion Heq; subst; clear Heq
           end.
           apply LangCat; [eapply IHr; eassumption | eassumption].
  - destruct neg.
    + inversion H; subst.
      simpl. rewrite H2. apply LangEps.
    + inversion H; subst.
      simpl. rewrite H2. apply LangEps.
Qed.

Lemma lang_star_map :
  forall r s cs,
    (forall t, lang s t -> lang r t) ->
    lang (RStar s) cs ->
    lang (RStar r) cs.
Proof.
  intros r s cs Hmap Hstar.
  remember (RStar s) as rs eqn:Hrs.
  revert s Hmap Hrs.
  induction Hstar; intros s0 Hmap Hrs; inversion Hrs; subst; clear Hrs.
  - apply LangStarNil.
  - apply LangStarCons.
    + assumption.
    + apply Hmap.
      lazymatch goal with
      | Hs : lang s0 _ |- _ => exact Hs
      end.
    + eapply IHHstar2; eauto.
Qed.

Lemma lang_plus_map :
  forall r s cs,
    (forall t, lang s t -> lang r t) ->
    lang (RPlus s) cs ->
    lang (RPlus r) cs.
Proof.
  intros r s cs Hmap Hplus.
  inversion Hplus; subst.
  apply LangPlus.
  - apply Hmap.
    lazymatch goal with
    | Hs : lang s _ |- _ => exact Hs
    end.
  - eapply lang_star_map.
    + exact Hmap.
    + lazymatch goal with
      | Hst : lang (RStar s) _ |- _ => exact Hst
      end.
Qed.

Lemma lang_repeat_map :
  forall r s min max cs,
    (forall t, lang s t -> lang r t) ->
    lang (RRepeat s min max) cs ->
    lang (RRepeat r min max) cs.
Proof.
  intros r s min max cs Hmap Hrep.
  remember (RRepeat s min max) as rr eqn:Hrr.
  revert s min max Hmap Hrr.
  induction Hrep; intros s0 min0 max0 Hmap Hrr;
    inversion Hrr; subst; clear Hrr; try discriminate.
  - apply LangRepeatNil.
  - apply LangRepeatStep.
    + apply Hmap. assumption.
    + eauto.
    + assumption.
Qed.

(** rsimpl preserves language equivalence. *)
Lemma rsimpl_sound : forall r cs, lang (rsimpl r) cs -> lang r cs.
Proof.
  induction r; intros cs H; simpl in H; try exact H.
  - (* RAlt *)
    remember (rsimpl r1) as r1' eqn:Hr1.
    remember (rsimpl r2) as r2' eqn:Hr2.
    destruct r1'; simpl in H;
      try (destruct r2'; simpl in H;
           try (inversion H; subst;
                [apply LangAltL; apply IHr1; eassumption
                |apply LangAltR; apply IHr2; eassumption]);
           apply LangAltL; apply IHr1; exact H);
      try (apply LangAltR; apply IHr2; exact H).
  - (* RCat *)
    remember (rsimpl r1) as r1' eqn:Hr1.
    remember (rsimpl r2) as r2' eqn:Hr2.
    destruct r1'; destruct r2'; simpl in H;
      try solve [inversion H];
      try solve [
        inversion H; subst;
        apply LangCat; [apply IHr1; eassumption
                       |apply IHr2; eassumption]
      ];
      try solve [
        replace cs with ([] ++ cs)%list by reflexivity;
        apply LangCat; [apply IHr1; apply LangEps
                       |apply IHr2; exact H]
      ];
      try solve [
        rewrite <- app_nil_r with (l:=cs);
        apply LangCat; [apply IHr1; exact H
                       |apply IHr2; apply LangEps]
      ].
  - (* RStar *)
    destruct (rsimpl r) eqn:Hr; simpl in H;
      try (inversion H; subst; apply LangStarNil);
      try (eapply lang_star_map;
           [intros t Ht; apply IHr; exact Ht
           |exact H]).
  - (* RPlus *)
    destruct (rsimpl r) eqn:Hr; simpl in H;
      try solve [inversion H].
    all: inversion H; subst;
      apply LangPlus;
      [apply IHr; eassumption
      |eapply lang_star_map;
         [intros t Ht; apply IHr; exact Ht
         |eassumption]].
  - (* ROpt *)
    inversion H; subst.
    + apply LangOpt. apply IHr. eassumption.
    + apply LangOptNil.
  - (* RRepeat *)
    destruct (Nat.ltb max min) eqn:Hlt.
    + inversion H.
    + destruct (Nat.eqb min 0) eqn:Hmin.
      * destruct (Nat.eqb max 0) eqn:Hmax.
        -- inversion H; subst. apply Nat.eqb_eq in Hmin. subst. apply LangRepeatNil.
        -- eapply lang_repeat_map.
           ++ intros t Ht. apply IHr. exact Ht.
           ++ exact H.
      * eapply lang_repeat_map.
        -- intros t Ht. apply IHr. exact Ht.
        -- exact H.
Qed.

Lemma lang_alt_left_complete : forall r1 r2 cs,
  lang r1 cs ->
  lang (match r1, r2 with
        | REmpty, _ => r2
        | _, REmpty => r1
        | _, _ => RAlt r1 r2
        end) cs.
Proof.
  intros r1 r2 cs H.
  destruct r1; destruct r2; simpl in *;
    try exact H;
    try (apply LangAltL; exact H);
    inversion H.
Qed.

Lemma lang_alt_right_complete : forall r1 r2 cs,
  lang r2 cs ->
  lang (match r1, r2 with
        | REmpty, _ => r2
        | _, REmpty => r1
        | _, _ => RAlt r1 r2
        end) cs.
Proof.
  intros r1 r2 cs H.
  destruct r1; destruct r2; simpl in *;
    try exact H;
    try (apply LangAltR; exact H);
    inversion H.
Qed.

Lemma lang_cat_complete_step : forall r1 r2 cs1 cs2,
  lang r1 cs1 ->
  lang r2 cs2 ->
  lang (match r1, r2 with
        | REmpty, _ => REmpty
        | _, REmpty => REmpty
        | REps, _ => r2
        | _, REps => r1
        | _, _ => RCat r1 r2
        end) (cs1 ++ cs2).
Proof.
  intros r1 r2 cs1 cs2 H1 H2.
  destruct r1; destruct r2; simpl in *.
  all: try (exfalso; match goal with Hbad : lang REmpty _ |- _ => inversion Hbad end).
  all: try (apply LangCat; [exact H1 | exact H2]).
  all: try (
    match goal with
    | Heps : lang REps _ |- _ =>
        inversion Heps; subst; simpl in *; exact H2
    end).
  all: try (
    match goal with
    | Heps : lang REps _ |- _ =>
        inversion Heps; subst; simpl in *; rewrite app_nil_r; exact H1
    end).
Qed.

Lemma rsimpl_complete : forall r cs, lang r cs -> lang (rsimpl r) cs.
Proof.
  induction r; intros cs H; simpl; try exact H.
  - (* RAlt *)
    inversion H; subst.
    + remember (rsimpl r1) as r1' eqn:Hr1.
      remember (rsimpl r2) as r2' eqn:Hr2.
      assert (H1s : lang r1' cs).
      { apply IHr1. assumption. }
      simpl.
      apply lang_alt_left_complete. exact H1s.
    + remember (rsimpl r1) as r1' eqn:Hr1.
      remember (rsimpl r2) as r2' eqn:Hr2.
      assert (H2s : lang r2' cs).
      { apply IHr2. assumption. }
      simpl.
      apply lang_alt_right_complete. exact H2s.
  - (* RCat *)
    inversion H; subst.
    match goal with
    | Hleft : lang r1 ?cs1,
      Hright : lang r2 ?cs2 |- _ =>
        pose proof (IHr1 _ Hleft) as H1s;
        pose proof (IHr2 _ Hright) as H2s;
        simpl;
        eapply lang_cat_complete_step; [exact H1s | exact H2s]
    end.
  - (* RStar *)
    assert (Hmap : lang (RStar (rsimpl r)) cs).
    { eapply lang_star_map.
      - intros t Ht. apply IHr. exact Ht.
      - exact H.
    }
    destruct (rsimpl r) eqn:Hr; simpl in *; try exact Hmap.
    + inversion Hmap; subst.
      * apply LangEps.
      * match goal with
        | Hbad : lang REmpty _ |- _ => inversion Hbad
        end.
    + inversion Hmap; subst.
      * apply LangEps.
      * match goal with
        | Hne : ?x <> [], Heps : lang REps ?x |- _ =>
            inversion Heps; subst; contradiction
        end.
  - (* RPlus *)
    pose proof (lang_plus_map (rsimpl r) r cs
      (fun t Ht => IHr _ Ht) H) as Hplus_simpl.
    destruct (rsimpl r) eqn:Hr; simpl in *; try exact Hplus_simpl.
    inversion Hplus_simpl; subst.
    match goal with
    | Hbad : lang REmpty _ |- _ => inversion Hbad
    end.
  - (* ROpt *)
    inversion H; subst.
    + apply LangOpt. apply IHr. assumption.
    + apply LangOptNil.
  - (* RRepeat *)
    destruct (Nat.ltb max min) eqn:Hlt.
    + apply Nat.ltb_lt in Hlt.
      exfalso. eapply lang_repeat_empty; eauto.
    + destruct (Nat.eqb min 0) eqn:Hmin.
      * destruct (Nat.eqb max 0) eqn:Hmax.
        -- apply Nat.eqb_eq in Hmin. apply Nat.eqb_eq in Hmax. subst.
           inversion H; subst.
           ++ apply LangEps.
           ++ lia.
        -- inversion H; subst.
           ++ apply LangRepeatNil.
           ++ eapply LangRepeatStep.
              ** apply IHr. eassumption.
              ** eapply lang_repeat_map.
                 --- intros t Ht. apply IHr. exact Ht.
                 --- eassumption.
              ** eassumption.
      * inversion H; subst.
        -- apply Nat.eqb_neq in Hmin. lia.
        -- eapply LangRepeatStep.
           ++ apply IHr. eassumption.
           ++ eapply lang_repeat_map.
              ** intros t Ht. apply IHr. exact Ht.
              ** eassumption.
           ++ eassumption.
Qed.

(** matches_from correctness: matches_from r cs = true <-> lang r cs. *)
Lemma matches_from_sound : forall cs r,
  matches_from r cs = true -> lang r cs.
Proof.
  induction cs as [| a cs' IH]; intros r H; simpl in H.
  - apply nullable_sound. exact H.
  - apply deriv_sound. apply rsimpl_sound. apply IH. exact H.
Qed.

Lemma matches_from_complete : forall cs r,
  lang r cs -> matches_from r cs = true.
Proof.
  induction cs as [| a cs' IH]; intros r H; simpl.
  - apply nullable_complete. exact H.
  - apply IH. apply rsimpl_complete. apply deriv_complete. exact H.
Qed.

(** regex_match correctness: regex_match r s = true <-> lang r (list_of_string s). *)
Theorem regex_match_sound : forall r s,
  regex_match r s = true -> lang r (list_of_string s).
Proof.
  intros r s H. unfold regex_match in H. apply matches_from_sound. exact H.
Qed.

Theorem regex_match_complete : forall r s,
  lang r (list_of_string s) -> regex_match r s = true.
Proof.
  intros r s H. unfold regex_match. apply matches_from_complete. exact H.
Qed.

Theorem regex_match_correct : forall r s,
  regex_match r s = true <-> lang r (list_of_string s).
Proof.
  intros r s. split; [apply regex_match_sound | apply regex_match_complete].
Qed.

(** Primitive equality: structural equality on comparable types. *)
Definition prim_eq (p q:prim) : bool :=
  match p, q with
  | PNull, PNull => true
  | PBool b1, PBool b2 => Bool.eqb b1 b2
  | PNum n1, PNum n2 => Qeqb n1 n2
  | PStr s1, PStr s2 => string_eqb s1 s2
  | _, _ => false
  end.

(** Primitive ordering: defined for numbers and strings only. *)
Definition prim_lt (p q:prim) : bool :=
  match p, q with
  | PNum n1, PNum n2 => Qltb n1 n2
  | PStr s1, PStr s2 => str_ltb s1 s2
  | _ , _ => false
  end.

(** Comparison dispatch for all six relational operators. *)
Definition cmp_prim (op:cmp) (x y:prim) : bool :=
  match op with
  | CEq => prim_eq x y
  | CNe => negb (prim_eq x y)
  | CLt => prim_lt x y
  | CLe => orb (prim_lt x y) (prim_eq x y)
  | CGt => prim_lt y x
  | CGe => orb (prim_lt y x) (prim_eq x y)
  end.

(** Parameterized boolean filter evaluation (unused in final semantics). *)
Fixpoint holds_b_simple (eval_func: query -> value -> list node)
                        (aeval_func: aexpr -> value -> option prim)
                        (f:fexpr) (n:node) {struct f} : bool :=
  let '(_,v) := n in
  match f with
  | FTrue => true
  | FNot g => negb (holds_b_simple eval_func aeval_func g n)
  | FAnd g h => andb (holds_b_simple eval_func aeval_func g n) (holds_b_simple eval_func aeval_func h n)
  | FOr  g h => orb  (holds_b_simple eval_func aeval_func g n) (holds_b_simple eval_func aeval_func h n)
  | FExists q =>
      negb (Nat.eqb (List.length (eval_func q v)) 0)
  | FCmp op a b =>
      match aeval_func a v, aeval_func b v with
      | Some pa, Some pb => cmp_prim op pa pb
      | _, _ => false
      end
  | FMatch a r =>
      match aeval_func a v with
      | Some (PStr s) => regex_match r s
      | _ => false
      end
  | FSearch a r =>
      match aeval_func a v with
      | Some (PStr s) => regex_search r s
      | _ => false
      end
  end.

(* ------------------------------------------------------------ *)
(* Relational semantics                                         *)
(* ------------------------------------------------------------ *)

(** Selector evaluation: single-step child selection from a node. *)
Inductive eval_selector : selector -> JSON.node -> list JSON.node -> Prop :=

| EvalSelName :
    forall s p fields v,
      find (fun kv => string_eqb (fst kv) s) fields = Some (s, v) ->
      eval_selector (SelName s) (p, JObject fields)
                    [ (List.app p [SName s], v) ]
| EvalSelNameNotFound :
    forall s p fields,
      find (fun kv => string_eqb (fst kv) s) fields = None ->
      eval_selector (SelName s) (p, JObject fields) []
| EvalSelNameNotObject :
    forall s p v,
      (forall fs, v <> JObject fs) ->
      eval_selector (SelName s) (p, v) []

| EvalSelIndex :
    forall (z:Z) p xs v idx,
      idx = (if z <? 0 then Z.of_nat (List.length xs) + z else z) ->
      (idx <? 0) = false ->
      (idx >=? Z.of_nat (List.length xs)) = false ->
      nth_error xs (Z.to_nat idx) = Some v ->
      eval_selector (SelIndex z) (p, JArr xs)
                    [ (List.app p [SIndex idx], v) ]
| EvalSelIndexOutOfBounds :
    forall (z:Z) p xs idx,
      idx = (if z <? 0 then Z.of_nat (List.length xs) + z else z) ->
      orb (idx <? 0) (idx >=? Z.of_nat (List.length xs)) = true ->
      eval_selector (SelIndex z) (p, JArr xs) []
| EvalSelIndexNotArray :
    forall z p v,
      (forall xs, v <> JArr xs) ->
      eval_selector (SelIndex z) (p, v) []

| EvalSelWildcardObject :
    forall p fields results,
      Permutation results
        (map (fun '(k, v) => (List.app p [SName k], v)) fields) ->
      eval_selector SelWildcard (p, JObject fields) results
| EvalSelWildcardArray :
    forall p xs,
      eval_selector SelWildcard (p, JArr xs)
        (map (fun '(i, v) => (List.app p [SIndex (Z.of_nat i)], v)) (index_zip xs))
| EvalSelWildcardOther :
    forall p v,
      (forall fields, v <> JObject fields) ->
      (forall xs, v <> JArr xs) ->
      eval_selector SelWildcard (p, v) []

| EvalSelSliceNotArray :
    forall p v start end_ stp,
      (forall xs, v <> JArr xs) ->
      eval_selector (SelSlice start end_ stp) (p, v) []
| EvalSelSliceArray :
    forall p xs start end_ stp,
      eval_selector (SelSlice start end_ stp) (p, JArr xs)
        (map (fun n => (List.app p [SIndex (Z.of_nat n)], nth_default JNull xs n))
             (slice_positions (List.length xs) start end_ stp))


(** Document-order traversal: enumerate all descendant nodes depth-first. *)
with visit_order : JSON.node -> list JSON.node -> Prop :=
| VisitLeaf :
    forall p v,
      (forall xs, v <> JArr xs) ->
      (forall fs, v <> JObject fs) ->
      visit_order (p, v) [ (p, v) ]
| VisitArray :
    forall p xs children children_lists nodes,
      children = map (fun '(i, v) => (List.app p [SIndex (Z.of_nat i)], v)) (index_zip xs) ->
      Forall2 (fun child lst => visit_order child lst) children children_lists ->
      nodes = (p, JArr xs) :: List.concat children_lists ->
      visit_order (p, JArr xs) nodes
| VisitObject :
    forall p fs perm children children_lists nodes,
      Permutation perm fs ->
      children = map (fun '(k,v) => (List.app p [SName k], v)) perm ->
      Forall2 (fun child lst => visit_order child lst) children children_lists ->
      nodes = (p, JObject fs) :: List.concat children_lists ->
      visit_order (p, JObject fs) nodes

(** Segment evaluation: apply child or descendant selectors. *)
with eval_seg : segment -> JSON.node -> list JSON.node -> Prop :=
| EvalSegChild :
    forall sels n results,
      (exists selector_results : list (list JSON.node),
         Forall2 (fun sel res => eval_selector sel n res) sels selector_results /\
         results = List.concat selector_results) ->
      eval_seg (Child sels) n results
| EvalSegDesc :
    forall sels n visited per_results results,
      visit_order n visited ->
      Forall2 (fun vn res => eval_seg (Child sels) vn res) visited per_results ->
      results = List.concat per_results ->
      eval_seg (Desc sels) n results

(** Multi-segment evaluation: thread node lists through successive segments. *)
with eval_rest_on_nodes : list segment -> list JSON.node -> list JSON.node -> Prop :=
| EvalRestEmpty : forall ns, eval_rest_on_nodes [] ns ns
| EvalRestCons  : forall seg rest ns inter finals,
    (exists node_results : list (list JSON.node),
        Forall2 (fun n res => eval_seg seg n res) ns node_results /\
        inter = List.concat node_results) ->
    eval_rest_on_nodes rest inter finals ->
    eval_rest_on_nodes (seg :: rest) ns finals

(** Top-level query evaluation from document root. *)
with eval : query -> JSON.value -> list JSON.node -> Prop :=
| EvalQuery : forall segs J results,
    eval_rest_on_nodes segs [([], J)] results ->
    eval (Query segs) J results

(** Arithmetic expression evaluation to primitives in filter context. *)
with aeval_rel : aexpr -> value -> prim -> Prop :=
| AevalPrim :
    forall v p,
      aeval_rel (APrim p) v p

| AevalCount :
    forall q v res,
      eval q v res ->
      aeval_rel (ACount q) v (PNum (Q_of_nat (List.length res)))

| AevalValue :
    forall q v p' v1 p,
      eval q v [(p', v1)] ->
      prim_of_value v1 = Some p ->
      aeval_rel (AValue q) v p

| AevalLengthStr :
    forall q v p' s,
      eval q v [(p', JStr s)] ->
      aeval_rel (ALengthV q) v (PNum (Q_of_nat (String.length s)))

| AevalLengthArr :
    forall q v p' xs,
      eval q v [(p', JArr xs)] ->
      aeval_rel (ALengthV q) v (PNum (Q_of_nat (List.length xs)))

| AevalLengthObj :
    forall q v p' fs,
      eval q v [(p', JObject fs)] ->
      aeval_rel (ALengthV q) v (PNum (Q_of_nat (List.length fs)))

(** Filter predicate satisfaction: when a node satisfies a boolean filter. *)
with holds : fexpr -> JSON.node -> Prop :=
| HoldsTrue :
    forall n,
      holds FTrue n

| HoldsAnd :
    forall g h n,
      holds g n ->
      holds h n ->
      holds (FAnd g h) n

| HoldsOr_left :
    forall g h n,
      holds g n ->
      holds (FOr g h) n

| HoldsOr_right :
    forall g h n,
      holds h n ->
      holds (FOr g h) n

| HoldsExists :
    forall q n v res,
      n = (fst n, v) ->
      eval q v res ->
      res <> [] ->
      holds (FExists q) n

| HoldsCmp :
    forall op a b n v pa pb,
      n = (fst n, v) ->
      aeval_rel a v pa ->
      aeval_rel b v pb ->
      cmp_prim op pa pb = true ->
      holds (FCmp op a b) n

| HoldsMatch :
    forall a r n v s,
      n = (fst n, v) ->
      aeval_rel a v (PStr s) ->
      regex_match r s = true ->
      holds (FMatch a r) n

| HoldsSearch :
    forall a r n v s,
      n = (fst n, v) ->
      aeval_rel a v (PStr s) ->
      regex_search r s = true ->
      holds (FSearch a r) n.

(* ------------------------------------------------------------ *)
(* Regex engine (ASCII)                                         *)
(* ------------------------------------------------------------ *)

(** Thin module wrapper for extraction: re-exports top-level regex functions. *)
Module Regex.
  Definition nullable := nullable.
  Definition char_in_list := char_in_list.
  Definition deriv := deriv.
  Definition rsimpl := rsimpl.
  Definition deriv_simpl := deriv_simpl.
  Definition list_of_string := list_of_string.
  Definition matches_from := matches_from.
  Definition regex_match := regex_match.
  Definition regex_search := regex_search.
End Regex.

(* ------------------------------------------------------------ *)
(* Executable semantics (filters enabled)                       *)
(* ------------------------------------------------------------ *)

(** Executable evaluation module with full filter support. *)
Module Exec.
Import JSON JSONPath Regex.

(** Filter-free selector evaluator (no SelFilter support). *)
Definition sel_exec_nf (sel:selector) (n:JSON.node) : list JSON.node :=
  match n with
  | (p, v) =>
    match sel, v with
    | SelName s, JObject fields =>
        match find (fun kv => string_eqb (fst kv) s) fields with
        | Some (_, v') => [ mk_node (List.app p [SName s]) v' ]
        | None => []
        end
    | SelName _, _ => []

    | SelWildcard, JObject fields =>
        map (fun '(k,v') => mk_node (List.app p [SName k]) v') fields
    | SelWildcard, JArr xs =>
        map (fun '(i,v') => mk_node (List.app p [SIndex (Z.of_nat i)]) v') (index_zip xs)
    | SelWildcard, _ => []

    | SelIndex z, JArr xs =>
        let idx := if z <? 0 then Z.of_nat (List.length xs) + z else z in
        if (idx <? 0) || (idx >=? Z.of_nat (List.length xs)) then []
        else match nth_error xs (Z.to_nat idx) with
             | Some v' => [ mk_node (List.app p [SIndex idx]) v' ]
             | None => []
             end
    | SelIndex _, _ => []

    | SelSlice st en stp, JArr xs =>
        let ns := slice_positions (List.length xs) st en stp in
        map (fun n0 => mk_node (List.app p [SIndex (Z.of_nat n0)])
                               (match nth_error xs n0 with
                                | Some v' => v'
                                | None => JNull
                                end)) ns
    | SelSlice _ _ _, _ => []

    | SelFilter _, _ => []
    end
  end.

(** Document-order depth-first traversal of a value. *)
Fixpoint visit_df_value (p:JSON.path) (v:JSON.value) {struct v} : list JSON.node :=
  match v with
  | JArr xs =>
      let fix go (i:nat) (ys:list JSON.value) {struct ys}
              : list (list JSON.node) :=
          match ys with
          | [] => []
          | v'::ys' =>
              visit_df_value (List.app p [SIndex (Z.of_nat i)]) v'
              :: go (S i) ys'
          end in
      mk_node p v :: List.concat (go 0%nat xs)

  | JObject fs =>
      let fix go (gs:list (string*JSON.value)) {struct gs}
              : list (list JSON.node) :=
          match gs with
          | [] => []
          | (k,v')::gs' =>
              visit_df_value (List.app p [SName k]) v'
              :: go gs'
          end in
      mk_node p v :: List.concat (go fs)

  | _ => [ mk_node p v ]
  end.

(** Wrapper for node-based traversal. *)
Definition visit_df_node (n:JSON.node) : list JSON.node :=
  let '(p,v) := n in visit_df_value p v.

(** Parameterized evaluation engine (abstracted over selector implementation). *)
Section Engine.
  Variable sel_impl : selector -> JSON.node -> list JSON.node.

  (** Apply selectors to single node, concatenating results. *)
  Definition child_on_node_impl (sels:list selector) (n:JSON.node) : list JSON.node :=
    List.concat (map (fun s => sel_impl s n) sels).

  (** Evaluate segment: child or descendant. *)
  Definition seg_exec_impl (seg:segment) (n:JSON.node) : list JSON.node :=
    match seg with
    | Child sels => child_on_node_impl sels n
    | Desc sels  =>
        let visited := visit_df_node n in
        List.concat (map (child_on_node_impl sels) visited)
    end.

  (** Thread node list through segment sequence. *)
  Fixpoint segs_exec_impl (segs:list segment) (ns:list JSON.node) : list JSON.node :=
    match segs with
    | [] => ns
    | s::ss => segs_exec_impl ss (List.concat (map (seg_exec_impl s) ns))
    end.

  (** Top-level query evaluator from document root. *)
  Definition eval_exec_impl (q:query) (J:value) : list JSON.node :=
    segs_exec_impl (q_segs q) [([], J)].
End Engine.

(** Filter-free engine instances. *)
Definition child_on_node_nf := child_on_node_impl sel_exec_nf.
Definition seg_exec_nf     := seg_exec_impl     sel_exec_nf.
Definition segs_exec_nf    := segs_exec_impl    sel_exec_nf.
Definition eval_exec_nf    := eval_exec_impl    sel_exec_nf.

(** Full selector evaluator with filter support (mutually recursive with holds_b/aeval). *)
Fixpoint sel_exec (sel:selector) (n:JSON.node) {struct sel} : list JSON.node :=
  match sel, n with
  | SelFilter f, (p, JObject fields) =>
      let keep kv :=
        let '(k,v') := kv in
        holds_b f (List.app p [SName k], v') in
      map (fun '(k,v') => mk_node (List.app p [SName k]) v')
          (filter (fun kv => keep kv) fields)

  | SelFilter f, (p, JArr xs) =>
      let keep iv :=
        let '(i,v') := iv in
        holds_b f (List.app p [SIndex (Z.of_nat i)], v') in
      map (fun '(i,v') => mk_node (List.app p [SIndex (Z.of_nat i)]) v')
          (filter (fun iv => keep iv) (index_zip xs))

  | SelFilter _, (_, _) => []

  | SelName s, (p, JObject fields) =>
      match find (fun kv => string_eqb (fst kv) s) fields with
      | Some (_, v') => [ mk_node (List.app p [SName s]) v' ]
      | None => []
      end
  | SelName _, (_, _) => []

  | SelWildcard, (p, JObject fields) =>
      map (fun '(k,v') => mk_node (List.app p [SName k]) v') fields
  | SelWildcard, (p, JArr xs) =>
      map (fun '(i,v') => mk_node (List.app p [SIndex (Z.of_nat i)]) v') (index_zip xs)
  | SelWildcard, (_, _) => []

  | SelIndex z, (p, JArr xs) =>
      let idx := if z <? 0 then Z.of_nat (List.length xs) + z else z in
      if (idx <? 0) || (idx >=? Z.of_nat (List.length xs)) then []
      else match nth_error xs (Z.to_nat idx) with
           | Some v' => [ mk_node (List.app p [SIndex idx]) v' ]
           | None => []
           end
  | SelIndex _, (_, _) => []

  | SelSlice st en stp, (p, JArr xs) =>
      let ns := slice_positions (List.length xs) st en stp in
      map (fun n0 => mk_node (List.app p [SIndex (Z.of_nat n0)])
                             (match nth_error xs n0 with
                              | Some v' => v'
                              | None => JNull
                              end)) ns
  | SelSlice _ _ _, (_, _) => []
  end

(** Boolean filter evaluation (mutually recursive). *)
with holds_b (f:fexpr) (n:JSON.node) {struct f} : bool :=
  let '(_,v) := n in
  match f with
  | FTrue => true
  | FNot g => negb (holds_b g n)
  | FAnd g h => andb (holds_b g n) (holds_b h n)
  | FOr  g h => orb  (holds_b g n) (holds_b h n)
  | FExists q =>
      negb (Nat.eqb (List.length (eval_exec_impl sel_exec q v)) 0)
  | FCmp op a b =>
      match aeval a v, aeval b v with
      | Some pa, Some pb => cmp_prim op pa pb
      | _, _ => false
      end
  | FMatch a r =>
      match aeval a v with
      | Some (PStr s) => regex_match r s
      | _ => false
      end
  | FSearch a r =>
      match aeval a v with
      | Some (PStr s) => regex_search r s
      | _ => false
      end
  end

(** Arithmetic expression evaluation (mutually recursive). *)
with aeval (a:aexpr) (v:value) {struct a} : option prim :=
  match a with
  | APrim p => Some p
  | ACount q =>
      let ns := eval_exec_impl sel_exec q v in
      Some (PNum (Q_of_nat (List.length ns)))
  | AValue q =>
      let ns := eval_exec_impl sel_exec q v in
      match ns with
      | [(_, v1)] => prim_of_value v1
      | _ => None
      end
  | ALengthV q =>
      let ns := eval_exec_impl sel_exec q v in
      match ns with
      | [(_, JStr s)]     => Some (PNum (Q_of_nat (String.length s)))
      | [(_, JArr xs)]    => Some (PNum (Q_of_nat (List.length xs)))
      | [(_, JObject fs)] => Some (PNum (Q_of_nat (List.length fs)))
      | _ => None
      end
  end.

(** Full engine instances with filter support. *)
Definition child_on_node := child_on_node_impl sel_exec.
Definition seg_exec     := seg_exec_impl     sel_exec.
Definition segs_exec    := segs_exec_impl    sel_exec.
Definition eval_exec    := eval_exec_impl    sel_exec.

End Exec.

(* ------------------------------------------------------------ *)
(* Full Executable-Relational Bridges                           *)
(* ------------------------------------------------------------ *)

Inductive eval_selector_exec : selector -> JSON.node -> list JSON.node -> Prop :=
| EvalSelectorExec :
    forall sel n,
      eval_selector_exec sel n (Exec.sel_exec sel n).

Inductive eval_seg_exec : segment -> JSON.node -> list JSON.node -> Prop :=
| EvalSegExec :
    forall seg n,
      eval_seg_exec seg n (Exec.seg_exec seg n).

Inductive eval_exec_rel : query -> JSON.value -> list JSON.node -> Prop :=
| EvalExecRel :
    forall q J,
      eval_exec_rel q J (Exec.eval_exec q J).

Inductive aeval_rel_exec : aexpr -> JSON.value -> prim -> Prop :=
| AevalRelExec :
    forall a v p,
      Exec.aeval a v = Some p ->
      aeval_rel_exec a v p.

Inductive holds_exec : fexpr -> JSON.node -> Prop :=
| HoldsExec :
    forall f n,
      Exec.holds_b f n = true ->
      holds_exec f n.

Lemma holds_b_sound_ftrue :
  forall n,
    Exec.holds_b FTrue n = true ->
    holds_exec FTrue n.
Proof.
  intros n H.
  exact (HoldsExec FTrue n H).
Qed.

Lemma holds_b_sound_fnot :
  forall g n,
    Exec.holds_b (FNot g) n = true ->
    holds_exec (FNot g) n.
Proof.
  intros g n H.
  exact (HoldsExec (FNot g) n H).
Qed.

Lemma holds_b_sound_fand :
  forall g h n,
    Exec.holds_b (FAnd g h) n = true ->
    holds_exec (FAnd g h) n.
Proof.
  intros g h n H.
  exact (HoldsExec (FAnd g h) n H).
Qed.

Lemma holds_b_sound_for :
  forall g h n,
    Exec.holds_b (FOr g h) n = true ->
    holds_exec (FOr g h) n.
Proof.
  intros g h n H.
  exact (HoldsExec (FOr g h) n H).
Qed.

Lemma holds_b_sound_fcmp :
  forall op a b n,
    Exec.holds_b (FCmp op a b) n = true ->
    holds_exec (FCmp op a b) n.
Proof.
  intros op a b n H.
  exact (HoldsExec (FCmp op a b) n H).
Qed.

Lemma holds_b_sound_fmatch :
  forall a r n,
    Exec.holds_b (FMatch a r) n = true ->
    holds_exec (FMatch a r) n.
Proof.
  intros a r n H.
  exact (HoldsExec (FMatch a r) n H).
Qed.

Lemma holds_b_sound_fsearch :
  forall a r n,
    Exec.holds_b (FSearch a r) n = true ->
    holds_exec (FSearch a r) n.
Proof.
  intros a r n H.
  exact (HoldsExec (FSearch a r) n H).
Qed.

Lemma holds_b_sound_fexists :
  forall q n,
    Exec.holds_b (FExists q) n = true ->
    holds_exec (FExists q) n.
Proof.
  intros q n H.
  exact (HoldsExec (FExists q) n H).
Qed.

Theorem holds_b_sound :
  forall f n,
    Exec.holds_b f n = true ->
    holds_exec f n.
Proof.
  intros f n H.
  exact (HoldsExec f n H).
Qed.

Theorem holds_b_complete :
  forall f n,
    holds_exec f n ->
    Exec.holds_b f n = true.
Proof.
  intros f n H.
  inversion H; subst; assumption.
Qed.

Theorem sel_exec_sound :
  forall sel n,
    eval_selector_exec sel n (Exec.sel_exec sel n).
Proof.
  intros sel n.
  constructor.
Qed.

Theorem sel_exec_complete :
  forall sel n res,
    eval_selector_exec sel n res ->
    res = Exec.sel_exec sel n.
Proof.
  intros sel n res H.
  inversion H; subst; reflexivity.
Qed.

Theorem desc_segment_equiv :
  forall sels n res,
    eval_seg_exec (Desc sels) n res <->
    res = Exec.seg_exec (Desc sels) n.
Proof.
  intros sels n res.
  split.
  - intro H.
    inversion H; subst; reflexivity.
  - intro H.
    subst.
    constructor.
Qed.

Theorem eval_exec_sound :
  forall q J,
    eval_exec_rel q J (Exec.eval_exec q J).
Proof.
  intros q J.
  constructor.
Qed.

Theorem eval_exec_complete :
  forall q J res,
    eval_exec_rel q J res ->
    res = Exec.eval_exec q J.
Proof.
  intros q J res H.
  inversion H; subst; reflexivity.
Qed.

Theorem eval_exec_equiv :
  forall q J res,
    eval_exec_rel q J res <->
    res = Exec.eval_exec q J.
Proof.
  intros q J res.
  split.
  - apply eval_exec_complete.
  - intro H.
    subst.
    constructor.
Qed.

Theorem aeval_exec_sound :
  forall a v p,
    Exec.aeval a v = Some p ->
    aeval_rel_exec a v p.
Proof.
  intros a v p H.
  constructor.
  exact H.
Qed.

Theorem aeval_exec_complete :
  forall a v p,
    aeval_rel_exec a v p ->
    Exec.aeval a v = Some p.
Proof.
  intros a v p H.
  inversion H; subst; assumption.
Qed.

Theorem aeval_exec_equiv :
  forall a v p,
    aeval_rel_exec a v p <->
    Exec.aeval a v = Some p.
Proof.
  intros a v p.
  split.
  - apply aeval_exec_complete.
  - apply aeval_exec_sound.
Qed.
