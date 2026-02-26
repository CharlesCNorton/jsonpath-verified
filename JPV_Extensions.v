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

Fixpoint sel_exec_nf (sel:uselector) (n:unode) : list unode :=
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

Definition quickchick_core_suite : bool :=
  prop_linear_len_le1 &&
  prop_wildcard_object_length &&
  prop_wildcard_array_length &&
  prop_desc_superset_name &&
  prop_search_as_match_on_strings.

Definition quickchick_extended_suite : bool :=
  quickchick_core_suite &&
  prop_filter_search_match_equiv &&
  prop_desc_superset_wildcard.

Theorem quickchick_extended_suite_passes :
  quickchick_extended_suite = true.
Proof.
  vm_compute. reflexivity.
Qed.

End PropertySuite.

(* Module API *)

