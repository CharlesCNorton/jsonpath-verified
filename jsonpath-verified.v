(**
  JSONPath (RFC 9535): relational and executable semantics in Coq.
  The development uses only the Coq standard library and supports OCaml extraction.
*)

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

Definition string_eqb (s1 s2 : string) : bool :=
  if string_dec s1 s2 then true else false.

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

Definition index_zip {A} (xs : list A) : list (nat * A) :=
  combine (seq 0 (List.length xs)) xs.

(* ASCII-based lexicographic order for strings *)
Definition ascii_eqb (a b:ascii) : bool :=
  if ascii_dec a b then true else false.

Definition ascii_ltb (a b:ascii) : bool :=
  Nat.ltb (nat_of_ascii a) (nat_of_ascii b).

Definition ascii_leb (a b:ascii) : bool :=
  negb (ascii_ltb b a).

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

Definition str_leb (s1 s2:string) : bool :=
  orb (string_eqb s1 s2) (str_ltb s1 s2).

(* Q helpers *)
Definition Qeqb (x y:Q) : bool :=
  match Qcompare x y with
  | Eq => true | _ => false
  end.

Definition Qltb (x y:Q) : bool :=
  match Qcompare x y with
  | Lt => true | _ => false
  end.

Definition Qleb (x y:Q) : bool :=
  negb (Qltb y x).

Definition Q_of_Z (z:Z) : Q := inject_Z z.
Definition Q_of_nat (n:nat) : Q := inject_Z (Z.of_nat n).



(* ------------------------------------------------------------ *)
(* JSON core                                                    *)
(* ------------------------------------------------------------ *)

Module JSON.
Inductive value :=
| JNull
| JBool (b:bool)
| JNum (n: Q)
| JStr (s:string)
| JArr (xs:list value)
| JObject (fields: list (string * value)).  (* RFC: member order not stipulated *)

Inductive step := SName (s:string) | SIndex (i:Z).
Definition path := list step.
Definition node := (path * value)%type.
End JSON.

Definition mk_node (p:JSON.path) (v:JSON.value) : JSON.node := (p, v).

(* ------------------------------------------------------------ *)
(* JSONPath AST                                                 *)
(* ------------------------------------------------------------ *)

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

(* Minimal regex AST for ASCII strings *)
Inductive regex :=
| REmpty
| REps
| RChr (c:ascii)
| RAny
| RAlt (r1 r2:regex)
| RCat (r1 r2:regex)
| RStar (r:regex).

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
| FMatch (a:aexpr) (r:regex)   (* full match *)
| FSearch (a:aexpr) (r:regex)  (* substring search *)
with selector :=
| SelName (s:string)
| SelWildcard
| SelIndex (i:Z)
| SelSlice (start end_ : option Z) (stp: Z)
| SelFilter (f:fexpr)
with segment :=
| Child (sels: list selector)
| Desc (sels: list selector)
with query := Query (segs : list segment).

Definition q_segs (q:query) : list segment :=
  match q with Query ss => ss end.

End JSONPath.

Import JSON JSONPath.

(* ------------------------------------------------------------ *)
(* Slice helpers                                                *)
(* ------------------------------------------------------------ *)

Definition clamp (x lo hi : Z) : Z := Z.max lo (Z.min hi x).

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

Fixpoint up_by (i stop step : Z) (fuel:nat) : list Z :=
  match fuel with
  | O => []
  | S fuel' =>
      if (i <? stop)%Z
      then i :: up_by (i + step) stop step fuel'
      else []
  end.

Fixpoint down_by (i stop step : Z) (fuel:nat) : list Z :=
  match fuel with
  | O => []
  | S fuel' =>
      if (stop <? i)%Z
      then i :: down_by (i + step) stop step fuel'
      else []
  end.

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

Fixpoint nth_default (d:JSON.value) (xs:list JSON.value) (n:nat) : JSON.value :=
  match xs, n with
  | [], _ => d
  | x::_, O => x
  | _::xs', S n' => nth_default d xs' n'
  end.

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
(* Relational semantics                                         *)
(* ------------------------------------------------------------ *)

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
                    [ (List.app p [SIndex z], v) ]
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
             (slice_positions (List.length xs) start end_ stp)).

Inductive visit_order : JSON.node -> list JSON.node -> Prop :=
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
      visit_order (p, JObject fs) nodes.

Inductive eval_seg : segment -> JSON.node -> list JSON.node -> Prop :=
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
      eval_seg (Desc sels) n results.

Inductive eval_rest_on_nodes : list segment -> list JSON.node -> list JSON.node -> Prop :=
| EvalRestEmpty : forall ns, eval_rest_on_nodes [] ns ns
| EvalRestCons  : forall seg rest ns inter finals,
    (exists node_results : list (list JSON.node),
        Forall2 (fun n res => eval_seg seg n res) ns node_results /\
        inter = List.concat node_results) ->
    eval_rest_on_nodes rest inter finals ->
    eval_rest_on_nodes (seg :: rest) ns finals.

Inductive eval : query -> JSON.value -> list JSON.node -> Prop :=
| EvalQuery : forall segs J results,
    eval_rest_on_nodes segs [([], J)] results ->
    eval (Query segs) J results.

(* ------------------------------------------------------------ *)
(* Regex engine (ASCII)                                         *)
(* ------------------------------------------------------------ *)

Module Regex.
Import JSONPath.

Fixpoint nullable (r:regex) : bool :=
  match r with
  | REmpty => false
  | REps => true
  | RChr _ => false
  | RAny => false
  | RAlt r1 r2 => orb (nullable r1) (nullable r2)
  | RCat r1 r2 => andb (nullable r1) (nullable r2)
  | RStar _ => true
  end.

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
  end.

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
  | _ => r
  end.

Definition deriv_simpl (a:ascii) (r:regex) : regex :=
  rsimpl (deriv a r).

Fixpoint list_of_string (s:string) : list ascii :=
  match s with
  | EmptyString => []
  | String a s' => a :: list_of_string s'
  end.

Fixpoint matches_from (r:regex) (cs:list ascii) : bool :=
  match cs with
  | [] => nullable r
  | a::cs' => matches_from (deriv_simpl a r) cs'
  end.

Definition regex_match (r:regex) (s:string) : bool :=
  matches_from r (list_of_string s).

(* search = .* r .* *)
Definition regex_search (r:regex) (s:string) : bool :=
  regex_match (RCat (RStar RAny) (RCat r (RStar RAny))) s.

End Regex.

(* ------------------------------------------------------------ *)
(* Executable semantics (filters enabled)                       *)
(* ------------------------------------------------------------ *)

Module Exec.
Import JSON JSONPath Regex.

(* Primitive comparisons *)

Definition prim_eq (p q:prim) : bool :=
  match p, q with
  | PNull, PNull => true
  | PBool b1, PBool b2 => Bool.eqb b1 b2
  | PNum n1, PNum n2 => Qeqb n1 n2
  | PStr s1, PStr s2 => string_eqb s1 s2
  | _, _ => false
  end.

Definition prim_lt (p q:prim) : bool :=
  match p, q with
  | PNum n1, PNum n2 => Qltb n1 n2
  | PStr s1, PStr s2 => str_ltb s1 s2
  | _ , _ => false
  end.

Definition cmp_prim (op:cmp) (x y:prim) : bool :=
  match op with
  | CEq => prim_eq x y
  | CNe => negb (prim_eq x y)
  | CLt => prim_lt x y
  | CLe => orb (prim_lt x y) (prim_eq x y)
  | CGt => prim_lt y x
  | CGe => orb (prim_lt y x) (prim_eq x y)
  end.

(* Selector evaluator without filters *)

Fixpoint sel_exec_nf (sel:selector) (n:JSON.node) : list JSON.node :=
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
             | Some v' => [ mk_node (List.app p [SIndex z]) v' ]
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

(* Document-order DFS visit *)

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

Definition visit_df_node (n:JSON.node) : list JSON.node :=
  let '(p,v) := n in visit_df_value p v.

(* Generic engine parameterized by a selector implementation *)

Section Engine.
  Variable sel_impl : selector -> JSON.node -> list JSON.node.

  Definition child_on_node_impl (sels:list selector) (n:JSON.node) : list JSON.node :=
    List.concat (map (fun s => sel_impl s n) sels).

  Definition seg_exec_impl (seg:segment) (n:JSON.node) : list JSON.node :=
    match seg with
    | Child sels => child_on_node_impl sels n
    | Desc sels  =>
        let visited := visit_df_node n in
        List.concat (map (child_on_node_impl sels) visited)
    end.

  Fixpoint segs_exec_impl (segs:list segment) (ns:list JSON.node) : list JSON.node :=
    match segs with
    | [] => ns
    | s::ss => segs_exec_impl ss (List.concat (map (seg_exec_impl s) ns))
    end.

  Definition eval_exec_impl (q:query) (J:value) : list JSON.node :=
    segs_exec_impl (q_segs q) [([], J)].
End Engine.

(* nf-instance engine (no filters) *)
Definition child_on_node_nf := child_on_node_impl sel_exec_nf.
Definition seg_exec_nf     := seg_exec_impl     sel_exec_nf.
Definition segs_exec_nf    := segs_exec_impl    sel_exec_nf.
Definition eval_exec_nf    := eval_exec_impl    sel_exec_nf.

(* Full engine with filters *)

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
           | Some v' => [ mk_node (List.app p [SIndex z]) v' ]
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

Definition child_on_node := child_on_node_impl sel_exec.
Definition seg_exec     := seg_exec_impl     sel_exec.
Definition segs_exec    := segs_exec_impl    sel_exec.
Definition eval_exec    := eval_exec_impl    sel_exec.

End Exec.

(* ------------------------------------------------------------ *)
(* Static well-formedness checks (conservative)                 *)
(* ------------------------------------------------------------ *)

Module Typing.
Import JSON JSONPath.

Inductive primty := TNull | TBool | TNum | TStr | TAnyPrim.

Definition selector_ok (sel:selector) : bool :=
  match sel with
  | SelName _ | SelIndex _ => true
  | _ => false
  end.

Definition segment_ok (s:segment) : bool :=
  match s with
  | Child sels => forallb selector_ok sels
  | Desc _ => false
  end.

(* Chains of Child with only SelName/SelIndex *)
Definition singleton_query (q:query) : bool :=
  match q with
  | Query segs =>
      match segs with
      | [] => false
      | _  => forallb segment_ok segs
      end
  end.

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

Definition comparable (t1 t2:primty) : bool :=
  match t1, t2 with
  | TNull, TNull => true
  | TBool, TBool => true
  | TNum , TNum  => true
  | TStr , TStr  => true
  | TAnyPrim, _  => true
  | _ , TAnyPrim => true
  | _ , _        => false
  end.

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
(* Bridge lemma: selector -> Child [selector]                   *)
(* ------------------------------------------------------------ *)

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

Definition JQ (z:Z) : JSON.value := JSON.JNum (Q_of_Z z).

(* Basic selectors *)

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

Example test_negative_index :
  let json := JArr [JQ 10; JQ 20; JQ 30] in
  exists result, eval (Query [Child [SelIndex (-1)]]) json result /\
                 result = [([SIndex (-1)], JQ 30)].
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

Theorem empty_query_returns_root : forall J,
  eval (Query []) J [([], J)].
Proof. intros. constructor. constructor. Qed.

(* Slices *)

Example exec_slice_pos :
  let j := JArr [JQ 0; JQ 1; JQ 2; JQ 3] in
  eval_exec (Query [Child [SelSlice (Some 1) (Some 3) 1]]) j
  = [ ([SIndex 1], JQ 1) ; ([SIndex 2], JQ 2) ].
Proof. reflexivity. Qed.

Example exec_slice_neg_step_all :
  let j := JArr [JQ 10; JQ 20; JQ 30] in
  eval_exec (Query [Child [SelSlice None None (-1)]]) j
  = [ ([SIndex 2], JQ 30) ; ([SIndex 1], JQ 20) ; ([SIndex 0], JQ 10) ].
Proof. reflexivity. Qed.

Example exec_slice_zero_step_is_empty :
  let j := JArr [JQ 10; JQ 20] in
  eval_exec (Query [Child [SelSlice None None 0]]) j = [].
Proof. reflexivity. Qed.

Example exec_slice_mixed_bounds :
  let j := JArr [JQ 0; JQ 1; JQ 2; JQ 3; JQ 4] in
  eval_exec (Query [Child [SelSlice (Some (-3)) None 1]]) j
  = [ ([SIndex 2], JQ 2) ; ([SIndex 3], JQ 3) ; ([SIndex 4], JQ 4) ].
Proof. reflexivity. Qed.

(* Filters *)

Definition f_age_gt_21 : selector :=
  SelFilter (FCmp CGt
                 (AValue (Query [Child [SelName "age"]]))
                 (APrim (PNum (Q_of_Z 21)))).

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

Definition f_exists_age : selector :=
  SelFilter (FExists (Query [Child [SelName "age"]])).

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

Definition f_tags_count_ge_2 : selector :=
  SelFilter (FCmp CGe
                 (ACount (Query [Child [SelName "tags"]; Child [SelWildcard]]))
                 (APrim (PNum (Q_of_Z 2)))).

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

Definition f_len_gt_3 : selector :=
  SelFilter (FCmp CGt
                 (ALengthV (Query []))
                 (APrim (PNum (Q_of_Z 3)))).

Example exec_filter_length_gt_3_on_array_of_strings :
  let j := JArr [JStr "a"; JStr "abcd"; JStr "xyz"; JStr "hello"] in
  eval_exec (Query [Child [f_len_gt_3]]) j
  = [
      ([SIndex 1], JStr "abcd");
      ([SIndex 3], JStr "hello")
    ].
Proof. reflexivity. Qed.

(* Descendant semantics *)

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

(* Regex utilities *)

Definition re_hello : regex :=
  RCat (RChr "h"%char)
    (RCat (RChr "e"%char)
     (RCat (RChr "l"%char)
      (RCat (RChr "l"%char) (RChr "o"%char)))).

Definition f_str_match_hello : selector :=
  SelFilter (FMatch (AValue (Query [])) re_hello).

Definition f_str_search_ll : selector :=
  SelFilter (FSearch (AValue (Query []))
                     (RCat (RChr "l"%char) (RChr "l"%char))).

Example exec_regex_match_full :
  let j := JArr [JStr "hello"; JStr "hell"; JStr "oh hello!"] in
  eval_exec (Query [Child [f_str_match_hello]]) j
  = [ ([SIndex 0], JStr "hello") ].
Proof. reflexivity. Qed.

Example exec_regex_search_substring :
  let j := JArr [JStr "hello"; JStr "hell"; JStr "oh hello!"] in
  eval_exec (Query [Child [f_str_search_ll]]) j
  = [
      ([SIndex 0], JStr "hello");
      ([SIndex 1], JStr "hell");
      ([SIndex 2], JStr "oh hello!")
    ].
Proof. reflexivity. Qed.

(* Edge cases *)

Example exec_name_on_non_object :
  let j := JQ 0 in
  eval_exec (Query [Child [SelName "a"]]) j = [].
Proof. reflexivity. Qed.

Example exec_index_on_non_array :
  let j := JObject [("a", JQ 1)] in
  eval_exec (Query [Child [SelIndex 0]]) j = [].
Proof. reflexivity. Qed.

Example exec_wildcard_on_scalar :
  let j := JStr "x" in
  eval_exec (Query [Child [SelWildcard]]) j = [].
Proof. reflexivity. Qed.

Example exec_filter_on_scalar_yields_empty :
  let j := JStr "abc" in
  eval_exec (Query [Child [f_len_gt_3]]) j = [].
Proof. reflexivity. Qed.

(* ------------------------------------------------------------ *)
(* Out-of-bounds contradiction lemma                             *)
(* ------------------------------------------------------------ *)

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

(* Small regexes used in filters *)
Definition re_at : JSONPath.regex := RChr "@"%char.
Definition re_dotcom : JSONPath.regex :=
  RCat (RChr "."%char)
   (RCat (RChr "c"%char) (RCat (RChr "o"%char) (RChr "m"%char))).

(* Projects *)
Definition proj_phoenix_a : JSON.value :=
  JObject [("name", JStr "phoenix"); ("stars", JQ 50);
           ("labels", JArr [JStr "ml"; JStr "vision"])].

Definition proj_drake_a : JSON.value :=
  JObject [("name", JStr "drake"); ("stars", JQ 20);
           ("labels", JArr [JStr "infra"])].

Definition proj_phoenix_c : JSON.value :=
  JObject [("name", JStr "phoenix"); ("stars", JQ 70);
           ("labels", JArr [JStr "ml"; JStr "nlp"])].

Definition proj_eagle_c : JSON.value :=
  JObject [("name", JStr "eagle"); ("stars", JQ 15);
           ("labels", JArr [JStr "infra"])].

Definition proj_crm_d : JSON.value :=
  JObject [("name", JStr "crm"); ("stars", JQ 8);
           ("labels", JArr [JStr "sales"])].

(* Employees *)
Definition emp_alice : JSON.value :=
  JObject [("name", JStr "alice");
           ("age", JQ 34);
           ("email", JStr "alice@acme.com");
           ("tags", JArr [JStr "ml"; JStr "backend"]);
           ("bio", JStr "senior ml engineer");
           ("projects", JArr [proj_phoenix_a; proj_drake_a])].

Definition emp_bob : JSON.value :=
  JObject [("name", JStr "bob");
           ("age", JQ 29);
           ("email", JStr "bob@acme.org");
           ("tags", JArr [JStr "frontend"]);
           ("bio", JStr "ui");
           ("projects", JArr [])].

Definition emp_carol : JSON.value :=
  JObject [("name", JStr "carol");
           ("age", JQ 41);
           ("email", JStr "carol@acme.com");
           ("tags", JArr [JStr "ml"; JStr "nlp"; JStr "research"]);
           ("bio", JStr "nlp specialist");
           ("projects", JArr [proj_phoenix_c; proj_eagle_c])].

Definition emp_dave : JSON.value :=
  JObject [("name", JStr "dave");
           ("age", JQ 33);
           ("email", JStr "dave@acme.com");
           ("tags", JArr [JStr "sales"; JStr "lead"]);
           ("bio", JStr "account exec");
           ("projects", JArr [proj_crm_d])].

Definition emp_erin : JSON.value :=
  JObject [("name", JStr "erin");
           ("age", JQ 22);
           ("email", JStr "erin@acme.com");
           ("tags", JArr [JStr "intern"]);
           ("bio", JStr "summer intern");
           ("projects", JArr [])].

(* Departments *)
Definition dept_research : JSON.value :=
  JObject [("name", JStr "Research");
           ("employees", JArr [emp_alice; emp_bob; emp_carol])].

Definition dept_sales : JSON.value :=
  JObject [("name", JStr "Sales");
           ("employees", JArr [emp_dave; emp_erin])].

(* Whole document *)
Definition company_json : JSON.value :=
  JObject [("company", JStr "Acme");
           ("departments", JArr [dept_research; dept_sales]);
           ("meta", JObject [("version", JStr "1.0"); ("rev", JQ 7)])].

(* Query 1: filter by age/tags/email *)
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

(* Query 2: last project names at any depth *)

Example exec_naturalistic_last_project_names :
  eval_exec
    (Query [ Desc  [SelName "projects"];
             Child [SelIndex (-1)];
             Child [SelName "name"] ])
    company_json
  =
  [
    ([SName "departments"; SIndex 0; SName "employees"; SIndex 0;
      SName "projects"; SIndex (-1); SName "name"], JStr "drake");
    ([SName "departments"; SIndex 0; SName "employees"; SIndex 2;
      SName "projects"; SIndex (-1); SName "name"], JStr "eagle");
    ([SName "departments"; SIndex 1; SName "employees"; SIndex 0;
      SName "projects"; SIndex (-1); SName "name"], JStr "crm")
  ].
Proof. reflexivity. Qed.

(* Query 3: employees with at least two projects stars>=15 *)

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

(* Query 4: lexicographic sanity check *)

Definition sel_emp_name_lt_c : JSONPath.selector :=
  SelFilter
    (FCmp CLt
      (AValue (Query [Child [SelName "name"]]))
      (APrim (PStr "c"))).

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

Example exec_desc_includes_self_immediate :
  let j := JObject [("name", JStr "top"); ("child", JObject [("name", JStr "kid")])] in
  eval_exec (Query [Desc [SelName "name"]]) j
  = [ ([SName "name"], JStr "top");
      ([SName "child"; SName "name"], JStr "kid") ].
Proof. reflexivity. Qed.

Example exec_slice_neg_step_bounds :
  let j := JArr [JQ 0; JQ 1; JQ 2; JQ 3; JQ 4] in
  eval_exec (Query [Child [SelSlice (Some 4) (Some 1) (-2)]]) j
  = [ ([SIndex 4], JQ 4) ; ([SIndex 2], JQ 2) ].
Proof. reflexivity. Qed.

Example exec_avalue_multi_hit_fails :
  let j := JObject [("a", JQ 1); ("b", JQ 2)] in
  Exec.holds_b (FCmp CEq (AValue (Query [Child [SelWildcard]])) (APrim (PNum (Q_of_Z 1))))
               ([], j) = false.
Proof. reflexivity. Qed.

Example typing_requires_string_for_search :
  Typing.wf_fexpr (FSearch (APrim (PNum (Q_of_Z 3))) (RChr "3"%char)) = false.
Proof. reflexivity. Qed.

(* Extended dataset *)

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
(* Equivalence theorems for the filter‑free, child‑only core    *)
(* ============================================================ *)

Module JSONPath_Equiv.
  Import JSON JSONPath Exec.

  Local Open Scope Z_scope.

  (* Syntactic fragments *)

  Definition selector_filter_free (s:selector) : bool :=
    match s with
    | SelFilter _ => false
    | _ => true
    end.

  Definition segment_child_only (seg:segment) : bool :=
    match seg with
    | Child sels => forallb selector_filter_free sels
    | Desc _     => false
    end.

  Definition query_child_only (q:query) : bool :=
    match q with
    | Query segs => forallb segment_child_only segs
    end.

  (* Utilities *)

  Lemma find_some :
    forall (A:Type) (f:A->bool) (l:list A) (x:A),
      List.find f l = Some x -> f x = true.
  Proof.
    intros A f l x H. induction l as [|y ys IH]; simpl in *; try discriminate.
    destruct (f y) eqn:Hy.
    - inversion H; subst; assumption.
    - apply IH; assumption.
  Qed.

  (* Helpers *)

  Lemma geb_false_lt : forall x y : Z, (x >=? y) = false -> x < y.
  Proof.
    intros x y H.
    unfold Z.geb in H.
    destruct (Z.compare x y) eqn:C; simpl in H; try discriminate.
    pose proof (Z.compare_spec x y) as Hc.
    rewrite C in Hc. inversion Hc; assumption.
  Qed.

  Lemma ltb_false_ge : forall x y : Z, (x <? y) = false -> y <= x.
  Proof. intros x y H; apply Z.ltb_ge in H; exact H. Qed.

  Lemma orb_false_split : forall a b : bool, a || b = false -> a = false /\ b = false.
  Proof. intros a b H; now apply Bool.orb_false_iff in H. Qed.

  Lemma in_bounds_from_bools :
    forall idx len : Z,
      (idx <? 0) = false ->
      (idx >=? len) = false ->
      0 <= idx < len.
  Proof.
    intros idx len Hlt0 Hge.
    split; [apply ltb_false_ge in Hlt0; lia | apply geb_false_lt in Hge; exact Hge].
  Qed.

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
    eval_selector (SelIndex i) (p, JArr xs) [ (List.app p [SIndex i], v') ].
Proof.
  intros i p xs idx v' Hidx Hlt0 Hge Hnth.
  eapply EvalSelIndex with (idx := idx); eauto.
Qed.


(* Soundness of the nf selector interpreter *)
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
    = [ (List.app p [SIndex i], v') ].
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

(* Completeness of the nf selector interpreter *)
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

(** * Selector-Level Properties (Filter-Free Fragment) *)

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
  - (* One step: concat ∘ map (seg_exec_nf seg) preserves permutations *)
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

Theorem linear_query_arity_le1 :
  forall q J,
    linear_query q = true ->
    (List.length (Exec.eval_exec_nf q J) <= 1)%nat.
Proof.
  intros [segs] J Hlin; simpl in *.
  change (Exec.segs_exec_nf segs [([], J)]) with (Exec.segs_exec_nf segs [([], J)]).
  eapply segs_exec_nf_linear_len_le1; [exact Hlin| simpl; lia].
Qed.

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
