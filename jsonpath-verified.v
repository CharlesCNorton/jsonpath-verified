(**
  JSONPath RFC9535 – relational + executable semantics (Coq)
   - No admits or axioms
   - Uses only Coq stdlib
   - Ready for OCaml extraction

  Added (vs. baseline):
   * JSON numbers generalized to rationals (Q)
   * String lexicographic ordering (ASCII) for <, <=, >, >=
   * Small total regex engine with Brzozowski derivatives
   * Filters: match()/search() over strings
   * Conservative static typing checker module (no proofs required)
*)

From Coq Require Import
  List String Ascii ZArith Arith Lia Bool
  Sorting.Permutation QArith QArith_base.

Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(* ------------------------------------------------------------ *)
(* Utilities *)
(* ------------------------------------------------------------ *)

Definition string_eqb (s1 s2 : string) : bool :=
  if string_dec s1 s2 then true else false.

(* zip with indices [0..n-1] *)
Definition index_zip {A} (xs : list A) : list (nat * A) :=
  combine (seq 0 (List.length xs)) xs.

(* ASCII-based lexicographic order for strings (total) *)
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
(* JSON core *)
(* ------------------------------------------------------------ *)

Module JSON.
Inductive value :=
| JNull
| JBool (b:bool)
| JNum (n: Q)              (* generalized to rationals *)
| JStr (s:string)
| JArr (xs:list value)
| JObject (fields: list (string * value)).  (* RFC: member order not stipulated *)

Inductive step := SName (s:string) | SIndex (i:Z).
Definition path := list step.
Definition node := (path * value)%type.
End JSON.

Definition mk_node (p:JSON.path) (v:JSON.value) : JSON.node := (p, v).

(* ------------------------------------------------------------ *)
(* JSONPath AST *)
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

(* A small regex AST for match/search on strings *)
Inductive regex :=
| REmpty   (* ∅ *)
| REps     (* ε *)
| RChr (c:ascii)
| RAny
| RAlt (r1 r2:regex)
| RCat (r1 r2:regex)
| RStar (r:regex).

Inductive aexpr :=
| APrim (p:prim)
| ACount (q:query)
| AValue (q:query)     (* value-of: defined if q yields exactly one node and it is a primitive *)
| ALengthV (q:query)   (* length of string/array/object result if exactly one node *)
with fexpr :=
| FTrue
| FNot (f:fexpr)
| FAnd (f g:fexpr)
| FOr  (f g:fexpr)
| FExists (q:query)
| FCmp (op:cmp) (a b:aexpr)
| FMatch (a:aexpr) (r:regex)   (* full match of string value *)
| FSearch (a:aexpr) (r:regex)  (* substring search of string value *)
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
(* Slice helpers *)
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

(* ------------------------------------------------------------ *)
(* Relational semantics *)
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
(* Regex engine (ASCII) *)
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

Fixpoint list_of_string (s:string) : list ascii :=
  match s with
  | EmptyString => []
  | String a s' => a :: list_of_string s'
  end.

Fixpoint matches_from (r:regex) (cs:list ascii) : bool :=
  match cs with
  | [] => nullable r
  | a::cs' => matches_from (deriv a r) cs'
  end.

Definition regex_match (r:regex) (s:string) : bool :=
  matches_from r (list_of_string s).

(* search = .* r .*   i.e., substring exists *)
Definition regex_search (r:regex) (s:string) : bool :=
  regex_match (RCat (RStar RAny) (RCat r (RStar RAny))) s.

End Regex.

(* ------------------------------------------------------------ *)
(* Executable semantics (complete filters) *)
(* ------------------------------------------------------------ *)

Module Exec.
Import JSON JSONPath Regex.

(* ---------- Primitive comparisons ---------- *)

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

(* ---------- No-filter selector evaluator (kept) ---------- *)

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

(* ---------- Depth-first visit in document order ---------- *)

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

(* ---------- Generic engine parameterized by selector impl ---------- *)

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

(* nf-instance engine (ignores filters) *)
Definition child_on_node_nf := child_on_node_impl sel_exec_nf.
Definition seg_exec_nf     := seg_exec_impl     sel_exec_nf.
Definition segs_exec_nf    := segs_exec_impl    sel_exec_nf.
Definition eval_exec_nf    := eval_exec_impl    sel_exec_nf.

(* ---------- Full semantics: filters (now with regex) may nest ---------- *)
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

  | SelFilter _, (_, _) => []  (* filtering a scalar yields nothing *)

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

(* Specialized full evaluator *)
Definition child_on_node := child_on_node_impl sel_exec.
Definition seg_exec     := seg_exec_impl     sel_exec.
Definition segs_exec    := segs_exec_impl    sel_exec.
Definition eval_exec    := eval_exec_impl    sel_exec.

End Exec.

(* ------------------------------------------------------------ *)
(* A conservative static typing/checking module (no proofs)     *)
(* This accepts a safe subset to avoid obvious dynamic failures *)
(* ------------------------------------------------------------ *)
Module Typing.
Import JSON JSONPath.

Inductive primty := TNull | TBool | TNum | TStr | TAnyPrim.

(* Helpers for the singleton-query syntactic check *)
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

(* A very conservative syntactic predicate for "singleton" queries:
   chains of Child with only SelName/SelIndex (no wildcard/slice/desc/filter). *)
Definition singleton_query (q:query) : bool :=
  match q with
  | Query segs =>
      match segs with
      | [] => false
      | _  => forallb segment_ok segs
      end
  end.

(* Type inference for aexpr (very conservative) *)
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

(* Check if two primitive types are “comparable” for FCmp *)
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
(* Bridge lemma: selector -> Child [selector] *)
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
(* Tests *)
(* ------------------------------------------------------------ *)

Import Exec.

(* Shorthand for Q-valued JSON numbers *)
Definition JQ (z:Z) : JSON.value := JSON.JNum (Q_of_Z z).

(* ---------- Basic selectors ---------- *)

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
        eapply EvalSelIndex with (idx:=1); simpl.
        { reflexivity. }  (* idx = z *)
        { reflexivity. }  (* idx <? 0 = false *)
        { reflexivity. }  (* idx >=? len = false *)
        { reflexivity. }  (* nth_error ... = Some _ *)
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
        eapply EvalSelIndex with (idx:=2); simpl.
        { reflexivity. }
        { reflexivity. }
        { reflexivity. }
        { reflexivity. }
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
  (* seg1 *)
  econstructor.
  - eexists. split.
    + constructor.
      * apply eval_child_single_selector.
        apply EvalSelName. reflexivity.
      * constructor.
    + simpl. reflexivity.
  - (* seg2 *)
    econstructor.
    + eexists. split.
      * constructor.
        -- apply eval_child_single_selector.
           eapply EvalSelIndex with (idx:=0); simpl.
           { reflexivity. }
           { reflexivity. }
           { reflexivity. }
           { reflexivity. }
        -- constructor.
      * simpl. reflexivity.
    + (* seg3 *)
      econstructor.
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

(* ---------- Slices ---------- *)

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

(* ---------- Filters (comparisons / exists / count / length) ---------- *)

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
                 (ALengthV (Query []))  (* length of current node value *)
                 (APrim (PNum (Q_of_Z 3)))).

Example exec_filter_length_gt_3_on_array_of_strings :
  let j := JArr [JStr "a"; JStr "abcd"; JStr "xyz"; JStr "hello"] in
  eval_exec (Query [Child [f_len_gt_3]]) j
  = [
      ([SIndex 1], JStr "abcd");
      ([SIndex 3], JStr "hello")
    ].
Proof. reflexivity. Qed.

(* ---------- Descendant semantics ---------- *)

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

(* ---------- Regex functions: match/search ---------- *)

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

(* ---------- Edge cases ---------- *)

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
(* Out-of-bounds contradiction lemma (unchanged) *)
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

(* ------------------------------------------------------------ *)
(* Extraction *)
(* ------------------------------------------------------------ *)

Require Extraction.
Extraction Language OCaml.

Extraction "jsonpath_exec.ml"
  JSON.value JSON.step JSON.path JSON.node
  JSONPath.prim JSONPath.cmp JSONPath.regex
  JSONPath.aexpr JSONPath.fexpr JSONPath.selector
  JSONPath.segment JSONPath.query JSONPath.q_segs
  Exec.eval_exec.

(*******************************************************)
(* A very difficult, naturalistic end-to-end example   *)
(* exercising RFC9535 features in one real-ish domain. *)
(*******************************************************)

(* --- Reusable bits --- *)
Import Exec.

(* Small regexes used in filters *)
Definition re_at : JSONPath.regex := RChr "@"%char.
Definition re_dotcom : JSONPath.regex :=
  RCat (RChr "."%char)
   (RCat (RChr "c"%char) (RCat (RChr "o"%char) (RChr "m"%char))).

(* --- Projects (as separate constants so expected results are exact) --- *)
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

(* --- Employees --- *)
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

(* --- Departments --- *)
Definition dept_research : JSON.value :=
  JObject [("name", JStr "Research");
           ("employees", JArr [emp_alice; emp_bob; emp_carol])].

Definition dept_sales : JSON.value :=
  JObject [("name", JStr "Sales");
           ("employees", JArr [emp_dave; emp_erin])].

(* --- Whole document --- *)
Definition company_json : JSON.value :=
  JObject [("company", JStr "Acme");
           ("departments", JArr [dept_research; dept_sales]);
           ("meta", JObject [("version", JStr "1.0"); ("rev", JQ 7)])].

(*************************************************************)
(* Query 1: Select employees who (age>30) AND (>=2 tags) AND  *)
(*          (email contains '@' AND '.com'). Return the whole *)
(*          employee objects, in document order.              *)
(*************************************************************)

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
    (* Research[0] alice *)
    ([SName "departments"; SIndex 0; SName "employees"; SIndex 0], emp_alice);

    (* Research[2] carol *)
    ([SName "departments"; SIndex 0; SName "employees"; SIndex 2], emp_carol);

    (* Sales[0] dave *)
    ([SName "departments"; SIndex 1; SName "employees"; SIndex 0], emp_dave)
  ].
Proof. reflexivity. Qed.

(************************************************************************)
(* Query 2: From every 'projects' array anywhere in the doc, pick the   *)
(*          last element (negative index) and then return its 'name'.   *)
(*          Exercises Desc, negative index, and field selection.        *)
(************************************************************************)

Example exec_naturalistic_last_project_names :
  eval_exec
    (Query [ Desc  [SelName "projects"];
             Child [SelIndex (-1)];
             Child [SelName "name"] ])
    company_json
  =
  [
    (* Research/alice last project = "drake" *)
    ([SName "departments"; SIndex 0; SName "employees"; SIndex 0;
      SName "projects"; SIndex (-1); SName "name"], JStr "drake");

    (* Research/carol last project = "eagle" *)
    ([SName "departments"; SIndex 0; SName "employees"; SIndex 2;
      SName "projects"; SIndex (-1); SName "name"], JStr "eagle");

    (* Sales/dave last project = "crm" *)
    ([SName "departments"; SIndex 1; SName "employees"; SIndex 0;
      SName "projects"; SIndex (-1); SName "name"], JStr "crm")
  ].
Proof. reflexivity. Qed.

(******************************************************************************)
(* Query 3: Names of employees who have at least TWO projects with stars>=15. *)
(*          Uses nested filter and ACount; returns names in document order.   *)
(******************************************************************************)

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

(******************************************************************)
(* Query 4: Lexicographic (ASCII) string comparison sanity check: *)
(*          pick employee names strictly less than "c".           *)
(******************************************************************)

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
