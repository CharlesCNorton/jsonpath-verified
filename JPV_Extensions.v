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

End UnicodeJSON.

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

