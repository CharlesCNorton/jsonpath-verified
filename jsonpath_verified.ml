open Ascii
open BinInt
open Bool
open Datatypes
open List0
open Nat
open QArith_base
open String0

(** val index_zip : 'a1 list -> (nat * 'a1) list **)

let index_zip xs =
  combine (seq O (Datatypes.length xs)) xs

(** val str_ltb : char list -> char list -> bool **)

let rec str_ltb s1 s2 =
  match s1 with
  | [] -> (match s2 with
           | [] -> false
           | _::_ -> true)
  | a1::r1 ->
    (match s2 with
     | [] -> false
     | a2::r2 ->
       if PeanoNat.Nat.ltb (nat_of_ascii a1) (nat_of_ascii a2)
       then true
       else if (=) a1 a2 then str_ltb r1 r2 else false)

(** val coq_Q_of_Z : Big_int_Z.big_int -> coq_Q **)

let coq_Q_of_Z =
  inject_Z

(** val coq_Q_of_nat : nat -> coq_Q **)

let coq_Q_of_nat n =
  inject_Z (Z.of_nat n)

module JSON =
 struct
  type value =
  | JNull
  | JBool of bool
  | JNum of coq_Q
  | JStr of char list
  | JArr of value list
  | JObject of (char list * value) list

  (** val value_rect :
      'a1 -> (bool -> 'a1) -> (coq_Q -> 'a1) -> (char list -> 'a1) -> (value
      list -> 'a1) -> ((char list * value) list -> 'a1) -> value -> 'a1 **)

  let value_rect f f0 f1 f2 f3 f4 = function
  | JNull -> f
  | JBool b -> f0 b
  | JNum n -> f1 n
  | JStr s -> f2 s
  | JArr xs -> f3 xs
  | JObject fields -> f4 fields

  (** val value_rec :
      'a1 -> (bool -> 'a1) -> (coq_Q -> 'a1) -> (char list -> 'a1) -> (value
      list -> 'a1) -> ((char list * value) list -> 'a1) -> value -> 'a1 **)

  let value_rec f f0 f1 f2 f3 f4 = function
  | JNull -> f
  | JBool b -> f0 b
  | JNum n -> f1 n
  | JStr s -> f2 s
  | JArr xs -> f3 xs
  | JObject fields -> f4 fields

  type step =
  | SName of char list
  | SIndex of Big_int_Z.big_int

  (** val step_rect :
      (char list -> 'a1) -> (Big_int_Z.big_int -> 'a1) -> step -> 'a1 **)

  let step_rect f f0 = function
  | SName s0 -> f s0
  | SIndex i -> f0 i

  (** val step_rec :
      (char list -> 'a1) -> (Big_int_Z.big_int -> 'a1) -> step -> 'a1 **)

  let step_rec f f0 = function
  | SName s0 -> f s0
  | SIndex i -> f0 i

  type path = step list

  type node = path * value
 end

(** val mk_node : JSON.path -> JSON.value -> JSON.node **)

let mk_node p v =
  (p, v)

module JSONPath =
 struct
  type prim =
  | PNull
  | PBool of bool
  | PNum of coq_Q
  | PStr of char list

  (** val prim_rect :
      'a1 -> (bool -> 'a1) -> (coq_Q -> 'a1) -> (char list -> 'a1) -> prim ->
      'a1 **)

  let prim_rect f f0 f1 f2 = function
  | PNull -> f
  | PBool b -> f0 b
  | PNum n -> f1 n
  | PStr s -> f2 s

  (** val prim_rec :
      'a1 -> (bool -> 'a1) -> (coq_Q -> 'a1) -> (char list -> 'a1) -> prim ->
      'a1 **)

  let prim_rec f f0 f1 f2 = function
  | PNull -> f
  | PBool b -> f0 b
  | PNum n -> f1 n
  | PStr s -> f2 s

  (** val prim_of_value : JSON.value -> prim option **)

  let prim_of_value = function
  | JSON.JNull -> Some PNull
  | JSON.JBool b -> Some (PBool b)
  | JSON.JNum n -> Some (PNum n)
  | JSON.JStr s -> Some (PStr s)
  | _ -> None

  type cmp =
  | CEq
  | CNe
  | CLt
  | CLe
  | CGt
  | CGe

  (** val cmp_rect : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> cmp -> 'a1 **)

  let cmp_rect f f0 f1 f2 f3 f4 = function
  | CEq -> f
  | CNe -> f0
  | CLt -> f1
  | CLe -> f2
  | CGt -> f3
  | CGe -> f4

  (** val cmp_rec : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> cmp -> 'a1 **)

  let cmp_rec f f0 f1 f2 f3 f4 = function
  | CEq -> f
  | CNe -> f0
  | CLt -> f1
  | CLe -> f2
  | CGt -> f3
  | CGe -> f4

  type regex =
  | REmpty
  | REps
  | RChr of char
  | RAny
  | RAlt of regex * regex
  | RCat of regex * regex
  | RStar of regex
  | RPlus of regex
  | ROpt of regex
  | RRepeat of regex * nat * nat
  | RCharClass of bool * char list

  (** val regex_rect :
      'a1 -> 'a1 -> (char -> 'a1) -> 'a1 -> (regex -> 'a1 -> regex -> 'a1 ->
      'a1) -> (regex -> 'a1 -> regex -> 'a1 -> 'a1) -> (regex -> 'a1 -> 'a1)
      -> (regex -> 'a1 -> 'a1) -> (regex -> 'a1 -> 'a1) -> (regex -> 'a1 ->
      nat -> nat -> 'a1) -> (bool -> char list -> 'a1) -> regex -> 'a1 **)

  let rec regex_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 = function
  | REmpty -> f
  | REps -> f0
  | RChr c -> f1 c
  | RAny -> f2
  | RAlt (r1, r2) ->
    f3 r1 (regex_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 r1) r2
      (regex_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 r2)
  | RCat (r1, r2) ->
    f4 r1 (regex_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 r1) r2
      (regex_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 r2)
  | RStar r0 -> f5 r0 (regex_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 r0)
  | RPlus r0 -> f6 r0 (regex_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 r0)
  | ROpt r0 -> f7 r0 (regex_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 r0)
  | RRepeat (r0, min0, max0) ->
    f8 r0 (regex_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 r0) min0 max0
  | RCharClass (neg, chars) -> f9 neg chars

  (** val regex_rec :
      'a1 -> 'a1 -> (char -> 'a1) -> 'a1 -> (regex -> 'a1 -> regex -> 'a1 ->
      'a1) -> (regex -> 'a1 -> regex -> 'a1 -> 'a1) -> (regex -> 'a1 -> 'a1)
      -> (regex -> 'a1 -> 'a1) -> (regex -> 'a1 -> 'a1) -> (regex -> 'a1 ->
      nat -> nat -> 'a1) -> (bool -> char list -> 'a1) -> regex -> 'a1 **)

  let rec regex_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 = function
  | REmpty -> f
  | REps -> f0
  | RChr c -> f1 c
  | RAny -> f2
  | RAlt (r1, r2) ->
    f3 r1 (regex_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 r1) r2
      (regex_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 r2)
  | RCat (r1, r2) ->
    f4 r1 (regex_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 r1) r2
      (regex_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 r2)
  | RStar r0 -> f5 r0 (regex_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 r0)
  | RPlus r0 -> f6 r0 (regex_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 r0)
  | ROpt r0 -> f7 r0 (regex_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 r0)
  | RRepeat (r0, min0, max0) ->
    f8 r0 (regex_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 r0) min0 max0
  | RCharClass (neg, chars) -> f9 neg chars

  type aexpr =
  | APrim of prim
  | ACount of query
  | AValue of query
  | ALengthV of query
  and fexpr =
  | FTrue
  | FNot of fexpr
  | FAnd of fexpr * fexpr
  | FOr of fexpr * fexpr
  | FExists of query
  | FCmp of cmp * aexpr * aexpr
  | FMatch of aexpr * regex
  | FSearch of aexpr * regex
  and selector =
  | SelName of char list
  | SelWildcard
  | SelIndex of Big_int_Z.big_int
  | SelSlice of Big_int_Z.big_int option * Big_int_Z.big_int option
     * Big_int_Z.big_int
  | SelFilter of fexpr
  and segment =
  | Child of selector list
  | Desc of selector list
  and query =
  | Query of segment list

  (** val aexpr_rect :
      (prim -> 'a1) -> (query -> 'a1) -> (query -> 'a1) -> (query -> 'a1) ->
      aexpr -> 'a1 **)

  let aexpr_rect f f0 f1 f2 = function
  | APrim p -> f p
  | ACount q -> f0 q
  | AValue q -> f1 q
  | ALengthV q -> f2 q

  (** val aexpr_rec :
      (prim -> 'a1) -> (query -> 'a1) -> (query -> 'a1) -> (query -> 'a1) ->
      aexpr -> 'a1 **)

  let aexpr_rec f f0 f1 f2 = function
  | APrim p -> f p
  | ACount q -> f0 q
  | AValue q -> f1 q
  | ALengthV q -> f2 q

  (** val fexpr_rect :
      'a1 -> (fexpr -> 'a1 -> 'a1) -> (fexpr -> 'a1 -> fexpr -> 'a1 -> 'a1)
      -> (fexpr -> 'a1 -> fexpr -> 'a1 -> 'a1) -> (query -> 'a1) -> (cmp ->
      aexpr -> aexpr -> 'a1) -> (aexpr -> regex -> 'a1) -> (aexpr -> regex ->
      'a1) -> fexpr -> 'a1 **)

  let rec fexpr_rect f f0 f1 f2 f3 f4 f5 f6 = function
  | FTrue -> f
  | FNot f8 -> f0 f8 (fexpr_rect f f0 f1 f2 f3 f4 f5 f6 f8)
  | FAnd (f8, g) ->
    f1 f8 (fexpr_rect f f0 f1 f2 f3 f4 f5 f6 f8) g
      (fexpr_rect f f0 f1 f2 f3 f4 f5 f6 g)
  | FOr (f8, g) ->
    f2 f8 (fexpr_rect f f0 f1 f2 f3 f4 f5 f6 f8) g
      (fexpr_rect f f0 f1 f2 f3 f4 f5 f6 g)
  | FExists q -> f3 q
  | FCmp (op, a, b) -> f4 op a b
  | FMatch (a, r) -> f5 a r
  | FSearch (a, r) -> f6 a r

  (** val fexpr_rec :
      'a1 -> (fexpr -> 'a1 -> 'a1) -> (fexpr -> 'a1 -> fexpr -> 'a1 -> 'a1)
      -> (fexpr -> 'a1 -> fexpr -> 'a1 -> 'a1) -> (query -> 'a1) -> (cmp ->
      aexpr -> aexpr -> 'a1) -> (aexpr -> regex -> 'a1) -> (aexpr -> regex ->
      'a1) -> fexpr -> 'a1 **)

  let rec fexpr_rec f f0 f1 f2 f3 f4 f5 f6 = function
  | FTrue -> f
  | FNot f8 -> f0 f8 (fexpr_rec f f0 f1 f2 f3 f4 f5 f6 f8)
  | FAnd (f8, g) ->
    f1 f8 (fexpr_rec f f0 f1 f2 f3 f4 f5 f6 f8) g
      (fexpr_rec f f0 f1 f2 f3 f4 f5 f6 g)
  | FOr (f8, g) ->
    f2 f8 (fexpr_rec f f0 f1 f2 f3 f4 f5 f6 f8) g
      (fexpr_rec f f0 f1 f2 f3 f4 f5 f6 g)
  | FExists q -> f3 q
  | FCmp (op, a, b) -> f4 op a b
  | FMatch (a, r) -> f5 a r
  | FSearch (a, r) -> f6 a r

  (** val selector_rect :
      (char list -> 'a1) -> 'a1 -> (Big_int_Z.big_int -> 'a1) ->
      (Big_int_Z.big_int option -> Big_int_Z.big_int option ->
      Big_int_Z.big_int -> 'a1) -> (fexpr -> 'a1) -> selector -> 'a1 **)

  let selector_rect f f0 f1 f2 f3 = function
  | SelName s0 -> f s0
  | SelWildcard -> f0
  | SelIndex i -> f1 i
  | SelSlice (start, end_, stp) -> f2 start end_ stp
  | SelFilter f4 -> f3 f4

  (** val selector_rec :
      (char list -> 'a1) -> 'a1 -> (Big_int_Z.big_int -> 'a1) ->
      (Big_int_Z.big_int option -> Big_int_Z.big_int option ->
      Big_int_Z.big_int -> 'a1) -> (fexpr -> 'a1) -> selector -> 'a1 **)

  let selector_rec f f0 f1 f2 f3 = function
  | SelName s0 -> f s0
  | SelWildcard -> f0
  | SelIndex i -> f1 i
  | SelSlice (start, end_, stp) -> f2 start end_ stp
  | SelFilter f4 -> f3 f4

  (** val segment_rect :
      (selector list -> 'a1) -> (selector list -> 'a1) -> segment -> 'a1 **)

  let segment_rect f f0 = function
  | Child sels -> f sels
  | Desc sels -> f0 sels

  (** val segment_rec :
      (selector list -> 'a1) -> (selector list -> 'a1) -> segment -> 'a1 **)

  let segment_rec f f0 = function
  | Child sels -> f sels
  | Desc sels -> f0 sels

  (** val query_rect : (segment list -> 'a1) -> query -> 'a1 **)

  let query_rect f = function
  | Query segs -> f segs

  (** val query_rec : (segment list -> 'a1) -> query -> 'a1 **)

  let query_rec f = function
  | Query segs -> f segs

  (** val q_segs : query -> segment list **)

  let q_segs = function
  | Query ss -> ss
 end

module Regex =
 struct
  (** val nullable : JSONPath.regex -> bool **)

  let rec nullable = function
  | JSONPath.REps -> true
  | JSONPath.RAlt (r1, r2) -> (||) (nullable r1) (nullable r2)
  | JSONPath.RCat (r1, r2) -> (&&) (nullable r1) (nullable r2)
  | JSONPath.RStar _ -> true
  | JSONPath.RPlus r1 -> nullable r1
  | JSONPath.ROpt _ -> true
  | JSONPath.RRepeat (r1, min0, _) ->
    if PeanoNat.Nat.eqb min0 O then true else nullable r1
  | _ -> false

  (** val char_in_list : char -> char list -> bool **)

  let rec char_in_list c = function
  | [] -> false
  | c' :: cs' -> if (=) c c' then true else char_in_list c cs'

  (** val deriv : char -> JSONPath.regex -> JSONPath.regex **)

  let rec deriv a = function
  | JSONPath.RChr c -> if (=) a c then JSONPath.REps else JSONPath.REmpty
  | JSONPath.RAny -> JSONPath.REps
  | JSONPath.RAlt (r1, r2) -> JSONPath.RAlt ((deriv a r1), (deriv a r2))
  | JSONPath.RCat (r1, r2) ->
    let d1 = deriv a r1 in
    let d2 = deriv a r2 in
    if let rec nullable0 = function
       | JSONPath.REps -> true
       | JSONPath.RAlt (r3, r4) -> (||) (nullable0 r3) (nullable0 r4)
       | JSONPath.RCat (r3, r4) -> (&&) (nullable0 r3) (nullable0 r4)
       | JSONPath.RStar _ -> true
       | JSONPath.RPlus r3 -> nullable0 r3
       | JSONPath.ROpt _ -> true
       | JSONPath.RRepeat (r3, min0, _) ->
         if PeanoNat.Nat.eqb min0 O then true else nullable0 r3
       | _ -> false
       in nullable0 r1
    then JSONPath.RAlt ((JSONPath.RCat (d1, r2)), d2)
    else JSONPath.RCat (d1, r2)
  | JSONPath.RStar r1 -> JSONPath.RCat ((deriv a r1), (JSONPath.RStar r1))
  | JSONPath.RPlus r1 -> JSONPath.RCat ((deriv a r1), (JSONPath.RStar r1))
  | JSONPath.ROpt r1 -> deriv a r1
  | JSONPath.RRepeat (r1, min0, max0) ->
    if PeanoNat.Nat.eqb min0 O
    then if PeanoNat.Nat.eqb max0 O
         then JSONPath.REmpty
         else JSONPath.RAlt ((JSONPath.RCat ((deriv a r1), (JSONPath.RRepeat
                (r1, O, (sub max0 (S O)))))), JSONPath.REmpty)
    else JSONPath.RCat ((deriv a r1), (JSONPath.RRepeat (r1,
           (sub min0 (S O)), (sub max0 (S O)))))
  | JSONPath.RCharClass (neg, cs) ->
    let matches = char_in_list a cs in
    if negb neg
    then if matches then JSONPath.REps else JSONPath.REmpty
    else if matches then JSONPath.REmpty else JSONPath.REps
  | _ -> JSONPath.REmpty

  (** val rsimpl : JSONPath.regex -> JSONPath.regex **)

  let rec rsimpl r = match r with
  | JSONPath.RAlt (r1, r2) ->
    let r1' = rsimpl r1 in
    let r2' = rsimpl r2 in
    (match r1' with
     | JSONPath.REmpty -> r2'
     | _ ->
       (match r2' with
        | JSONPath.REmpty -> r1'
        | _ -> JSONPath.RAlt (r1', r2')))
  | JSONPath.RCat (r1, r2) ->
    let r1' = rsimpl r1 in
    let r2' = rsimpl r2 in
    (match r1' with
     | JSONPath.REmpty -> JSONPath.REmpty
     | JSONPath.REps ->
       (match r2' with
        | JSONPath.REmpty -> JSONPath.REmpty
        | _ -> r2')
     | _ ->
       (match r2' with
        | JSONPath.REmpty -> JSONPath.REmpty
        | JSONPath.REps -> r1'
        | _ -> JSONPath.RCat (r1', r2')))
  | JSONPath.RStar r1 ->
    let r1' = rsimpl r1 in
    (match r1' with
     | JSONPath.REmpty -> JSONPath.REps
     | JSONPath.REps -> JSONPath.REps
     | _ -> JSONPath.RStar r1')
  | JSONPath.RPlus r1 ->
    let r1' = rsimpl r1 in
    (match r1' with
     | JSONPath.REmpty -> JSONPath.REmpty
     | _ -> JSONPath.RPlus r1')
  | JSONPath.ROpt r1 -> let r1' = rsimpl r1 in JSONPath.ROpt r1'
  | JSONPath.RRepeat (r1, min0, max0) ->
    let r1' = rsimpl r1 in
    if PeanoNat.Nat.ltb max0 min0
    then JSONPath.REmpty
    else if PeanoNat.Nat.eqb min0 O
         then if PeanoNat.Nat.eqb max0 O
              then JSONPath.REps
              else JSONPath.RRepeat (r1', min0, max0)
         else JSONPath.RRepeat (r1', min0, max0)
  | _ -> r

  (** val deriv_simpl : char -> JSONPath.regex -> JSONPath.regex **)

  let deriv_simpl a r =
    let rec rsimpl0 r0 = match r0 with
    | JSONPath.RAlt (r1, r2) ->
      let r1' = rsimpl0 r1 in
      let r2' = rsimpl0 r2 in
      (match r1' with
       | JSONPath.REmpty -> r2'
       | _ ->
         (match r2' with
          | JSONPath.REmpty -> r1'
          | _ -> JSONPath.RAlt (r1', r2')))
    | JSONPath.RCat (r1, r2) ->
      let r1' = rsimpl0 r1 in
      let r2' = rsimpl0 r2 in
      (match r1' with
       | JSONPath.REmpty -> JSONPath.REmpty
       | JSONPath.REps ->
         (match r2' with
          | JSONPath.REmpty -> JSONPath.REmpty
          | _ -> r2')
       | _ ->
         (match r2' with
          | JSONPath.REmpty -> JSONPath.REmpty
          | JSONPath.REps -> r1'
          | _ -> JSONPath.RCat (r1', r2')))
    | JSONPath.RStar r1 ->
      let r1' = rsimpl0 r1 in
      (match r1' with
       | JSONPath.REmpty -> JSONPath.REps
       | JSONPath.REps -> JSONPath.REps
       | _ -> JSONPath.RStar r1')
    | JSONPath.RPlus r1 ->
      let r1' = rsimpl0 r1 in
      (match r1' with
       | JSONPath.REmpty -> JSONPath.REmpty
       | _ -> JSONPath.RPlus r1')
    | JSONPath.ROpt r1 -> let r1' = rsimpl0 r1 in JSONPath.ROpt r1'
    | JSONPath.RRepeat (r1, min0, max0) ->
      let r1' = rsimpl0 r1 in
      if PeanoNat.Nat.ltb max0 min0
      then JSONPath.REmpty
      else if PeanoNat.Nat.eqb min0 O
           then if PeanoNat.Nat.eqb max0 O
                then JSONPath.REps
                else JSONPath.RRepeat (r1', min0, max0)
           else JSONPath.RRepeat (r1', min0, max0)
    | _ -> r0
    in rsimpl0
         (let rec deriv0 a0 = function
          | JSONPath.RChr c ->
            if (=) a0 c then JSONPath.REps else JSONPath.REmpty
          | JSONPath.RAny -> JSONPath.REps
          | JSONPath.RAlt (r1, r2) ->
            JSONPath.RAlt ((deriv0 a0 r1), (deriv0 a0 r2))
          | JSONPath.RCat (r1, r2) ->
            let d1 = deriv0 a0 r1 in
            let d2 = deriv0 a0 r2 in
            if let rec nullable0 = function
               | JSONPath.REps -> true
               | JSONPath.RAlt (r4, r5) -> (||) (nullable0 r4) (nullable0 r5)
               | JSONPath.RCat (r4, r5) -> (&&) (nullable0 r4) (nullable0 r5)
               | JSONPath.RStar _ -> true
               | JSONPath.RPlus r4 -> nullable0 r4
               | JSONPath.ROpt _ -> true
               | JSONPath.RRepeat (r4, min0, _) ->
                 if PeanoNat.Nat.eqb min0 O then true else nullable0 r4
               | _ -> false
               in nullable0 r1
            then JSONPath.RAlt ((JSONPath.RCat (d1, r2)), d2)
            else JSONPath.RCat (d1, r2)
          | JSONPath.RStar r1 ->
            JSONPath.RCat ((deriv0 a0 r1), (JSONPath.RStar r1))
          | JSONPath.RPlus r1 ->
            JSONPath.RCat ((deriv0 a0 r1), (JSONPath.RStar r1))
          | JSONPath.ROpt r1 -> deriv0 a0 r1
          | JSONPath.RRepeat (r1, min0, max0) ->
            if PeanoNat.Nat.eqb min0 O
            then if PeanoNat.Nat.eqb max0 O
                 then JSONPath.REmpty
                 else JSONPath.RAlt ((JSONPath.RCat ((deriv0 a0 r1),
                        (JSONPath.RRepeat (r1, O, (sub max0 (S O)))))),
                        JSONPath.REmpty)
            else JSONPath.RCat ((deriv0 a0 r1), (JSONPath.RRepeat (r1,
                   (sub min0 (S O)), (sub max0 (S O)))))
          | JSONPath.RCharClass (neg, cs) ->
            let matches = char_in_list a0 cs in
            if negb neg
            then if matches then JSONPath.REps else JSONPath.REmpty
            else if matches then JSONPath.REmpty else JSONPath.REps
          | _ -> JSONPath.REmpty
          in deriv0 a r)

  (** val list_of_string : char list -> char list **)

  let rec list_of_string = function
  | [] -> []
  | a::s' -> a :: (list_of_string s')

  (** val matches_from : JSONPath.regex -> char list -> bool **)

  let rec matches_from r = function
  | [] ->
    let rec nullable0 = function
    | JSONPath.REps -> true
    | JSONPath.RAlt (r1, r2) -> (||) (nullable0 r1) (nullable0 r2)
    | JSONPath.RCat (r1, r2) -> (&&) (nullable0 r1) (nullable0 r2)
    | JSONPath.RStar _ -> true
    | JSONPath.RPlus r1 -> nullable0 r1
    | JSONPath.ROpt _ -> true
    | JSONPath.RRepeat (r1, min0, _) ->
      if PeanoNat.Nat.eqb min0 O then true else nullable0 r1
    | _ -> false
    in nullable0 r
  | a :: cs' ->
    matches_from
      (let rec rsimpl0 r0 = match r0 with
       | JSONPath.RAlt (r1, r2) ->
         let r1' = rsimpl0 r1 in
         let r2' = rsimpl0 r2 in
         (match r1' with
          | JSONPath.REmpty -> r2'
          | _ ->
            (match r2' with
             | JSONPath.REmpty -> r1'
             | _ -> JSONPath.RAlt (r1', r2')))
       | JSONPath.RCat (r1, r2) ->
         let r1' = rsimpl0 r1 in
         let r2' = rsimpl0 r2 in
         (match r1' with
          | JSONPath.REmpty -> JSONPath.REmpty
          | JSONPath.REps ->
            (match r2' with
             | JSONPath.REmpty -> JSONPath.REmpty
             | _ -> r2')
          | _ ->
            (match r2' with
             | JSONPath.REmpty -> JSONPath.REmpty
             | JSONPath.REps -> r1'
             | _ -> JSONPath.RCat (r1', r2')))
       | JSONPath.RStar r1 ->
         let r1' = rsimpl0 r1 in
         (match r1' with
          | JSONPath.REmpty -> JSONPath.REps
          | JSONPath.REps -> JSONPath.REps
          | _ -> JSONPath.RStar r1')
       | JSONPath.RPlus r1 ->
         let r1' = rsimpl0 r1 in
         (match r1' with
          | JSONPath.REmpty -> JSONPath.REmpty
          | _ -> JSONPath.RPlus r1')
       | JSONPath.ROpt r1 -> let r1' = rsimpl0 r1 in JSONPath.ROpt r1'
       | JSONPath.RRepeat (r1, min0, max0) ->
         let r1' = rsimpl0 r1 in
         if PeanoNat.Nat.ltb max0 min0
         then JSONPath.REmpty
         else if PeanoNat.Nat.eqb min0 O
              then if PeanoNat.Nat.eqb max0 O
                   then JSONPath.REps
                   else JSONPath.RRepeat (r1', min0, max0)
              else JSONPath.RRepeat (r1', min0, max0)
       | _ -> r0
       in rsimpl0
            (let rec deriv0 a0 = function
             | JSONPath.RChr c ->
               if (=) a0 c then JSONPath.REps else JSONPath.REmpty
             | JSONPath.RAny -> JSONPath.REps
             | JSONPath.RAlt (r1, r2) ->
               JSONPath.RAlt ((deriv0 a0 r1), (deriv0 a0 r2))
             | JSONPath.RCat (r1, r2) ->
               let d1 = deriv0 a0 r1 in
               let d2 = deriv0 a0 r2 in
               if let rec nullable0 = function
                  | JSONPath.REps -> true
                  | JSONPath.RAlt (r4, r5) ->
                    (||) (nullable0 r4) (nullable0 r5)
                  | JSONPath.RCat (r4, r5) ->
                    (&&) (nullable0 r4) (nullable0 r5)
                  | JSONPath.RStar _ -> true
                  | JSONPath.RPlus r4 -> nullable0 r4
                  | JSONPath.ROpt _ -> true
                  | JSONPath.RRepeat (r4, min0, _) ->
                    if PeanoNat.Nat.eqb min0 O then true else nullable0 r4
                  | _ -> false
                  in nullable0 r1
               then JSONPath.RAlt ((JSONPath.RCat (d1, r2)), d2)
               else JSONPath.RCat (d1, r2)
             | JSONPath.RStar r1 ->
               JSONPath.RCat ((deriv0 a0 r1), (JSONPath.RStar r1))
             | JSONPath.RPlus r1 ->
               JSONPath.RCat ((deriv0 a0 r1), (JSONPath.RStar r1))
             | JSONPath.ROpt r1 -> deriv0 a0 r1
             | JSONPath.RRepeat (r1, min0, max0) ->
               if PeanoNat.Nat.eqb min0 O
               then if PeanoNat.Nat.eqb max0 O
                    then JSONPath.REmpty
                    else JSONPath.RAlt ((JSONPath.RCat ((deriv0 a0 r1),
                           (JSONPath.RRepeat (r1, O, (sub max0 (S O)))))),
                           JSONPath.REmpty)
               else JSONPath.RCat ((deriv0 a0 r1), (JSONPath.RRepeat (r1,
                      (sub min0 (S O)), (sub max0 (S O)))))
             | JSONPath.RCharClass (neg, cs0) ->
               let matches = char_in_list a0 cs0 in
               if negb neg
               then if matches then JSONPath.REps else JSONPath.REmpty
               else if matches then JSONPath.REmpty else JSONPath.REps
             | _ -> JSONPath.REmpty
             in deriv0 a r)) cs'

  (** val regex_match : JSONPath.regex -> char list -> bool **)

  let regex_match r s =
    let rec matches_from0 r0 = function
    | [] ->
      let rec nullable0 = function
      | JSONPath.REps -> true
      | JSONPath.RAlt (r2, r3) -> (||) (nullable0 r2) (nullable0 r3)
      | JSONPath.RCat (r2, r3) -> (&&) (nullable0 r2) (nullable0 r3)
      | JSONPath.RStar _ -> true
      | JSONPath.RPlus r2 -> nullable0 r2
      | JSONPath.ROpt _ -> true
      | JSONPath.RRepeat (r2, min0, _) ->
        if PeanoNat.Nat.eqb min0 O then true else nullable0 r2
      | _ -> false
      in nullable0 r0
    | a :: cs' ->
      matches_from0
        (let rec rsimpl0 r1 = match r1 with
         | JSONPath.RAlt (r2, r3) ->
           let r1' = rsimpl0 r2 in
           let r2' = rsimpl0 r3 in
           (match r1' with
            | JSONPath.REmpty -> r2'
            | _ ->
              (match r2' with
               | JSONPath.REmpty -> r1'
               | _ -> JSONPath.RAlt (r1', r2')))
         | JSONPath.RCat (r2, r3) ->
           let r1' = rsimpl0 r2 in
           let r2' = rsimpl0 r3 in
           (match r1' with
            | JSONPath.REmpty -> JSONPath.REmpty
            | JSONPath.REps ->
              (match r2' with
               | JSONPath.REmpty -> JSONPath.REmpty
               | _ -> r2')
            | _ ->
              (match r2' with
               | JSONPath.REmpty -> JSONPath.REmpty
               | JSONPath.REps -> r1'
               | _ -> JSONPath.RCat (r1', r2')))
         | JSONPath.RStar r2 ->
           let r1' = rsimpl0 r2 in
           (match r1' with
            | JSONPath.REmpty -> JSONPath.REps
            | JSONPath.REps -> JSONPath.REps
            | _ -> JSONPath.RStar r1')
         | JSONPath.RPlus r2 ->
           let r1' = rsimpl0 r2 in
           (match r1' with
            | JSONPath.REmpty -> JSONPath.REmpty
            | _ -> JSONPath.RPlus r1')
         | JSONPath.ROpt r2 -> let r1' = rsimpl0 r2 in JSONPath.ROpt r1'
         | JSONPath.RRepeat (r2, min0, max0) ->
           let r1' = rsimpl0 r2 in
           if PeanoNat.Nat.ltb max0 min0
           then JSONPath.REmpty
           else if PeanoNat.Nat.eqb min0 O
                then if PeanoNat.Nat.eqb max0 O
                     then JSONPath.REps
                     else JSONPath.RRepeat (r1', min0, max0)
                else JSONPath.RRepeat (r1', min0, max0)
         | _ -> r1
         in rsimpl0
              (let rec deriv0 a0 = function
               | JSONPath.RChr c ->
                 if (=) a0 c then JSONPath.REps else JSONPath.REmpty
               | JSONPath.RAny -> JSONPath.REps
               | JSONPath.RAlt (r2, r3) ->
                 JSONPath.RAlt ((deriv0 a0 r2), (deriv0 a0 r3))
               | JSONPath.RCat (r2, r3) ->
                 let d1 = deriv0 a0 r2 in
                 let d2 = deriv0 a0 r3 in
                 if let rec nullable0 = function
                    | JSONPath.REps -> true
                    | JSONPath.RAlt (r5, r6) ->
                      (||) (nullable0 r5) (nullable0 r6)
                    | JSONPath.RCat (r5, r6) ->
                      (&&) (nullable0 r5) (nullable0 r6)
                    | JSONPath.RStar _ -> true
                    | JSONPath.RPlus r5 -> nullable0 r5
                    | JSONPath.ROpt _ -> true
                    | JSONPath.RRepeat (r5, min0, _) ->
                      if PeanoNat.Nat.eqb min0 O then true else nullable0 r5
                    | _ -> false
                    in nullable0 r2
                 then JSONPath.RAlt ((JSONPath.RCat (d1, r3)), d2)
                 else JSONPath.RCat (d1, r3)
               | JSONPath.RStar r2 ->
                 JSONPath.RCat ((deriv0 a0 r2), (JSONPath.RStar r2))
               | JSONPath.RPlus r2 ->
                 JSONPath.RCat ((deriv0 a0 r2), (JSONPath.RStar r2))
               | JSONPath.ROpt r2 -> deriv0 a0 r2
               | JSONPath.RRepeat (r2, min0, max0) ->
                 if PeanoNat.Nat.eqb min0 O
                 then if PeanoNat.Nat.eqb max0 O
                      then JSONPath.REmpty
                      else JSONPath.RAlt ((JSONPath.RCat ((deriv0 a0 r2),
                             (JSONPath.RRepeat (r2, O, (sub max0 (S O)))))),
                             JSONPath.REmpty)
                 else JSONPath.RCat ((deriv0 a0 r2), (JSONPath.RRepeat (r2,
                        (sub min0 (S O)), (sub max0 (S O)))))
               | JSONPath.RCharClass (neg, cs0) ->
                 let matches = char_in_list a0 cs0 in
                 if negb neg
                 then if matches then JSONPath.REps else JSONPath.REmpty
                 else if matches then JSONPath.REmpty else JSONPath.REps
               | _ -> JSONPath.REmpty
               in deriv0 a r0)) cs'
    in matches_from0 r
         (let rec list_of_string0 = function
          | [] -> []
          | a::s' -> a :: (list_of_string0 s')
          in list_of_string0 s)

  (** val regex_search : JSONPath.regex -> char list -> bool **)

  let regex_search r s =
    regex_match (JSONPath.RCat ((JSONPath.RStar JSONPath.RAny),
      (JSONPath.RCat (r, (JSONPath.RStar JSONPath.RAny))))) s
 end

module Exec =
 struct
  (** val prim_eq : JSONPath.prim -> JSONPath.prim -> bool **)

  let prim_eq p q =
    match p with
    | JSONPath.PNull -> (match q with
                         | JSONPath.PNull -> true
                         | _ -> false)
    | JSONPath.PBool b1 ->
      (match q with
       | JSONPath.PBool b2 -> eqb b1 b2
       | _ -> false)
    | JSONPath.PNum n1 ->
      (match q with
       | JSONPath.PNum n2 ->
         (match coq_Qcompare n1 n2 with
          | Eq -> true
          | _ -> false)
       | _ -> false)
    | JSONPath.PStr s1 ->
      (match q with
       | JSONPath.PStr s2 -> if string_dec s1 s2 then true else false
       | _ -> false)

  (** val prim_lt : JSONPath.prim -> JSONPath.prim -> bool **)

  let prim_lt p q =
    match p with
    | JSONPath.PNum n1 ->
      (match q with
       | JSONPath.PNum n2 ->
         (match coq_Qcompare n1 n2 with
          | Lt -> true
          | _ -> false)
       | _ -> false)
    | JSONPath.PStr s1 ->
      (match q with
       | JSONPath.PStr s2 -> str_ltb s1 s2
       | _ -> false)
    | _ -> false

  (** val cmp_prim :
      JSONPath.cmp -> JSONPath.prim -> JSONPath.prim -> bool **)

  let cmp_prim op x y =
    match op with
    | JSONPath.CEq -> prim_eq x y
    | JSONPath.CNe -> negb (prim_eq x y)
    | JSONPath.CLt -> prim_lt x y
    | JSONPath.CLe -> (||) (prim_lt x y) (prim_eq x y)
    | JSONPath.CGt -> prim_lt y x
    | JSONPath.CGe -> (||) (prim_lt y x) (prim_eq x y)

  (** val sel_exec_nf : JSONPath.selector -> JSON.node -> JSON.node list **)

  let rec sel_exec_nf sel = function
  | (p, v) ->
    (match sel with
     | JSONPath.SelName s ->
       (match v with
        | JSON.JObject fields ->
          (match find (fun kv ->
                   if string_dec (fst kv) s then true else false) fields with
           | Some p0 ->
             let (_, v') = p0 in
             (mk_node (app p ((JSON.SName s) :: [])) v') :: []
           | None -> [])
        | _ -> [])
     | JSONPath.SelWildcard ->
       (match v with
        | JSON.JArr xs ->
          map (fun pat ->
            let (i, v') = pat in
            mk_node (app p ((JSON.SIndex (Z.of_nat i)) :: [])) v')
            (index_zip xs)
        | JSON.JObject fields ->
          map (fun pat ->
            let (k, v') = pat in mk_node (app p ((JSON.SName k) :: [])) v')
            fields
        | _ -> [])
     | JSONPath.SelIndex z ->
       (match v with
        | JSON.JArr xs ->
          let idx =
            if Z.ltb z Big_int_Z.zero_big_int
            then Z.add (Z.of_nat (Datatypes.length xs)) z
            else z
          in
          if (||) (Z.ltb idx Big_int_Z.zero_big_int)
               (Z.geb idx (Z.of_nat (Datatypes.length xs)))
          then []
          else (match nth_error xs (Z.to_nat idx) with
                | Some v' ->
                  (mk_node (app p ((JSON.SIndex idx) :: [])) v') :: []
                | None -> [])
        | _ -> [])
     | JSONPath.SelSlice (st, en, stp) ->
       (match v with
        | JSON.JArr xs ->
          let ns =
            let len = Datatypes.length xs in
            let (p0, st0) =
              let lz = Z.of_nat len in
              if Z.eqb stp Big_int_Z.zero_big_int
              then ((Big_int_Z.zero_big_int, Big_int_Z.zero_big_int),
                     Big_int_Z.zero_big_int)
              else let default_start =
                     if Z.ltb Big_int_Z.zero_big_int stp
                     then Big_int_Z.zero_big_int
                     else Z.sub lz Big_int_Z.unit_big_int
                   in
                   let default_end =
                     if Z.ltb Big_int_Z.zero_big_int stp
                     then lz
                     else Big_int_Z.minus_big_int Big_int_Z.unit_big_int
                   in
                   let s0 =
                     match st with
                     | Some s ->
                       if Z.ltb s Big_int_Z.zero_big_int
                       then Z.add lz s
                       else s
                     | None -> default_start
                   in
                   let e0 =
                     match en with
                     | Some e ->
                       if Z.ltb e Big_int_Z.zero_big_int
                       then Z.add lz e
                       else e
                     | None -> default_end
                   in
                   if Z.ltb Big_int_Z.zero_big_int stp
                   then let s1 = Z.max Big_int_Z.zero_big_int (Z.min lz s0) in
                        let e1 = Z.max Big_int_Z.zero_big_int (Z.min lz e0) in
                        ((s1, e1), stp)
                   else let s1 =
                          Z.max (Big_int_Z.minus_big_int
                            Big_int_Z.unit_big_int)
                            (Z.min (Z.sub lz Big_int_Z.unit_big_int) s0)
                        in
                        let e1 =
                          Z.max (Big_int_Z.minus_big_int
                            Big_int_Z.unit_big_int)
                            (Z.min (Z.sub lz Big_int_Z.unit_big_int) e0)
                        in
                        ((s1, e1), stp)
            in
            let (s, e) = p0 in
            if Z.eqb st0 Big_int_Z.zero_big_int
            then []
            else let lz = Z.of_nat len in
                 let fuel = S (add len len) in
                 let zs =
                   if Z.ltb Big_int_Z.zero_big_int st0
                   then let rec up_by i stop step0 = function
                        | O -> []
                        | S fuel' ->
                          if Z.ltb i stop
                          then i :: (up_by (Z.add i step0) stop step0 fuel')
                          else []
                        in up_by s e st0 fuel
                   else let rec down_by i stop step0 = function
                        | O -> []
                        | S fuel' ->
                          if Z.ltb stop i
                          then i :: (down_by (Z.add i step0) stop step0 fuel')
                          else []
                        in down_by s e st0 fuel
                 in
                 fold_right (fun z acc ->
                   if (&&) (Z.leb Big_int_Z.zero_big_int z) (Z.ltb z lz)
                   then (Z.to_nat z) :: acc
                   else acc) [] zs
          in
          map (fun n0 ->
            mk_node (app p ((JSON.SIndex (Z.of_nat n0)) :: []))
              (match nth_error xs n0 with
               | Some v' -> v'
               | None -> JSON.JNull)) ns
        | _ -> [])
     | JSONPath.SelFilter _ -> [])

  (** val visit_df_value : JSON.path -> JSON.value -> JSON.node list **)

  let rec visit_df_value p v = match v with
  | JSON.JArr xs ->
    let go =
      let rec go i = function
      | [] -> []
      | v' :: ys' ->
        (visit_df_value (app p ((JSON.SIndex (Z.of_nat i)) :: [])) v') :: 
          (go (S i) ys')
      in go
    in
    (mk_node p v) :: (concat (go O xs))
  | JSON.JObject fs ->
    let go =
      let rec go = function
      | [] -> []
      | p0 :: gs' ->
        let (k, v') = p0 in
        (visit_df_value (app p ((JSON.SName k) :: [])) v') :: (go gs')
      in go
    in
    (mk_node p v) :: (concat (go fs))
  | _ -> (mk_node p v) :: []

  (** val visit_df_node : JSON.node -> JSON.node list **)

  let visit_df_node = function
  | (p, v) -> visit_df_value p v

  (** val child_on_node_impl :
      (JSONPath.selector -> JSON.node -> JSON.node list) -> JSONPath.selector
      list -> JSON.node -> JSON.node list **)

  let child_on_node_impl sel_impl sels n =
    concat (map (fun s -> sel_impl s n) sels)

  (** val seg_exec_impl :
      (JSONPath.selector -> JSON.node -> JSON.node list) -> JSONPath.segment
      -> JSON.node -> JSON.node list **)

  let seg_exec_impl sel_impl seg n =
    match seg with
    | JSONPath.Child sels -> concat (map (fun s -> sel_impl s n) sels)
    | JSONPath.Desc sels ->
      let visited = visit_df_node n in
      concat
        (map (fun n0 -> concat (map (fun s -> sel_impl s n0) sels)) visited)

  (** val segs_exec_impl :
      (JSONPath.selector -> JSON.node -> JSON.node list) -> JSONPath.segment
      list -> JSON.node list -> JSON.node list **)

  let rec segs_exec_impl sel_impl segs ns =
    match segs with
    | [] -> ns
    | s :: ss ->
      segs_exec_impl sel_impl ss
        (concat
          (map (fun n ->
            match s with
            | JSONPath.Child sels ->
              concat (map (fun s0 -> sel_impl s0 n) sels)
            | JSONPath.Desc sels ->
              let visited = visit_df_node n in
              concat
                (map (fun n0 -> concat (map (fun s0 -> sel_impl s0 n0) sels))
                  visited)) ns))

  (** val eval_exec_impl :
      (JSONPath.selector -> JSON.node -> JSON.node list) -> JSONPath.query ->
      JSON.value -> JSON.node list **)

  let eval_exec_impl sel_impl q j =
    let rec segs_exec_impl0 segs ns =
      match segs with
      | [] -> ns
      | s :: ss ->
        segs_exec_impl0 ss
          (concat
            (map (fun n ->
              match s with
              | JSONPath.Child sels ->
                concat (map (fun s0 -> sel_impl s0 n) sels)
              | JSONPath.Desc sels ->
                let visited = visit_df_node n in
                concat
                  (map (fun n0 ->
                    concat (map (fun s0 -> sel_impl s0 n0) sels)) visited))
              ns))
    in segs_exec_impl0 (JSONPath.q_segs q) (([], j) :: [])

  (** val child_on_node_nf :
      JSONPath.selector list -> JSON.node -> JSON.node list **)

  let child_on_node_nf sels n =
    concat (map (fun s -> sel_exec_nf s n) sels)

  (** val seg_exec_nf : JSONPath.segment -> JSON.node -> JSON.node list **)

  let seg_exec_nf seg n =
    match seg with
    | JSONPath.Child sels -> concat (map (fun s -> sel_exec_nf s n) sels)
    | JSONPath.Desc sels ->
      let visited = visit_df_node n in
      concat
        (map (fun n0 -> concat (map (fun s -> sel_exec_nf s n0) sels))
          visited)

  (** val segs_exec_nf :
      JSONPath.segment list -> JSON.node list -> JSON.node list **)

  let rec segs_exec_nf segs ns =
    match segs with
    | [] -> ns
    | s :: ss ->
      segs_exec_nf ss
        (concat
          (map (fun n ->
            match s with
            | JSONPath.Child sels ->
              concat (map (fun s0 -> sel_exec_nf s0 n) sels)
            | JSONPath.Desc sels ->
              let visited = visit_df_node n in
              concat
                (map (fun n0 ->
                  concat (map (fun s0 -> sel_exec_nf s0 n0) sels)) visited))
            ns))

  (** val eval_exec_nf : JSONPath.query -> JSON.value -> JSON.node list **)

  let eval_exec_nf =
    eval_exec_impl sel_exec_nf

  (** val sel_exec : JSONPath.selector -> JSON.node -> JSON.node list **)

  let rec sel_exec sel n =
    match sel with
    | JSONPath.SelName s ->
      let (p, v) = n in
      (match v with
       | JSON.JObject fields ->
         (match find (fun kv ->
                  if string_dec (fst kv) s then true else false) fields with
          | Some p0 ->
            let (_, v') = p0 in
            (mk_node (app p ((JSON.SName s) :: [])) v') :: []
          | None -> [])
       | _ -> [])
    | JSONPath.SelWildcard ->
      let (p, v) = n in
      (match v with
       | JSON.JArr xs ->
         map (fun pat ->
           let (i, v') = pat in
           mk_node (app p ((JSON.SIndex (Z.of_nat i)) :: [])) v')
           (index_zip xs)
       | JSON.JObject fields ->
         map (fun pat ->
           let (k, v') = pat in mk_node (app p ((JSON.SName k) :: [])) v')
           fields
       | _ -> [])
    | JSONPath.SelIndex z ->
      let (p, v) = n in
      (match v with
       | JSON.JArr xs ->
         let idx =
           if Z.ltb z Big_int_Z.zero_big_int
           then Z.add (Z.of_nat (Datatypes.length xs)) z
           else z
         in
         if (||) (Z.ltb idx Big_int_Z.zero_big_int)
              (Z.geb idx (Z.of_nat (Datatypes.length xs)))
         then []
         else (match nth_error xs (Z.to_nat idx) with
               | Some v' ->
                 (mk_node (app p ((JSON.SIndex idx) :: [])) v') :: []
               | None -> [])
       | _ -> [])
    | JSONPath.SelSlice (st, en, stp) ->
      let (p, v) = n in
      (match v with
       | JSON.JArr xs ->
         let ns =
           let len = Datatypes.length xs in
           let (p0, st0) =
             let lz = Z.of_nat len in
             if Z.eqb stp Big_int_Z.zero_big_int
             then ((Big_int_Z.zero_big_int, Big_int_Z.zero_big_int),
                    Big_int_Z.zero_big_int)
             else let default_start =
                    if Z.ltb Big_int_Z.zero_big_int stp
                    then Big_int_Z.zero_big_int
                    else Z.sub lz Big_int_Z.unit_big_int
                  in
                  let default_end =
                    if Z.ltb Big_int_Z.zero_big_int stp
                    then lz
                    else Big_int_Z.minus_big_int Big_int_Z.unit_big_int
                  in
                  let s0 =
                    match st with
                    | Some s ->
                      if Z.ltb s Big_int_Z.zero_big_int then Z.add lz s else s
                    | None -> default_start
                  in
                  let e0 =
                    match en with
                    | Some e ->
                      if Z.ltb e Big_int_Z.zero_big_int then Z.add lz e else e
                    | None -> default_end
                  in
                  if Z.ltb Big_int_Z.zero_big_int stp
                  then let s1 = Z.max Big_int_Z.zero_big_int (Z.min lz s0) in
                       let e1 = Z.max Big_int_Z.zero_big_int (Z.min lz e0) in
                       ((s1, e1), stp)
                  else let s1 =
                         Z.max (Big_int_Z.minus_big_int
                           Big_int_Z.unit_big_int)
                           (Z.min (Z.sub lz Big_int_Z.unit_big_int) s0)
                       in
                       let e1 =
                         Z.max (Big_int_Z.minus_big_int
                           Big_int_Z.unit_big_int)
                           (Z.min (Z.sub lz Big_int_Z.unit_big_int) e0)
                       in
                       ((s1, e1), stp)
           in
           let (s, e) = p0 in
           if Z.eqb st0 Big_int_Z.zero_big_int
           then []
           else let lz = Z.of_nat len in
                let fuel = S (add len len) in
                let zs =
                  if Z.ltb Big_int_Z.zero_big_int st0
                  then let rec up_by i stop step0 = function
                       | O -> []
                       | S fuel' ->
                         if Z.ltb i stop
                         then i :: (up_by (Z.add i step0) stop step0 fuel')
                         else []
                       in up_by s e st0 fuel
                  else let rec down_by i stop step0 = function
                       | O -> []
                       | S fuel' ->
                         if Z.ltb stop i
                         then i :: (down_by (Z.add i step0) stop step0 fuel')
                         else []
                       in down_by s e st0 fuel
                in
                fold_right (fun z acc ->
                  if (&&) (Z.leb Big_int_Z.zero_big_int z) (Z.ltb z lz)
                  then (Z.to_nat z) :: acc
                  else acc) [] zs
         in
         map (fun n0 ->
           mk_node (app p ((JSON.SIndex (Z.of_nat n0)) :: []))
             (match nth_error xs n0 with
              | Some v' -> v'
              | None -> JSON.JNull)) ns
       | _ -> [])
    | JSONPath.SelFilter f ->
      let (p, v) = n in
      (match v with
       | JSON.JArr xs ->
         let keep = fun iv ->
           let (i, v') = iv in
           holds_b f ((app p ((JSON.SIndex (Z.of_nat i)) :: [])), v')
         in
         map (fun pat ->
           let (i, v') = pat in
           mk_node (app p ((JSON.SIndex (Z.of_nat i)) :: [])) v')
           (filter keep (index_zip xs))
       | JSON.JObject fields ->
         let keep = fun kv ->
           let (k, v') = kv in holds_b f ((app p ((JSON.SName k) :: [])), v')
         in
         map (fun pat ->
           let (k, v') = pat in mk_node (app p ((JSON.SName k) :: [])) v')
           (filter keep fields)
       | _ -> [])

  (** val holds_b : JSONPath.fexpr -> JSON.node -> bool **)

  and holds_b f n = match n with
  | (_, v) ->
    (match f with
     | JSONPath.FTrue -> true
     | JSONPath.FNot g -> negb (holds_b g n)
     | JSONPath.FAnd (g, h) -> (&&) (holds_b g n) (holds_b h n)
     | JSONPath.FOr (g, h) -> (||) (holds_b g n) (holds_b h n)
     | JSONPath.FExists q ->
       negb
         (PeanoNat.Nat.eqb (Datatypes.length (eval_exec_impl sel_exec q v)) O)
     | JSONPath.FCmp (op, a, b) ->
       (match aeval a v with
        | Some pa ->
          (match aeval b v with
           | Some pb -> cmp_prim op pa pb
           | None -> false)
        | None -> false)
     | JSONPath.FMatch (a, r) ->
       (match aeval a v with
        | Some p ->
          (match p with
           | JSONPath.PStr s -> Regex.regex_match r s
           | _ -> false)
        | None -> false)
     | JSONPath.FSearch (a, r) ->
       (match aeval a v with
        | Some p ->
          (match p with
           | JSONPath.PStr s -> Regex.regex_search r s
           | _ -> false)
        | None -> false))

  (** val aeval : JSONPath.aexpr -> JSON.value -> JSONPath.prim option **)

  and aeval a v =
    match a with
    | JSONPath.APrim p -> Some p
    | JSONPath.ACount q ->
      let ns = eval_exec_impl sel_exec q v in
      Some (JSONPath.PNum (coq_Q_of_nat (Datatypes.length ns)))
    | JSONPath.AValue q ->
      let ns = eval_exec_impl sel_exec q v in
      (match ns with
       | [] -> None
       | n :: l ->
         let (_, v1) = n in
         (match l with
          | [] -> JSONPath.prim_of_value v1
          | _ :: _ -> None))
    | JSONPath.ALengthV q ->
      let ns = eval_exec_impl sel_exec q v in
      (match ns with
       | [] -> None
       | n :: l ->
         let (_, v0) = n in
         (match v0 with
          | JSON.JStr s ->
            (match l with
             | [] -> Some (JSONPath.PNum (coq_Q_of_nat (length s)))
             | _ :: _ -> None)
          | JSON.JArr xs ->
            (match l with
             | [] -> Some (JSONPath.PNum (coq_Q_of_nat (Datatypes.length xs)))
             | _ :: _ -> None)
          | JSON.JObject fs ->
            (match l with
             | [] -> Some (JSONPath.PNum (coq_Q_of_nat (Datatypes.length fs)))
             | _ :: _ -> None)
          | _ -> None))

  (** val child_on_node :
      JSONPath.selector list -> JSON.node -> JSON.node list **)

  let child_on_node sels n =
    concat (map (fun s -> sel_exec s n) sels)

  (** val seg_exec : JSONPath.segment -> JSON.node -> JSON.node list **)

  let seg_exec seg n =
    match seg with
    | JSONPath.Child sels -> concat (map (fun s -> sel_exec s n) sels)
    | JSONPath.Desc sels ->
      let visited = visit_df_node n in
      concat
        (map (fun n0 -> concat (map (fun s -> sel_exec s n0) sels)) visited)

  (** val segs_exec :
      JSONPath.segment list -> JSON.node list -> JSON.node list **)

  let rec segs_exec segs ns =
    match segs with
    | [] -> ns
    | s :: ss ->
      segs_exec ss
        (concat
          (map (fun n ->
            match s with
            | JSONPath.Child sels ->
              concat (map (fun s0 -> sel_exec s0 n) sels)
            | JSONPath.Desc sels ->
              let visited = visit_df_node n in
              concat
                (map (fun n0 -> concat (map (fun s0 -> sel_exec s0 n0) sels))
                  visited)) ns))

  (** val eval_exec : JSONPath.query -> JSON.value -> JSON.node list **)

  let eval_exec =
    eval_exec_impl sel_exec
 end

module Typing =
 struct
  type primty =
  | TNull
  | TBool
  | TNum
  | TStr
  | TAnyPrim

  (** val primty_rect : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> primty -> 'a1 **)

  let primty_rect f f0 f1 f2 f3 = function
  | TNull -> f
  | TBool -> f0
  | TNum -> f1
  | TStr -> f2
  | TAnyPrim -> f3

  (** val primty_rec : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> primty -> 'a1 **)

  let primty_rec f f0 f1 f2 f3 = function
  | TNull -> f
  | TBool -> f0
  | TNum -> f1
  | TStr -> f2
  | TAnyPrim -> f3

  (** val selector_ok : JSONPath.selector -> bool **)

  let selector_ok = function
  | JSONPath.SelName _ -> true
  | JSONPath.SelIndex _ -> true
  | _ -> false

  (** val segment_ok : JSONPath.segment -> bool **)

  let segment_ok = function
  | JSONPath.Child sels -> forallb selector_ok sels
  | JSONPath.Desc _ -> false

  (** val singleton_query : JSONPath.query -> bool **)

  let singleton_query = function
  | JSONPath.Query segs ->
    (match segs with
     | [] -> false
     | _ :: _ -> forallb segment_ok segs)

  (** val aety : JSONPath.aexpr -> primty **)

  let aety = function
  | JSONPath.APrim p ->
    (match p with
     | JSONPath.PNull -> TNull
     | JSONPath.PBool _ -> TBool
     | JSONPath.PNum _ -> TNum
     | JSONPath.PStr _ -> TStr)
  | JSONPath.AValue _ -> TAnyPrim
  | _ -> TNum

  (** val comparable : primty -> primty -> bool **)

  let comparable _ _ =
    true

  (** val wf_fexpr : JSONPath.fexpr -> bool **)

  let rec wf_fexpr = function
  | JSONPath.FNot g -> wf_fexpr g
  | JSONPath.FAnd (g, h) -> (&&) (wf_fexpr g) (wf_fexpr h)
  | JSONPath.FOr (g, h) -> (&&) (wf_fexpr g) (wf_fexpr h)
  | JSONPath.FCmp (_, a, b) -> comparable (aety a) (aety b)
  | JSONPath.FMatch (a, _) ->
    (match aety a with
     | TStr -> true
     | TAnyPrim -> true
     | _ -> false)
  | JSONPath.FSearch (a, _) ->
    (match aety a with
     | TStr -> true
     | TAnyPrim -> true
     | _ -> false)
  | _ -> true
 end

(** val coq_JQ : Big_int_Z.big_int -> JSON.value **)

let coq_JQ z =
  JSON.JNum (coq_Q_of_Z z)

(** val proj_phoenix_a : JSON.value **)

let proj_phoenix_a =
  JSON.JObject ((('n'::('a'::('m'::('e'::[])))), (JSON.JStr
    ('p'::('h'::('o'::('e'::('n'::('i'::('x'::[]))))))))) :: ((('s'::('t'::('a'::('r'::('s'::[]))))),
    (coq_JQ (Big_int_Z.mult_int_big_int 2
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      Big_int_Z.unit_big_int))))))) :: ((('l'::('a'::('b'::('e'::('l'::('s'::[])))))),
    (JSON.JArr ((JSON.JStr ('m'::('l'::[]))) :: ((JSON.JStr
    ('v'::('i'::('s'::('i'::('o'::('n'::[]))))))) :: [])))) :: [])))

(** val proj_drake_a : JSON.value **)

let proj_drake_a =
  JSON.JObject ((('n'::('a'::('m'::('e'::[])))), (JSON.JStr
    ('d'::('r'::('a'::('k'::('e'::[]))))))) :: ((('s'::('t'::('a'::('r'::('s'::[]))))),
    (coq_JQ (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int)))))) :: ((('l'::('a'::('b'::('e'::('l'::('s'::[])))))),
    (JSON.JArr ((JSON.JStr
    ('i'::('n'::('f'::('r'::('a'::[])))))) :: []))) :: [])))

(** val proj_phoenix_c : JSON.value **)

let proj_phoenix_c =
  JSON.JObject ((('n'::('a'::('m'::('e'::[])))), (JSON.JStr
    ('p'::('h'::('o'::('e'::('n'::('i'::('x'::[]))))))))) :: ((('s'::('t'::('a'::('r'::('s'::[]))))),
    (coq_JQ (Big_int_Z.mult_int_big_int 2
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int)))))))) :: ((('l'::('a'::('b'::('e'::('l'::('s'::[])))))),
    (JSON.JArr ((JSON.JStr ('m'::('l'::[]))) :: ((JSON.JStr
    ('n'::('l'::('p'::[])))) :: [])))) :: [])))

(** val proj_eagle_c : JSON.value **)

let proj_eagle_c =
  JSON.JObject ((('n'::('a'::('m'::('e'::[])))), (JSON.JStr
    ('e'::('a'::('g'::('l'::('e'::[]))))))) :: ((('s'::('t'::('a'::('r'::('s'::[]))))),
    (coq_JQ
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      Big_int_Z.unit_big_int))))) :: ((('l'::('a'::('b'::('e'::('l'::('s'::[])))))),
    (JSON.JArr ((JSON.JStr
    ('i'::('n'::('f'::('r'::('a'::[])))))) :: []))) :: [])))

(** val proj_crm_d : JSON.value **)

let proj_crm_d =
  JSON.JObject ((('n'::('a'::('m'::('e'::[])))), (JSON.JStr
    ('c'::('r'::('m'::[]))))) :: ((('s'::('t'::('a'::('r'::('s'::[]))))),
    (coq_JQ (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int))))) :: ((('l'::('a'::('b'::('e'::('l'::('s'::[])))))),
    (JSON.JArr ((JSON.JStr
    ('s'::('a'::('l'::('e'::('s'::[])))))) :: []))) :: [])))

(** val emp_alice : JSON.value **)

let emp_alice =
  JSON.JObject ((('n'::('a'::('m'::('e'::[])))), (JSON.JStr
    ('a'::('l'::('i'::('c'::('e'::[]))))))) :: ((('a'::('g'::('e'::[]))),
    (coq_JQ (Big_int_Z.mult_int_big_int 2
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int))))))) :: ((('e'::('m'::('a'::('i'::('l'::[]))))),
    (JSON.JStr
    ('a'::('l'::('i'::('c'::('e'::('@'::('a'::('c'::('m'::('e'::('.'::('c'::('o'::('m'::[])))))))))))))))) :: ((('t'::('a'::('g'::('s'::[])))),
    (JSON.JArr ((JSON.JStr ('m'::('l'::[]))) :: ((JSON.JStr
    ('b'::('a'::('c'::('k'::('e'::('n'::('d'::[])))))))) :: [])))) :: ((('b'::('i'::('o'::[]))),
    (JSON.JStr
    ('s'::('e'::('n'::('i'::('o'::('r'::(' '::('m'::('l'::(' '::('e'::('n'::('g'::('i'::('n'::('e'::('e'::('r'::[])))))))))))))))))))) :: ((('p'::('r'::('o'::('j'::('e'::('c'::('t'::('s'::[])))))))),
    (JSON.JArr (proj_phoenix_a :: (proj_drake_a :: [])))) :: []))))))

(** val emp_bob : JSON.value **)

let emp_bob =
  JSON.JObject ((('n'::('a'::('m'::('e'::[])))), (JSON.JStr
    ('b'::('o'::('b'::[]))))) :: ((('a'::('g'::('e'::[]))),
    (coq_JQ
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      Big_int_Z.unit_big_int)))))) :: ((('e'::('m'::('a'::('i'::('l'::[]))))),
    (JSON.JStr
    ('b'::('o'::('b'::('@'::('a'::('c'::('m'::('e'::('.'::('o'::('r'::('g'::[])))))))))))))) :: ((('t'::('a'::('g'::('s'::[])))),
    (JSON.JArr ((JSON.JStr
    ('f'::('r'::('o'::('n'::('t'::('e'::('n'::('d'::[]))))))))) :: []))) :: ((('b'::('i'::('o'::[]))),
    (JSON.JStr
    ('u'::('i'::[])))) :: ((('p'::('r'::('o'::('j'::('e'::('c'::('t'::('s'::[])))))))),
    (JSON.JArr [])) :: []))))))

(** val emp_carol : JSON.value **)

let emp_carol =
  JSON.JObject ((('n'::('a'::('m'::('e'::[])))), (JSON.JStr
    ('c'::('a'::('r'::('o'::('l'::[]))))))) :: ((('a'::('g'::('e'::[]))),
    (coq_JQ
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int))))))) :: ((('e'::('m'::('a'::('i'::('l'::[]))))),
    (JSON.JStr
    ('c'::('a'::('r'::('o'::('l'::('@'::('a'::('c'::('m'::('e'::('.'::('c'::('o'::('m'::[])))))))))))))))) :: ((('t'::('a'::('g'::('s'::[])))),
    (JSON.JArr ((JSON.JStr ('m'::('l'::[]))) :: ((JSON.JStr
    ('n'::('l'::('p'::[])))) :: ((JSON.JStr
    ('r'::('e'::('s'::('e'::('a'::('r'::('c'::('h'::[]))))))))) :: []))))) :: ((('b'::('i'::('o'::[]))),
    (JSON.JStr
    ('n'::('l'::('p'::(' '::('s'::('p'::('e'::('c'::('i'::('a'::('l'::('i'::('s'::('t'::[])))))))))))))))) :: ((('p'::('r'::('o'::('j'::('e'::('c'::('t'::('s'::[])))))))),
    (JSON.JArr (proj_phoenix_c :: (proj_eagle_c :: [])))) :: []))))))

(** val emp_dave : JSON.value **)

let emp_dave =
  JSON.JObject ((('n'::('a'::('m'::('e'::[])))), (JSON.JStr
    ('d'::('a'::('v'::('e'::[])))))) :: ((('a'::('g'::('e'::[]))),
    (coq_JQ
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      Big_int_Z.unit_big_int))))))) :: ((('e'::('m'::('a'::('i'::('l'::[]))))),
    (JSON.JStr
    ('d'::('a'::('v'::('e'::('@'::('a'::('c'::('m'::('e'::('.'::('c'::('o'::('m'::[]))))))))))))))) :: ((('t'::('a'::('g'::('s'::[])))),
    (JSON.JArr ((JSON.JStr
    ('s'::('a'::('l'::('e'::('s'::[])))))) :: ((JSON.JStr
    ('l'::('e'::('a'::('d'::[]))))) :: [])))) :: ((('b'::('i'::('o'::[]))),
    (JSON.JStr
    ('a'::('c'::('c'::('o'::('u'::('n'::('t'::(' '::('e'::('x'::('e'::('c'::[])))))))))))))) :: ((('p'::('r'::('o'::('j'::('e'::('c'::('t'::('s'::[])))))))),
    (JSON.JArr (proj_crm_d :: []))) :: []))))))

(** val emp_erin : JSON.value **)

let emp_erin =
  JSON.JObject ((('n'::('a'::('m'::('e'::[])))), (JSON.JStr
    ('e'::('r'::('i'::('n'::[])))))) :: ((('a'::('g'::('e'::[]))),
    (coq_JQ (Big_int_Z.mult_int_big_int 2
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int)))))) :: ((('e'::('m'::('a'::('i'::('l'::[]))))),
    (JSON.JStr
    ('e'::('r'::('i'::('n'::('@'::('a'::('c'::('m'::('e'::('.'::('c'::('o'::('m'::[]))))))))))))))) :: ((('t'::('a'::('g'::('s'::[])))),
    (JSON.JArr ((JSON.JStr
    ('i'::('n'::('t'::('e'::('r'::('n'::[]))))))) :: []))) :: ((('b'::('i'::('o'::[]))),
    (JSON.JStr
    ('s'::('u'::('m'::('m'::('e'::('r'::(' '::('i'::('n'::('t'::('e'::('r'::('n'::[]))))))))))))))) :: ((('p'::('r'::('o'::('j'::('e'::('c'::('t'::('s'::[])))))))),
    (JSON.JArr [])) :: []))))))

(** val dept_research : JSON.value **)

let dept_research =
  JSON.JObject ((('n'::('a'::('m'::('e'::[])))), (JSON.JStr
    ('R'::('e'::('s'::('e'::('a'::('r'::('c'::('h'::[])))))))))) :: ((('e'::('m'::('p'::('l'::('o'::('y'::('e'::('e'::('s'::[]))))))))),
    (JSON.JArr (emp_alice :: (emp_bob :: (emp_carol :: []))))) :: []))

(** val dept_sales : JSON.value **)

let dept_sales =
  JSON.JObject ((('n'::('a'::('m'::('e'::[])))), (JSON.JStr
    ('S'::('a'::('l'::('e'::('s'::[]))))))) :: ((('e'::('m'::('p'::('l'::('o'::('y'::('e'::('e'::('s'::[]))))))))),
    (JSON.JArr (emp_dave :: (emp_erin :: [])))) :: []))

(** val company_json : JSON.value **)

let company_json =
  JSON.JObject ((('c'::('o'::('m'::('p'::('a'::('n'::('y'::[]))))))),
    (JSON.JStr
    ('A'::('c'::('m'::('e'::[])))))) :: ((('d'::('e'::('p'::('a'::('r'::('t'::('m'::('e'::('n'::('t'::('s'::[]))))))))))),
    (JSON.JArr
    (dept_research :: (dept_sales :: [])))) :: ((('m'::('e'::('t'::('a'::[])))),
    (JSON.JObject ((('v'::('e'::('r'::('s'::('i'::('o'::('n'::[]))))))),
    (JSON.JStr ('1'::('.'::('0'::[]))))) :: ((('r'::('e'::('v'::[]))),
    (coq_JQ
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      Big_int_Z.unit_big_int)))) :: [])))) :: [])))

(** val acme_db_json : JSON.value **)

let acme_db_json =
  JSON.JObject ((('c'::('o'::('m'::('p'::('a'::('n'::('y'::[]))))))),
    (JSON.JStr
    ('A'::('c'::('m'::('e'::(' '::('I'::('n'::('c'::('.'::[]))))))))))) :: ((('h'::('q'::[])),
    (JSON.JObject
    ((('a'::('d'::('d'::('r'::('e'::('s'::('s'::('1'::[])))))))), (JSON.JStr
    ('5'::('0'::('0'::(' '::('M'::('a'::('r'::('k'::('e'::('t'::(' '::('S'::('t'::[]))))))))))))))) :: ((('c'::('i'::('t'::('y'::[])))),
    (JSON.JStr
    ('S'::('a'::('n'::(' '::('F'::('r'::('a'::('n'::('c'::('i'::('s'::('c'::('o'::[]))))))))))))))) :: ((('s'::('t'::('a'::('t'::('e'::[]))))),
    (JSON.JStr
    ('C'::('A'::[])))) :: ((('p'::('o'::('s'::('t'::('a'::('l'::('_'::('c'::('o'::('d'::('e'::[]))))))))))),
    (JSON.JStr
    ('9'::('4'::('1'::('0'::('5'::[]))))))) :: ((('c'::('o'::('u'::('n'::('t'::('r'::('y'::[]))))))),
    (JSON.JStr
    ('U'::('S'::[])))) :: []))))))) :: ((('c'::('o'::('n'::('t'::('a'::('c'::('t'::('s'::[])))))))),
    (JSON.JObject ((('s'::('u'::('p'::('p'::('o'::('r'::('t'::[]))))))),
    (JSON.JStr
    ('s'::('u'::('p'::('p'::('o'::('r'::('t'::('@'::('a'::('c'::('m'::('e'::('.'::('c'::('o'::('m'::[])))))))))))))))))) :: ((('s'::('a'::('l'::('e'::('s'::[]))))),
    (JSON.JStr
    ('s'::('a'::('l'::('e'::('s'::('@'::('a'::('c'::('m'::('e'::('.'::('c'::('o'::('m'::[])))))))))))))))) :: ((('s'::('t'::('a'::('t'::('u'::('s'::[])))))),
    (JSON.JStr
    ('g'::('r'::('e'::('e'::('n'::[]))))))) :: ((('p'::('h'::('o'::('n'::('e'::[]))))),
    (JSON.JStr
    ('+'::('1'::('-'::('4'::('1'::('5'::('-'::('5'::('5'::('5'::('-'::('0'::('0'::('0'::('0'::[]))))))))))))))))) :: [])))))) :: ((('o'::('f'::('f'::('i'::('c'::('e'::('s'::[]))))))),
    (JSON.JArr ((JSON.JObject ((('c'::('o'::('d'::('e'::[])))), (JSON.JStr
    ('S'::('F'::('O'::[]))))) :: ((('t'::('i'::('m'::('e'::('z'::('o'::('n'::('e'::[])))))))),
    (JSON.JStr
    ('A'::('m'::('e'::('r'::('i'::('c'::('a'::('/'::('L'::('o'::('s'::('_'::('A'::('n'::('g'::('e'::('l'::('e'::('s'::[]))))))))))))))))))))) :: ((('l'::('e'::('a'::('d'::[])))),
    (JSON.JStr
    ('c'::('a'::('r'::('o'::('l'::[]))))))) :: [])))) :: ((JSON.JObject
    ((('c'::('o'::('d'::('e'::[])))), (JSON.JStr
    ('N'::('Y'::('C'::[]))))) :: ((('t'::('i'::('m'::('e'::('z'::('o'::('n'::('e'::[])))))))),
    (JSON.JStr
    ('A'::('m'::('e'::('r'::('i'::('c'::('a'::('/'::('N'::('e'::('w'::('_'::('Y'::('o'::('r'::('k'::[])))))))))))))))))) :: ((('l'::('e'::('a'::('d'::[])))),
    (JSON.JStr ('d'::('a'::('v'::('e'::[])))))) :: [])))) :: ((JSON.JObject
    ((('c'::('o'::('d'::('e'::[])))), (JSON.JStr
    ('B'::('E'::('R'::[]))))) :: ((('t'::('i'::('m'::('e'::('z'::('o'::('n'::('e'::[])))))))),
    (JSON.JStr
    ('E'::('u'::('r'::('o'::('p'::('e'::('/'::('B'::('e'::('r'::('l'::('i'::('n'::[]))))))))))))))) :: ((('l'::('e'::('a'::('d'::[])))),
    (JSON.JStr
    ('h'::('e'::('i'::('d'::('i'::[]))))))) :: [])))) :: []))))) :: ((('d'::('e'::('p'::('a'::('r'::('t'::('m'::('e'::('n'::('t'::('s'::[]))))))))))),
    (JSON.JArr ((JSON.JObject ((('i'::('d'::[])), (JSON.JStr
    ('R'::('&'::('D'::[]))))) :: ((('n'::('a'::('m'::('e'::[])))), (JSON.JStr
    ('R'::('e'::('s'::('e'::('a'::('r'::('c'::('h'::[])))))))))) :: ((('c'::('o'::('s'::('t'::('_'::('c'::('e'::('n'::('t'::('e'::('r'::[]))))))))))),
    (JSON.JStr
    ('1'::('0'::('0'::('1'::[])))))) :: ((('b'::('u'::('d'::('g'::('e'::('t'::('_'::('u'::('s'::('d'::[])))))))))),
    (coq_JQ (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      (Big_int_Z.mult_int_big_int 2
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2
      Big_int_Z.unit_big_int))))))))))))))))))))))))) :: ((('e'::('m'::('p'::('l'::('o'::('y'::('e'::('e'::('s'::[]))))))))),
    (JSON.JArr ((JSON.JObject ((('i'::('d'::[])), (JSON.JStr
    ('u'::('-'::('a'::('l'::('i'::('c'::('e'::[]))))))))) :: ((('n'::('a'::('m'::('e'::[])))),
    (JSON.JStr
    ('a'::('l'::('i'::('c'::('e'::[]))))))) :: ((('a'::('g'::('e'::[]))),
    (coq_JQ (Big_int_Z.mult_int_big_int 2
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int))))))) :: ((('e'::('m'::('a'::('i'::('l'::[]))))),
    (JSON.JStr
    ('a'::('l'::('i'::('c'::('e'::('@'::('a'::('c'::('m'::('e'::('.'::('c'::('o'::('m'::[])))))))))))))))) :: ((('p'::('h'::('o'::('n'::('e'::[]))))),
    (JSON.JStr
    ('+'::('1'::('-'::('4'::('1'::('5'::('-'::('5'::('5'::('5'::('-'::('1'::('0'::('1'::('0'::[]))))))))))))))))) :: ((('h'::('i'::('r'::('e'::('_'::('d'::('a'::('t'::('e'::[]))))))))),
    (JSON.JStr
    ('2'::('0'::('1'::('8'::('-'::('0'::('3'::('-'::('1'::('2'::[])))))))))))) :: ((('t'::('a'::('g'::('s'::[])))),
    (JSON.JArr ((JSON.JStr ('m'::('l'::[]))) :: ((JSON.JStr
    ('b'::('a'::('c'::('k'::('e'::('n'::('d'::[])))))))) :: [])))) :: ((('b'::('i'::('o'::[]))),
    (JSON.JStr
    ('s'::('e'::('n'::('i'::('o'::('r'::(' '::('m'::('l'::(' '::('e'::('n'::('g'::('i'::('n'::('e'::('e'::('r'::[])))))))))))))))))))) :: ((('p'::('r'::('o'::('j'::('e'::('c'::('t'::('s'::[])))))))),
    (JSON.JArr ((JSON.JObject ((('i'::('d'::[])), (JSON.JStr
    ('p'::('h'::('o'::('e'::('n'::('i'::('x'::('-'::('a'::[]))))))))))) :: ((('n'::('a'::('m'::('e'::[])))),
    (JSON.JStr
    ('p'::('h'::('o'::('e'::('n'::('i'::('x'::[]))))))))) :: ((('s'::('t'::('a'::('r'::('s'::[]))))),
    (coq_JQ (Big_int_Z.mult_int_big_int 2
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      Big_int_Z.unit_big_int))))))) :: ((('l'::('a'::('b'::('e'::('l'::('s'::[])))))),
    (JSON.JArr ((JSON.JStr ('m'::('l'::[]))) :: ((JSON.JStr
    ('v'::('i'::('s'::('i'::('o'::('n'::[]))))))) :: [])))) :: ((('s'::('t'::('a'::('t'::('u'::('s'::[])))))),
    (JSON.JStr
    ('a'::('c'::('t'::('i'::('v'::('e'::[])))))))) :: ((('r'::('e'::('p'::('o'::[])))),
    (JSON.JStr
    ('g'::('i'::('t'::('@'::('g'::('i'::('t'::('h'::('u'::('b'::('.'::('c'::('o'::('m'::(':'::('a'::('c'::('m'::('e'::('/'::('p'::('h'::('o'::('e'::('n'::('i'::('x'::[]))))))))))))))))))))))))))))) :: ((('s'::('t'::('a'::('r'::('t'::('e'::('d'::[]))))))),
    (JSON.JStr
    ('2'::('0'::('1'::('9'::('-'::('0'::('9'::('-'::('0'::('1'::[])))))))))))) :: ((('m'::('e'::('t'::('r'::('i'::('c'::('s'::[]))))))),
    (JSON.JObject
    ((('p'::('r'::('s'::('_'::('o'::('p'::('e'::('n'::[])))))))),
    (coq_JQ
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      Big_int_Z.unit_big_int)))) :: ((('i'::('s'::('s'::('u'::('e'::('s'::('_'::('o'::('p'::('e'::('n'::[]))))))))))),
    (coq_JQ (Big_int_Z.mult_int_big_int 2
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int))))))) :: ((('c'::('o'::('v'::('e'::('r'::('a'::('g'::('e'::('_'::('p'::('c'::('t'::[])))))))))))),
    (coq_JQ
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int)))))))) :: []))))) :: []))))))))) :: ((JSON.JObject
    ((('i'::('d'::[])), (JSON.JStr
    ('d'::('r'::('a'::('k'::('e'::('-'::('a'::[]))))))))) :: ((('n'::('a'::('m'::('e'::[])))),
    (JSON.JStr
    ('d'::('r'::('a'::('k'::('e'::[]))))))) :: ((('s'::('t'::('a'::('r'::('s'::[]))))),
    (coq_JQ (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int)))))) :: ((('l'::('a'::('b'::('e'::('l'::('s'::[])))))),
    (JSON.JArr ((JSON.JStr
    ('i'::('n'::('f'::('r'::('a'::[])))))) :: []))) :: ((('s'::('t'::('a'::('t'::('u'::('s'::[])))))),
    (JSON.JStr
    ('a'::('r'::('c'::('h'::('i'::('v'::('e'::('d'::[])))))))))) :: ((('r'::('e'::('p'::('o'::[])))),
    (JSON.JStr
    ('g'::('i'::('t'::('@'::('g'::('i'::('t'::('h'::('u'::('b'::('.'::('c'::('o'::('m'::(':'::('a'::('c'::('m'::('e'::('/'::('d'::('r'::('a'::('k'::('e'::[]))))))))))))))))))))))))))) :: ((('s'::('t'::('a'::('r'::('t'::('e'::('d'::[]))))))),
    (JSON.JStr
    ('2'::('0'::('1'::('7'::('-'::('0'::('5'::('-'::('2'::('2'::[])))))))))))) :: ((('m'::('e'::('t'::('r'::('i'::('c'::('s'::[]))))))),
    (JSON.JObject
    ((('p'::('r'::('s'::('_'::('o'::('p'::('e'::('n'::[])))))))),
    (coq_JQ Big_int_Z.zero_big_int)) :: ((('i'::('s'::('s'::('u'::('e'::('s'::('_'::('o'::('p'::('e'::('n'::[]))))))))))),
    (coq_JQ
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      Big_int_Z.unit_big_int))) :: ((('c'::('o'::('v'::('e'::('r'::('a'::('g'::('e'::('_'::('p'::('c'::('t'::[])))))))))))),
    (coq_JQ (Big_int_Z.mult_int_big_int 2
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      Big_int_Z.unit_big_int)))))))) :: []))))) :: []))))))))) :: [])))) :: [])))))))))) :: ((JSON.JObject
    ((('i'::('d'::[])), (JSON.JStr
    ('u'::('-'::('b'::('o'::('b'::[]))))))) :: ((('n'::('a'::('m'::('e'::[])))),
    (JSON.JStr ('b'::('o'::('b'::[]))))) :: ((('a'::('g'::('e'::[]))),
    (coq_JQ
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      Big_int_Z.unit_big_int)))))) :: ((('e'::('m'::('a'::('i'::('l'::[]))))),
    (JSON.JStr
    ('b'::('o'::('b'::('@'::('a'::('c'::('m'::('e'::('.'::('o'::('r'::('g'::[])))))))))))))) :: ((('p'::('h'::('o'::('n'::('e'::[]))))),
    (JSON.JStr
    ('+'::('1'::('-'::('4'::('1'::('5'::('-'::('5'::('5'::('5'::('-'::('1'::('0'::('1'::('1'::[]))))))))))))))))) :: ((('h'::('i'::('r'::('e'::('_'::('d'::('a'::('t'::('e'::[]))))))))),
    (JSON.JStr
    ('2'::('0'::('2'::('0'::('-'::('0'::('7'::('-'::('0'::('1'::[])))))))))))) :: ((('t'::('a'::('g'::('s'::[])))),
    (JSON.JArr ((JSON.JStr
    ('f'::('r'::('o'::('n'::('t'::('e'::('n'::('d'::[]))))))))) :: []))) :: ((('b'::('i'::('o'::[]))),
    (JSON.JStr
    ('u'::('i'::[])))) :: ((('p'::('r'::('o'::('j'::('e'::('c'::('t'::('s'::[])))))))),
    (JSON.JArr [])) :: [])))))))))) :: ((JSON.JObject ((('i'::('d'::[])),
    (JSON.JStr
    ('u'::('-'::('c'::('a'::('r'::('o'::('l'::[]))))))))) :: ((('n'::('a'::('m'::('e'::[])))),
    (JSON.JStr
    ('c'::('a'::('r'::('o'::('l'::[]))))))) :: ((('a'::('g'::('e'::[]))),
    (coq_JQ
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int))))))) :: ((('e'::('m'::('a'::('i'::('l'::[]))))),
    (JSON.JStr
    ('c'::('a'::('r'::('o'::('l'::('@'::('a'::('c'::('m'::('e'::('.'::('c'::('o'::('m'::[])))))))))))))))) :: ((('p'::('h'::('o'::('n'::('e'::[]))))),
    (JSON.JStr
    ('+'::('1'::('-'::('4'::('1'::('5'::('-'::('5'::('5'::('5'::('-'::('1'::('0'::('1'::('2'::[]))))))))))))))))) :: ((('h'::('i'::('r'::('e'::('_'::('d'::('a'::('t'::('e'::[]))))))))),
    (JSON.JStr
    ('2'::('0'::('1'::('3'::('-'::('1'::('1'::('-'::('0'::('5'::[])))))))))))) :: ((('t'::('a'::('g'::('s'::[])))),
    (JSON.JArr ((JSON.JStr ('m'::('l'::[]))) :: ((JSON.JStr
    ('n'::('l'::('p'::[])))) :: ((JSON.JStr
    ('r'::('e'::('s'::('e'::('a'::('r'::('c'::('h'::[]))))))))) :: []))))) :: ((('b'::('i'::('o'::[]))),
    (JSON.JStr
    ('n'::('l'::('p'::(' '::('s'::('p'::('e'::('c'::('i'::('a'::('l'::('i'::('s'::('t'::[])))))))))))))))) :: ((('p'::('r'::('o'::('j'::('e'::('c'::('t'::('s'::[])))))))),
    (JSON.JArr ((JSON.JObject ((('i'::('d'::[])), (JSON.JStr
    ('p'::('h'::('o'::('e'::('n'::('i'::('x'::('-'::('c'::[]))))))))))) :: ((('n'::('a'::('m'::('e'::[])))),
    (JSON.JStr
    ('p'::('h'::('o'::('e'::('n'::('i'::('x'::[]))))))))) :: ((('s'::('t'::('a'::('r'::('s'::[]))))),
    (coq_JQ (Big_int_Z.mult_int_big_int 2
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int)))))))) :: ((('l'::('a'::('b'::('e'::('l'::('s'::[])))))),
    (JSON.JArr ((JSON.JStr ('m'::('l'::[]))) :: ((JSON.JStr
    ('n'::('l'::('p'::[])))) :: [])))) :: ((('s'::('t'::('a'::('t'::('u'::('s'::[])))))),
    (JSON.JStr
    ('a'::('c'::('t'::('i'::('v'::('e'::[])))))))) :: ((('r'::('e'::('p'::('o'::[])))),
    (JSON.JStr
    ('g'::('i'::('t'::('@'::('g'::('i'::('t'::('h'::('u'::('b'::('.'::('c'::('o'::('m'::(':'::('a'::('c'::('m'::('e'::('/'::('p'::('h'::('o'::('e'::('n'::('i'::('x'::[]))))))))))))))))))))))))))))) :: ((('s'::('t'::('a'::('r'::('t'::('e'::('d'::[]))))))),
    (JSON.JStr
    ('2'::('0'::('2'::('1'::('-'::('0'::('2'::('-'::('1'::('0'::[])))))))))))) :: ((('m'::('e'::('t'::('r'::('i'::('c'::('s'::[]))))))),
    (JSON.JObject
    ((('p'::('r'::('s'::('_'::('o'::('p'::('e'::('n'::[])))))))),
    (coq_JQ (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      Big_int_Z.unit_big_int))))) :: ((('i'::('s'::('s'::('u'::('e'::('s'::('_'::('o'::('p'::('e'::('n'::[]))))))))))),
    (coq_JQ
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      Big_int_Z.unit_big_int))))) :: ((('c'::('o'::('v'::('e'::('r'::('a'::('g'::('e'::('_'::('p'::('c'::('t'::[])))))))))))),
    (coq_JQ (Big_int_Z.mult_int_big_int 2
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int)))))))) :: []))))) :: []))))))))) :: ((JSON.JObject
    ((('i'::('d'::[])), (JSON.JStr
    ('e'::('a'::('g'::('l'::('e'::('-'::('c'::[]))))))))) :: ((('n'::('a'::('m'::('e'::[])))),
    (JSON.JStr
    ('e'::('a'::('g'::('l'::('e'::[]))))))) :: ((('s'::('t'::('a'::('r'::('s'::[]))))),
    (coq_JQ
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      Big_int_Z.unit_big_int))))) :: ((('l'::('a'::('b'::('e'::('l'::('s'::[])))))),
    (JSON.JArr ((JSON.JStr
    ('i'::('n'::('f'::('r'::('a'::[])))))) :: []))) :: ((('s'::('t'::('a'::('t'::('u'::('s'::[])))))),
    (JSON.JStr
    ('a'::('c'::('t'::('i'::('v'::('e'::[])))))))) :: ((('r'::('e'::('p'::('o'::[])))),
    (JSON.JStr
    ('g'::('i'::('t'::('@'::('g'::('i'::('t'::('h'::('u'::('b'::('.'::('c'::('o'::('m'::(':'::('a'::('c'::('m'::('e'::('/'::('e'::('a'::('g'::('l'::('e'::[]))))))))))))))))))))))))))) :: ((('s'::('t'::('a'::('r'::('t'::('e'::('d'::[]))))))),
    (JSON.JStr
    ('2'::('0'::('2'::('0'::('-'::('1'::('0'::('-'::('1'::('8'::[])))))))))))) :: ((('m'::('e'::('t'::('r'::('i'::('c'::('s'::[]))))))),
    (JSON.JObject
    ((('p'::('r'::('s'::('_'::('o'::('p'::('e'::('n'::[])))))))),
    (coq_JQ
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      Big_int_Z.unit_big_int))) :: ((('i'::('s'::('s'::('u'::('e'::('s'::('_'::('o'::('p'::('e'::('n'::[]))))))))))),
    (coq_JQ
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int)))) :: ((('c'::('o'::('v'::('e'::('r'::('a'::('g'::('e'::('_'::('p'::('c'::('t'::[])))))))))))),
    (coq_JQ
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      (Big_int_Z.mult_int_big_int 2
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int)))))))) :: []))))) :: []))))))))) :: [])))) :: [])))))))))) :: []))))) :: [])))))) :: ((JSON.JObject
    ((('i'::('d'::[])), (JSON.JStr
    ('E'::('N'::('G'::[]))))) :: ((('n'::('a'::('m'::('e'::[])))), (JSON.JStr
    ('E'::('n'::('g'::('i'::('n'::('e'::('e'::('r'::('i'::('n'::('g'::[]))))))))))))) :: ((('c'::('o'::('s'::('t'::('_'::('c'::('e'::('n'::('t'::('e'::('r'::[]))))))))))),
    (JSON.JStr
    ('1'::('0'::('0'::('2'::[])))))) :: ((('b'::('u'::('d'::('g'::('e'::('t'::('_'::('u'::('s'::('d'::[])))))))))),
    (coq_JQ (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      (Big_int_Z.mult_int_big_int 2
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      Big_int_Z.unit_big_int)))))))))))))))))))))))))) :: ((('e'::('m'::('p'::('l'::('o'::('y'::('e'::('e'::('s'::[]))))))))),
    (JSON.JArr ((JSON.JObject ((('i'::('d'::[])), (JSON.JStr
    ('u'::('-'::('t'::('r'::('e'::('n'::('t'::[]))))))))) :: ((('n'::('a'::('m'::('e'::[])))),
    (JSON.JStr
    ('t'::('r'::('e'::('n'::('t'::[]))))))) :: ((('a'::('g'::('e'::[]))),
    (coq_JQ
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      Big_int_Z.unit_big_int))))))) :: ((('e'::('m'::('a'::('i'::('l'::[]))))),
    (JSON.JStr
    ('t'::('r'::('e'::('n'::('t'::('@'::('a'::('c'::('m'::('e'::('.'::('c'::('o'::('m'::[])))))))))))))))) :: ((('p'::('h'::('o'::('n'::('e'::[]))))),
    (JSON.JStr
    ('+'::('1'::('-'::('2'::('1'::('2'::('-'::('5'::('5'::('5'::('-'::('2'::('0'::('0'::('1'::[]))))))))))))))))) :: ((('h'::('i'::('r'::('e'::('_'::('d'::('a'::('t'::('e'::[]))))))))),
    (JSON.JStr
    ('2'::('0'::('1'::('6'::('-'::('0'::('4'::('-'::('0'::('9'::[])))))))))))) :: ((('t'::('a'::('g'::('s'::[])))),
    (JSON.JArr ((JSON.JStr
    ('p'::('l'::('a'::('t'::('f'::('o'::('r'::('m'::[]))))))))) :: ((JSON.JStr
    ('s'::('r'::('e'::[])))) :: [])))) :: ((('b'::('i'::('o'::[]))),
    (JSON.JStr
    ('p'::('l'::('a'::('t'::('f'::('o'::('r'::('m'::(' '::('l'::('e'::('a'::('d'::[]))))))))))))))) :: ((('p'::('r'::('o'::('j'::('e'::('c'::('t'::('s'::[])))))))),
    (JSON.JArr ((JSON.JObject ((('i'::('d'::[])), (JSON.JStr
    ('t'::('i'::('t'::('a'::('n'::[]))))))) :: ((('n'::('a'::('m'::('e'::[])))),
    (JSON.JStr
    ('t'::('i'::('t'::('a'::('n'::[]))))))) :: ((('s'::('t'::('a'::('r'::('s'::[]))))),
    (coq_JQ
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      Big_int_Z.unit_big_int))))))) :: ((('l'::('a'::('b'::('e'::('l'::('s'::[])))))),
    (JSON.JArr ((JSON.JStr
    ('p'::('l'::('a'::('t'::('f'::('o'::('r'::('m'::[]))))))))) :: ((JSON.JStr
    ('k'::('8'::('s'::[])))) :: [])))) :: ((('s'::('t'::('a'::('t'::('u'::('s'::[])))))),
    (JSON.JStr
    ('a'::('c'::('t'::('i'::('v'::('e'::[])))))))) :: ((('r'::('e'::('p'::('o'::[])))),
    (JSON.JStr
    ('g'::('i'::('t'::('@'::('g'::('i'::('t'::('h'::('u'::('b'::('.'::('c'::('o'::('m'::(':'::('a'::('c'::('m'::('e'::('/'::('t'::('i'::('t'::('a'::('n'::[]))))))))))))))))))))))))))) :: ((('s'::('t'::('a'::('r'::('t'::('e'::('d'::[]))))))),
    (JSON.JStr
    ('2'::('0'::('1'::('9'::('-'::('0'::('1'::('-'::('1'::('5'::[])))))))))))) :: ((('m'::('e'::('t'::('r'::('i'::('c'::('s'::[]))))))),
    (JSON.JObject
    ((('p'::('r'::('s'::('_'::('o'::('p'::('e'::('n'::[])))))))),
    (coq_JQ
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      Big_int_Z.unit_big_int))))) :: ((('i'::('s'::('s'::('u'::('e'::('s'::('_'::('o'::('p'::('e'::('n'::[]))))))))))),
    (coq_JQ
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int)))))) :: ((('c'::('o'::('v'::('e'::('r'::('a'::('g'::('e'::('_'::('p'::('c'::('t'::[])))))))))))),
    (coq_JQ (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int)))))))) :: []))))) :: []))))))))) :: []))) :: [])))))))))) :: ((JSON.JObject
    ((('i'::('d'::[])), (JSON.JStr
    ('u'::('-'::('g'::('r'::('a'::('c'::('e'::[]))))))))) :: ((('n'::('a'::('m'::('e'::[])))),
    (JSON.JStr
    ('g'::('r'::('a'::('c'::('e'::[]))))))) :: ((('a'::('g'::('e'::[]))),
    (coq_JQ
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      Big_int_Z.unit_big_int)))))) :: ((('e'::('m'::('a'::('i'::('l'::[]))))),
    (JSON.JStr
    ('g'::('r'::('a'::('c'::('e'::('@'::('a'::('c'::('m'::('e'::('.'::('c'::('o'::('m'::[])))))))))))))))) :: ((('p'::('h'::('o'::('n'::('e'::[]))))),
    (JSON.JStr
    ('+'::('1'::('-'::('2'::('1'::('2'::('-'::('5'::('5'::('5'::('-'::('2'::('0'::('0'::('2'::[]))))))))))))))))) :: ((('h'::('i'::('r'::('e'::('_'::('d'::('a'::('t'::('e'::[]))))))))),
    (JSON.JStr
    ('2'::('0'::('1'::('9'::('-'::('0'::('8'::('-'::('2'::('3'::[])))))))))))) :: ((('t'::('a'::('g'::('s'::[])))),
    (JSON.JArr ((JSON.JStr
    ('b'::('a'::('c'::('k'::('e'::('n'::('d'::[])))))))) :: ((JSON.JStr
    ('a'::('p'::('i'::[])))) :: [])))) :: ((('b'::('i'::('o'::[]))),
    (JSON.JStr
    ('s'::('e'::('n'::('i'::('o'::('r'::(' '::('b'::('a'::('c'::('k'::('e'::('n'::('d'::(' '::('e'::('n'::('g'::('i'::('n'::('e'::('e'::('r'::[]))))))))))))))))))))))))) :: ((('p'::('r'::('o'::('j'::('e'::('c'::('t'::('s'::[])))))))),
    (JSON.JArr ((JSON.JObject ((('i'::('d'::[])), (JSON.JStr
    ('a'::('t'::('l'::('a'::('s'::[]))))))) :: ((('n'::('a'::('m'::('e'::[])))),
    (JSON.JStr
    ('a'::('t'::('l'::('a'::('s'::[]))))))) :: ((('s'::('t'::('a'::('r'::('s'::[]))))),
    (coq_JQ (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      Big_int_Z.unit_big_int)))))) :: ((('l'::('a'::('b'::('e'::('l'::('s'::[])))))),
    (JSON.JArr ((JSON.JStr
    ('a'::('p'::('i'::[])))) :: []))) :: ((('s'::('t'::('a'::('t'::('u'::('s'::[])))))),
    (JSON.JStr
    ('a'::('c'::('t'::('i'::('v'::('e'::[])))))))) :: ((('r'::('e'::('p'::('o'::[])))),
    (JSON.JStr
    ('g'::('i'::('t'::('@'::('g'::('i'::('t'::('h'::('u'::('b'::('.'::('c'::('o'::('m'::(':'::('a'::('c'::('m'::('e'::('/'::('a'::('t'::('l'::('a'::('s'::[]))))))))))))))))))))))))))) :: ((('s'::('t'::('a'::('r'::('t'::('e'::('d'::[]))))))),
    (JSON.JStr
    ('2'::('0'::('2'::('2'::('-'::('0'::('4'::('-'::('0'::('1'::[])))))))))))) :: ((('m'::('e'::('t'::('r'::('i'::('c'::('s'::[]))))))),
    (JSON.JObject
    ((('p'::('r'::('s'::('_'::('o'::('p'::('e'::('n'::[])))))))),
    (coq_JQ
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int)))) :: ((('i'::('s'::('s'::('u'::('e'::('s'::('_'::('o'::('p'::('e'::('n'::[]))))))))))),
    (coq_JQ (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int))))) :: ((('c'::('o'::('v'::('e'::('r'::('a'::('g'::('e'::('_'::('p'::('c'::('t'::[])))))))))))),
    (coq_JQ (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      (Big_int_Z.mult_int_big_int 2
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int)))))))) :: []))))) :: []))))))))) :: []))) :: [])))))))))) :: ((JSON.JObject
    ((('i'::('d'::[])), (JSON.JStr
    ('u'::('-'::('h'::('e'::('i'::('d'::('i'::[]))))))))) :: ((('n'::('a'::('m'::('e'::[])))),
    (JSON.JStr
    ('h'::('e'::('i'::('d'::('i'::[]))))))) :: ((('a'::('g'::('e'::[]))),
    (coq_JQ
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      Big_int_Z.unit_big_int)))))) :: ((('e'::('m'::('a'::('i'::('l'::[]))))),
    (JSON.JStr
    ('h'::('e'::('i'::('d'::('i'::('@'::('a'::('c'::('m'::('e'::('.'::('c'::('o'::('m'::[])))))))))))))))) :: ((('p'::('h'::('o'::('n'::('e'::[]))))),
    (JSON.JStr
    ('+'::('4'::('9'::('-'::('3'::('0'::('-'::('5'::('5'::('5'::('-'::('3'::('0'::('0'::('3'::[]))))))))))))))))) :: ((('h'::('i'::('r'::('e'::('_'::('d'::('a'::('t'::('e'::[]))))))))),
    (JSON.JStr
    ('2'::('0'::('2'::('3'::('-'::('0'::('3'::('-'::('0'::('1'::[])))))))))))) :: ((('t'::('a'::('g'::('s'::[])))),
    (JSON.JArr ((JSON.JStr
    ('f'::('r'::('o'::('n'::('t'::('e'::('n'::('d'::[]))))))))) :: ((JSON.JStr
    ('d'::('e'::('s'::('i'::('g'::('n'::[]))))))) :: [])))) :: ((('b'::('i'::('o'::[]))),
    (JSON.JStr
    ('p'::('r'::('o'::('d'::('u'::('c'::('t'::(' '::('d'::('e'::('s'::('i'::('g'::('n'::('e'::('r'::[])))))))))))))))))) :: ((('p'::('r'::('o'::('j'::('e'::('c'::('t'::('s'::[])))))))),
    (JSON.JArr [])) :: [])))))))))) :: []))))) :: [])))))) :: ((JSON.JObject
    ((('i'::('d'::[])), (JSON.JStr
    ('S'::('A'::('L'::('E'::('S'::[]))))))) :: ((('n'::('a'::('m'::('e'::[])))),
    (JSON.JStr
    ('S'::('a'::('l'::('e'::('s'::[]))))))) :: ((('c'::('o'::('s'::('t'::('_'::('c'::('e'::('n'::('t'::('e'::('r'::[]))))))))))),
    (JSON.JStr
    ('2'::('0'::('0'::('1'::[])))))) :: ((('b'::('u'::('d'::('g'::('e'::('t'::('_'::('u'::('s'::('d'::[])))))))))),
    (coq_JQ (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      (Big_int_Z.mult_int_big_int 2
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      (Big_int_Z.mult_int_big_int 2
      Big_int_Z.unit_big_int))))))))))))))))))))))))) :: ((('e'::('m'::('p'::('l'::('o'::('y'::('e'::('e'::('s'::[]))))))))),
    (JSON.JArr ((JSON.JObject ((('i'::('d'::[])), (JSON.JStr
    ('u'::('-'::('d'::('a'::('v'::('e'::[])))))))) :: ((('n'::('a'::('m'::('e'::[])))),
    (JSON.JStr ('d'::('a'::('v'::('e'::[])))))) :: ((('a'::('g'::('e'::[]))),
    (coq_JQ
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      Big_int_Z.unit_big_int))))))) :: ((('e'::('m'::('a'::('i'::('l'::[]))))),
    (JSON.JStr
    ('d'::('a'::('v'::('e'::('@'::('a'::('c'::('m'::('e'::('.'::('c'::('o'::('m'::[]))))))))))))))) :: ((('p'::('h'::('o'::('n'::('e'::[]))))),
    (JSON.JStr
    ('+'::('1'::('-'::('6'::('4'::('6'::('-'::('5'::('5'::('5'::('-'::('4'::('0'::('0'::('1'::[]))))))))))))))))) :: ((('h'::('i'::('r'::('e'::('_'::('d'::('a'::('t'::('e'::[]))))))))),
    (JSON.JStr
    ('2'::('0'::('1'::('7'::('-'::('0'::('6'::('-'::('3'::('0'::[])))))))))))) :: ((('t'::('a'::('g'::('s'::[])))),
    (JSON.JArr ((JSON.JStr
    ('s'::('a'::('l'::('e'::('s'::[])))))) :: ((JSON.JStr
    ('l'::('e'::('a'::('d'::[]))))) :: [])))) :: ((('b'::('i'::('o'::[]))),
    (JSON.JStr
    ('a'::('c'::('c'::('o'::('u'::('n'::('t'::(' '::('e'::('x'::('e'::('c'::[])))))))))))))) :: ((('p'::('r'::('o'::('j'::('e'::('c'::('t'::('s'::[])))))))),
    (JSON.JArr ((JSON.JObject ((('i'::('d'::[])), (JSON.JStr
    ('c'::('r'::('m'::('-'::('d'::[]))))))) :: ((('n'::('a'::('m'::('e'::[])))),
    (JSON.JStr
    ('c'::('r'::('m'::[]))))) :: ((('s'::('t'::('a'::('r'::('s'::[]))))),
    (coq_JQ (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int))))) :: ((('l'::('a'::('b'::('e'::('l'::('s'::[])))))),
    (JSON.JArr ((JSON.JStr
    ('s'::('a'::('l'::('e'::('s'::[])))))) :: []))) :: ((('s'::('t'::('a'::('t'::('u'::('s'::[])))))),
    (JSON.JStr
    ('a'::('c'::('t'::('i'::('v'::('e'::[])))))))) :: ((('r'::('e'::('p'::('o'::[])))),
    (JSON.JStr
    ('g'::('i'::('t'::('@'::('g'::('i'::('t'::('h'::('u'::('b'::('.'::('c'::('o'::('m'::(':'::('a'::('c'::('m'::('e'::('/'::('c'::('r'::('m'::[]))))))))))))))))))))))))) :: ((('s'::('t'::('a'::('r'::('t'::('e'::('d'::[]))))))),
    (JSON.JStr
    ('2'::('0'::('1'::('6'::('-'::('0'::('7'::('-'::('1'::('5'::[])))))))))))) :: ((('m'::('e'::('t'::('r'::('i'::('c'::('s'::[]))))))),
    (JSON.JObject
    ((('p'::('r'::('s'::('_'::('o'::('p'::('e'::('n'::[])))))))),
    (coq_JQ Big_int_Z.unit_big_int)) :: ((('i'::('s'::('s'::('u'::('e'::('s'::('_'::('o'::('p'::('e'::('n'::[]))))))))))),
    (coq_JQ (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int))) :: ((('c'::('o'::('v'::('e'::('r'::('a'::('g'::('e'::('_'::('p'::('c'::('t'::[])))))))))))),
    (coq_JQ
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      Big_int_Z.unit_big_int))))))) :: []))))) :: []))))))))) :: []))) :: [])))))))))) :: ((JSON.JObject
    ((('i'::('d'::[])), (JSON.JStr
    ('u'::('-'::('e'::('r'::('i'::('n'::[])))))))) :: ((('n'::('a'::('m'::('e'::[])))),
    (JSON.JStr ('e'::('r'::('i'::('n'::[])))))) :: ((('a'::('g'::('e'::[]))),
    (coq_JQ (Big_int_Z.mult_int_big_int 2
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int)))))) :: ((('e'::('m'::('a'::('i'::('l'::[]))))),
    (JSON.JStr
    ('e'::('r'::('i'::('n'::('@'::('a'::('c'::('m'::('e'::('.'::('c'::('o'::('m'::[]))))))))))))))) :: ((('p'::('h'::('o'::('n'::('e'::[]))))),
    (JSON.JStr
    ('+'::('1'::('-'::('6'::('4'::('6'::('-'::('5'::('5'::('5'::('-'::('4'::('0'::('0'::('2'::[]))))))))))))))))) :: ((('h'::('i'::('r'::('e'::('_'::('d'::('a'::('t'::('e'::[]))))))))),
    (JSON.JStr
    ('2'::('0'::('2'::('5'::('-'::('0'::('6'::('-'::('0'::('1'::[])))))))))))) :: ((('t'::('a'::('g'::('s'::[])))),
    (JSON.JArr ((JSON.JStr
    ('i'::('n'::('t'::('e'::('r'::('n'::[]))))))) :: []))) :: ((('b'::('i'::('o'::[]))),
    (JSON.JStr
    ('s'::('u'::('m'::('m'::('e'::('r'::(' '::('i'::('n'::('t'::('e'::('r'::('n'::[]))))))))))))))) :: ((('p'::('r'::('o'::('j'::('e'::('c'::('t'::('s'::[])))))))),
    (JSON.JArr [])) :: [])))))))))) :: [])))) :: [])))))) :: ((JSON.JObject
    ((('i'::('d'::[])), (JSON.JStr
    ('H'::('R'::[])))) :: ((('n'::('a'::('m'::('e'::[])))), (JSON.JStr
    ('P'::('e'::('o'::('p'::('l'::('e'::(' '::('O'::('p'::('s'::[])))))))))))) :: ((('c'::('o'::('s'::('t'::('_'::('c'::('e'::('n'::('t'::('e'::('r'::[]))))))))))),
    (JSON.JStr
    ('3'::('0'::('0'::('1'::[])))))) :: ((('b'::('u'::('d'::('g'::('e'::('t'::('_'::('u'::('s'::('d'::[])))))))))),
    (coq_JQ (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      Big_int_Z.unit_big_int))))))))))))))))))))))) :: ((('e'::('m'::('p'::('l'::('o'::('y'::('e'::('e'::('s'::[]))))))))),
    (JSON.JArr ((JSON.JObject ((('i'::('d'::[])), (JSON.JStr
    ('u'::('-'::('p'::('e'::('g'::('g'::('y'::[]))))))))) :: ((('n'::('a'::('m'::('e'::[])))),
    (JSON.JStr
    ('p'::('e'::('g'::('g'::('y'::[]))))))) :: ((('a'::('g'::('e'::[]))),
    (coq_JQ
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      Big_int_Z.unit_big_int))))))) :: ((('e'::('m'::('a'::('i'::('l'::[]))))),
    (JSON.JStr
    ('p'::('e'::('g'::('g'::('y'::('@'::('a'::('c'::('m'::('e'::('.'::('c'::('o'::('m'::[])))))))))))))))) :: ((('p'::('h'::('o'::('n'::('e'::[]))))),
    (JSON.JStr
    ('+'::('1'::('-'::('4'::('1'::('5'::('-'::('5'::('5'::('5'::('-'::('5'::('0'::('0'::('5'::[]))))))))))))))))) :: ((('h'::('i'::('r'::('e'::('_'::('d'::('a'::('t'::('e'::[]))))))))),
    (JSON.JStr
    ('2'::('0'::('1'::('5'::('-'::('0'::('9'::('-'::('0'::('9'::[])))))))))))) :: ((('t'::('a'::('g'::('s'::[])))),
    (JSON.JArr ((JSON.JStr ('h'::('r'::[]))) :: ((JSON.JStr
    ('b'::('e'::('n'::('e'::('f'::('i'::('t'::('s'::[]))))))))) :: [])))) :: ((('b'::('i'::('o'::[]))),
    (JSON.JStr
    ('b'::('e'::('n'::('e'::('f'::('i'::('t'::('s'::(' '::('m'::('a'::('n'::('a'::('g'::('e'::('r'::[])))))))))))))))))) :: ((('p'::('r'::('o'::('j'::('e'::('c'::('t'::('s'::[])))))))),
    (JSON.JArr
    [])) :: [])))))))))) :: []))) :: [])))))) :: [])))))) :: ((('p'::('r'::('o'::('d'::('u'::('c'::('t'::('s'::[])))))))),
    (JSON.JArr ((JSON.JObject ((('s'::('k'::('u'::[]))), (JSON.JStr
    ('P'::('X'::('-'::('1'::('0'::('0'::[])))))))) :: ((('n'::('a'::('m'::('e'::[])))),
    (JSON.JStr
    ('P'::('h'::('o'::('e'::('n'::('i'::('x'::[]))))))))) :: ((('s'::('t'::('a'::('t'::('u'::('s'::[])))))),
    (JSON.JStr
    ('G'::('A'::[])))) :: ((('o'::('w'::('n'::('e'::('r'::('s'::[])))))),
    (JSON.JArr ((JSON.JStr
    ('a'::('l'::('i'::('c'::('e'::[])))))) :: ((JSON.JStr
    ('c'::('a'::('r'::('o'::('l'::[])))))) :: [])))) :: ((('s'::('t'::('a'::('r'::('s'::[]))))),
    (coq_JQ (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      (Big_int_Z.mult_int_big_int 2
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      Big_int_Z.unit_big_int)))))))) :: [])))))) :: ((JSON.JObject
    ((('s'::('k'::('u'::[]))), (JSON.JStr
    ('D'::('R'::('-'::('2'::('0'::('0'::[])))))))) :: ((('n'::('a'::('m'::('e'::[])))),
    (JSON.JStr
    ('D'::('r'::('a'::('k'::('e'::[]))))))) :: ((('s'::('t'::('a'::('t'::('u'::('s'::[])))))),
    (JSON.JStr
    ('E'::('O'::('L'::[]))))) :: ((('o'::('w'::('n'::('e'::('r'::('s'::[])))))),
    (JSON.JArr ((JSON.JStr
    ('a'::('l'::('i'::('c'::('e'::[])))))) :: []))) :: ((('s'::('t'::('a'::('r'::('s'::[]))))),
    (coq_JQ (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      (Big_int_Z.mult_int_big_int 2
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int))))))) :: [])))))) :: ((JSON.JObject
    ((('s'::('k'::('u'::[]))), (JSON.JStr
    ('T'::('T'::('-'::('3'::('0'::('0'::[])))))))) :: ((('n'::('a'::('m'::('e'::[])))),
    (JSON.JStr
    ('T'::('i'::('t'::('a'::('n'::[]))))))) :: ((('s'::('t'::('a'::('t'::('u'::('s'::[])))))),
    (JSON.JStr
    ('B'::('e'::('t'::('a'::[])))))) :: ((('o'::('w'::('n'::('e'::('r'::('s'::[])))))),
    (JSON.JArr ((JSON.JStr
    ('t'::('r'::('e'::('n'::('t'::[])))))) :: ((JSON.JStr
    ('g'::('r'::('a'::('c'::('e'::[])))))) :: [])))) :: ((('s'::('t'::('a'::('r'::('s'::[]))))),
    (coq_JQ
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      Big_int_Z.unit_big_int))))))) :: [])))))) :: []))))) :: ((('a'::('u'::('d'::('i'::('t'::[]))))),
    (JSON.JObject
    ((('g'::('e'::('n'::('e'::('r'::('a'::('t'::('e'::('d'::('_'::('b'::('y'::[])))))))))))),
    (JSON.JStr
    ('a'::('c'::('m'::('e'::('/'::('e'::('x'::('p'::('o'::('r'::('t'::('e'::('r'::('/'::('2'::('.'::('1'::('.'::('7'::[]))))))))))))))))))))) :: ((('e'::('x'::('p'::('o'::('r'::('t'::('e'::('d'::('_'::('a'::('t'::[]))))))))))),
    (JSON.JStr
    ('2'::('0'::('2'::('5'::('-'::('0'::('8'::('-'::('1'::('6'::('T'::('1'::('2'::(':'::('3'::('4'::(':'::('5'::('6'::('Z'::[])))))))))))))))))))))) :: ((('r'::('o'::('w'::('_'::('c'::('o'::('u'::('n'::('t'::[]))))))))),
    (coq_JQ
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int)))))) :: ((('c'::('h'::('e'::('c'::('k'::('s'::('u'::('m'::[])))))))),
    (JSON.JStr
    ('s'::('h'::('a'::('2'::('5'::('6'::(':'::('4'::('f'::('2'::('d'::('0'::('a'::('8'::('b'::('.'::('.'::('.'::('d'::('e'::('a'::('d'::('b'::('e'::('e'::('f'::[])))))))))))))))))))))))))))) :: [])))))) :: ((('m'::('e'::('t'::('a'::[])))),
    (JSON.JObject ((('v'::('e'::('r'::('s'::('i'::('o'::('n'::[]))))))),
    (JSON.JStr
    ('2'::('0'::('2'::('5'::('.'::('0'::('8'::[]))))))))) :: ((('r'::('e'::('v'::[]))),
    (coq_JQ (Big_int_Z.mult_int_big_int 2
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int))))))) :: [])))) :: []))))))))
