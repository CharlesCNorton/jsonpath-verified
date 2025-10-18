open BinInt
open Datatypes

type coq_Q = { coq_Qnum : Big_int_Z.big_int; coq_Qden : Big_int_Z.big_int }

(** val inject_Z : Big_int_Z.big_int -> coq_Q **)

let inject_Z x =
  { coq_Qnum = x; coq_Qden = Big_int_Z.unit_big_int }

(** val coq_Qcompare : coq_Q -> coq_Q -> comparison **)

let coq_Qcompare p q =
  Z.compare (Z.mul p.coq_Qnum q.coq_Qden) (Z.mul q.coq_Qnum p.coq_Qden)
