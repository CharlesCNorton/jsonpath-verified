open BinInt
open Datatypes

type coq_Q = { coq_Qnum : Big_int_Z.big_int; coq_Qden : Big_int_Z.big_int }

val inject_Z : Big_int_Z.big_int -> coq_Q

val coq_Qcompare : coq_Q -> coq_Q -> comparison
