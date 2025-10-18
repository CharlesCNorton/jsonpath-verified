open Datatypes

val nth_error : 'a1 list -> nat -> 'a1 option

val concat : 'a1 list list -> 'a1 list

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1

val forallb : ('a1 -> bool) -> 'a1 list -> bool

val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list

val find : ('a1 -> bool) -> 'a1 list -> 'a1 option

val combine : 'a1 list -> 'a2 list -> ('a1 * 'a2) list

val seq : nat -> nat -> nat list
