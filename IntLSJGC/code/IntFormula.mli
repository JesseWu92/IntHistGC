exception IntException of string

type formula =
  | TRUE
  | FALSE
  | AP of string
  | EQU of formula * formula
  | IMP of formula * formula
  | OR of formula * formula
  | AND of formula * formula

val sizeFormula : formula -> int
val numberOfTypes : int
val getTypeFormula : formula -> int

val generateCompare : int list -> (formula -> formula -> int)
val aRanking : int list
val intFCompare : formula -> formula -> int
val prep : formula -> formula

val exportFormula : formula -> string
val importFormula : string -> formula
val importFormula_ic : in_channel -> formula

val detClosure : (formula -> formula -> int) -> formula -> formula list
