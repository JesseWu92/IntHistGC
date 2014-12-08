module I :
  sig
    exception IntException of string
    type formula =
      IntFormula.formula =
        TRUE
      | FALSE
      | AP of string
      | EQU of formula * formula
      | IMP of formula * formula
      | OR of formula * formula
      | AND of formula * formula
    val numberOfTypes : int
    val getTypeFormula : formula -> int
    val generateCompare : int list -> formula -> formula -> int
    val aRanking : int list
    val exportFormula : formula -> string
    val importFormula : string -> formula
    val importFormula_ic : in_channel -> formula
    val sizeFormula : formula -> int
    val detClosure : (formula -> formula -> int) -> formula -> formula list
  end
val arrayFormula : I.formula array ref
val htF : (I.formula, int) Hashtbl.t ref
val maxAtom : int ref
val arrayAtom : int list array ref

val initTables : (I.formula, int) Hashtbl.t -> I.formula -> int -> unit
val ppFormula : I.formula -> int list -> int -> I.formula * int
val exportF : int -> string
val addF : I.formula -> int -> int -> int
