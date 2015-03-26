(** Common functions and data structures
    which are shared by most of the decision procedures.
    @author Florian Widmann, Jimmy Thomson
 *)


(** This table maps formulae (represented as integers)
    to their "types" (i.e. and, or, <>, etc;
    represented as integers).
 *)
let arrayType = ref (Array.make 0 (-1))

(** These lookup tables map formulae (represented as integers)
    to their decompositions (represented as integers).
    This is done according to the rules of the tableau procedure
    and depends on the type of the formulae.
 *)
let arrayDest1 = ref (Array.make 0 (-1))
let arrayDest2 = ref (Array.make 0 (-1))

(** This lookup table maps formulae (represented as integers)
    to their negation (in negation normal form).
 *)
let arrayNeg = ref (Array.make 0 (-1))


(** Counter that is used to assign unique id numbers to nodes.
 *)
let idcount = ref 0

(** Returns an unused id number.
 *)
let getNewId () =
  if !idcount < max_int then begin incr idcount; !idcount end
  else raise (Failure "Id overflow!")



(** An instantiation of a set (of the standard library)
    for formulae (in integer representation).
 *)
module FSet = Set.Make(
  struct
    type t = int
    let compare (i1 : int) i2 = compare i1 i2
  end
 )

(** An instantiation of a map (of the standard library)
    for formulae (in integer representation).
 *)
module FMap = Map.Make(
  struct
    type t = int
    let compare (i1 : int) i2 = compare i1 i2
  end
 )


(** The number of formulae which must be positive.
    The formulae are represented by the integers 0..(nrFormulae-1).
    It is assumed that formulae of the same type are grouped together
    (e.g. EX-formulae are exactly the formulae with index in [lposEX..hposEX]).
    It is further assumed that all principal formulae (e.g. or-formulae) come first,
    then come the EX-formulae, then the AX-formulae, and finally all remaining formulae.
 *)
let nrFormulae = ref (-1)





(** The integer representing the formula False.
    It must hold that !arrayNeg.(bsfalse) = bstrue.
 *)
let bsfalse = ref (-1)

(** The integer representing the formula True.
    It must hold that !arrayNeg.(bstrue) = bsfalse.
 *)
let bstrue = ref (-1)




(** Initialises the global fields of this module
    with the exception of the tables.
    This procedure must only be invoked once.
    @param size The number of formulae which must be positive (cf. nrFormulae).
    @param bsf cf. bsfalse
    @param bst cf. bstrue
    @param lIMP cf. lposIMP
    @param nrIMP The number of IMP-formulae.
 *)
let initMisc size bsf bst =
  assert (size > 0);
  nrFormulae := size;
  bsfalse := bsf;
  bstrue := bst;
  idcount := 0
