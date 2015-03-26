(** Common functions and data structures
    which are shared by the decision procedures for Int-satisfiability.
    @author Jimmy Thomson
 *)


module I = IntFormula


open MiscSolver


(** This lookup table maps integers (representing formulae)
    to their corresponding formulae.
 *)
let arrayFormula = ref (Array.make 0 I.TRUE)

(** This table maps formulae to their corresponding integer
 *)
let htF = ref (Hashtbl.create 0)

(** The largest integer corresponding to an atom *)
let maxAtom = ref 0

(** Array from formulae (int) to list of positive atoms *)
let arrayAtom = ref (Array.make 0 [])


let initTables ht f n =
  !arrayFormula.(n) <- f;
  !arrayType.(n) <- I.getTypeFormula f;
  match f with
	  I.FALSE
	| I.TRUE -> ()
	| I.AP s -> ()
	| I.OR (f1,f2)
	| I.AND (f1,f2)
	| I.IMP (f1,f2)
	| I.EQU (f1,f2) ->
		!arrayDest1.(n) <- Hashtbl.find ht f1;
		!arrayDest2.(n) <- Hashtbl.find ht f2



(** Converts a formula and initialises the internal tables of
	this module.  @param f The initial formula that is to be
	tested for satisfiability.  @param rankingF A complete
	ranking of the different types of formulae.  @param noty
	The number of types in rankingF, starting from the
	beginning of the list, whose formulae are stored in the
	bitsets explicitly.  @return The resulting formula once as
	real formula and once in integer representation.  *)
let ppFormula f rankingF noty =
  let flist = I.detClosure (I.generateCompare rankingF) f in (* Include subformulae from globals in the closure *)
  let getFml f = f in
  let module Ht = Hashtbl in
  let noF = Array.make I.numberOfTypes 0 in
  let liter f =
	let ty = I.getTypeFormula (getFml f) in
	  noF.(ty) <- succ noF.(ty)
  in
	List.iter liter flist;
	let idxF = Array.make I.numberOfTypes 0 in
	let len = List.fold_left (fun idx ty -> idxF.(ty) <- idx; idx + noF.(ty)) 0 rankingF in
	let countSize (size, idx) ty =
	  let nsize = if idx > 0 then size + noF.(ty) else size in
		(nsize, pred idx)
	in
	let (size, _) = List.fold_left countSize (0, noty) rankingF in
	  arrayFormula := Array.make (2 * len) I.TRUE;
	  arrayType := Array.make (2 * len) (-1);
	  arrayDest1 := Array.make (2 * len) (-1);
	  arrayDest2 := Array.make (2 * len) (-1);
	  htF := Ht.create (2 * size);
	  let fillHt f =
		let ty = I.getTypeFormula (getFml f) in
      (* Keep track of largest integer representing an atom *)
      if (ty = 2) then maxAtom := idxF.(ty);
      (* Fill htF *)
		  Ht.add !htF f idxF.(ty);
		  idxF.(ty) <- succ idxF.(ty)
	  in
		List.iter fillHt flist;

		let initTbl = initTables !htF in
		  Ht.iter initTbl !htF;
		  
		  initMisc size (Ht.find !htF (I.FALSE)) (Ht.find !htF (I.TRUE));
		  (f, Ht.find !htF f)


(** Converts a formula into a string.
    @param f A formula in integer representation.
    @return A string representing f.
*)
let exportF f = I.exportFormula !arrayFormula.(f)


(** Add a formula to our maps
    @param f A formula
    @param d1 Index of left subformula
    @param d2 Index of right subformula
    @return The index of the newly added formula
 *)
let addF f d1 d2 =
  let n = !nrFormulae in
  nrFormulae := succ !nrFormulae;
  (* Ensure arrays can hold the new formula *)
  if (Array.length !arrayFormula = n) then begin
    let emptyArray = Array.make n (-1) in
    arrayFormula := Array.append !arrayFormula (Array.make n I.TRUE);
    arrayType := Array.append !arrayType emptyArray;
    arrayDest1 := Array.append !arrayDest1 emptyArray;
    arrayDest2 := Array.append !arrayDest2 emptyArray;
    arrayAtom := Array.append !arrayAtom (Array.make n [])
  end;
  (* Update arrays with new formula *)
  Hashtbl.add !htF f n;
  !arrayFormula.(n) <- f;
  !arrayType.(n) <- I.getTypeFormula f;
  begin
    match f with
      I.FALSE
    | I.TRUE -> ()
    | I.AP s -> ()
    | I.OR (f1,f2)
    | I.AND (f1,f2)
    | I.IMP (f1,f2)
    | I.EQU (f1,f2) ->
      !arrayDest1.(n) <- d1;
      !arrayDest2.(n) <- d2
  end;
  n
