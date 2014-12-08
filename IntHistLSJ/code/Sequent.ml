(** Sequent rules and application for intuitionistic propositional logic
    @author Jesse Wu, u5009927@anu.edu.au

    Brief implementation details.
    A set of axioms {A}  and conjecture C will be interpreted as:
      empty ::= {A} => C

    A sequent Gamma ::= Delta will be divided into Left and Right formula.
    These will be arrays of sets corresponding to each connective.
    Currently:
    Left = [{Atoms}, {AND}, {OR}, {IMP}, {Lookahead}]
    Right = [{Atoms}, {AND}, {OR}, {IMP}, {*currently unused*}]

    This implementation uses LSJ as its underlying calculus, see:
    Mauro Ferrari, Camillo Fiorentini, Guido Fiorino.
    Contraction-Free Linear Depth Sequent Calculi for Intuitionistic Propositional Logic with the Subformula Property and Minimal Depth Counter-Models.
    J. Autom. Reasoning 51(2): 129-149 (2013)
 *)

(** TODO: modus ponens priority, hmatch probably not
    For modus ponens, instead of a direct FSet.iter do:
    Copy every implication, into a list/array.
    Find all implications which will lead to modus ponens and move to front.
    Iterate through this list/array.

    reverse modus ponens?
    p =/> q |- p, q    q |- q
    -------------------------
           p => q |- q
    closes on second premise

    closes on only one premises in lsj
*)

open IntFormula
open MiscSolver
open IntMisc

(* Switches for optimisations *)
let sw_bjump = ref false
let sw_cache = ref false
let sw_cachemore = ref false
let sw_cache3 = ref false
let sw_hmatch = ref false

(********** Definitions **********)

(** A sequent is a pair (Left, Right) *)
type sequent = FSet.t array * FSet.t array;;

(* Number of component sets in a Left or Right array *)
let numSets = 5

(* Formula indexing within Left and Right arrays *)
let i_AP = 0
let i_AND = 1
let i_OR = 2
let i_IMP = 3
(* Lookahead *)
let i_L = 4

(* Indices corresponding to TRUE and FALSE *)
let idx_T = ref 0
let idx_F = ref 1

(* Variables for statistics gathering *)
let nodes = ref 0
let c_land = ref 0
let c_rand = ref 0
let c_lor = ref 0
let c_ror = ref 0
let c_limp = ref 0
let c_rimp = ref 0
let c_cache = ref 0
let c_bjump = ref 0

(* Exceptions for early returns *)
exception Found
exception Valid
exception Invalid

(********** Utilities **********)
(** Check if a formula exists in our arrays, if not add it
    @param fml Formula to find (as a IntFormula tree)
    @return Index of fml
 *)
let rec findAdd fml =
  try begin
    Hashtbl.find !htF fml
  end
  with Not_found -> begin
    let left = ref 0 in
    let right = ref 0 in
    begin
      match fml with
        AND (f1, f2)
      | OR (f1, f2)
      | IMP (f1, f2)
      | EQU (f1, f2) ->
        left := findAdd f1;
        right := findAdd f2;
      (* All atoms and constants should have been found by Hashtbl.find *)
      | _ -> invalid_arg "FindAdd: non-existant formula"
    end;
    addF fml !left !right
  end;;


(** Insert a formula to the appropriate set in some array
    @param f The formula to add, represented by an int
    @param lst Left or Right array
 *)
let insert f lst =
  match !arrayType.(f) with
    0
  | 1
  | 2 -> lst.(i_AP) <- FSet.add f lst.(i_AP)
  | 6 -> lst.(i_AND) <- FSet.add f lst.(i_AND)
  | 5 -> lst.(i_OR) <- FSet.add f lst.(i_OR)
  | 4 -> lst.(i_IMP) <- FSet.add f lst.(i_IMP)
  | 3 -> invalid_arg "Insert: EQU are not valid for insertion."
  | _ -> invalid_arg "Insert: Unknown formula type.";;

(** Delete a formula from an array
    @param f The formula to delete 
    @param lst Left or Right array
 *)
let delete f lst =
  match !arrayType.(f) with
    0
  | 1
  | 2 -> lst.(i_AP) <- FSet.remove f lst.(i_AP)
  | 6 -> lst.(i_AND) <- FSet.remove f lst.(i_AND)
  | 5 -> lst.(i_OR) <- FSet.remove f lst.(i_OR)
  | 4 -> lst.(i_IMP) <- FSet.remove f lst.(i_IMP)
  (* The following should not occur *)
  | _ -> invalid_arg "Deletion: EQU should not exist at sequent top level.";;

(** Check if a formula exists in a side of sequent.
    Ignores blocked left list and right tracking list.
    @param f Formula to check
    @param lst Left or Right array
 *)
let exists f lst =
  match !arrayType.(f) with
    0
  | 1
  | 2 -> FSet.mem f lst.(i_AP)
  | 6 -> FSet.mem f lst.(i_AND)
  | 5 -> FSet.mem f lst.(i_OR)
  | 4 -> FSet.mem f lst.(i_IMP)
  | 3 -> false (*invalid_arg "Exists: EQU are not stored in sequents"*)
  | _ -> invalid_arg "Exists: Unknown formula type.";;

(** Basic operations for the lookahead compartment *)
let existsLook f lst =
  FSet.mem f lst.(i_L);;

let insertLook f lst =
  lst.(i_L) <- FSet.add f lst.(i_L);;

let deleteLook f lst =
  lst.(i_L) <- FSet.remove f lst.(i_L);;


(** Print all formula within a set *)
let print_set set =
  FSet.iter (fun x -> print_string ((exportF x) ^ "; ")) set;;

(** Print a sequent *)
let print_seq s =
  print_string "lookahead:";
  print_set (fst s).(i_L);
  print_string "\nsequent: ";
  for i = 0 to numSets - 2 do
    print_set (fst s).(i)
  done;
  print_string " ::= ";
  Array.iter print_set (snd s);
  print_newline ();;

(** Print a sequent, identifying left and right component lists *)
let print_dbg_seq s =
  print_endline "Left:";
  Array.iter (fun x -> print_set x; print_newline ()) (fst s);
  print_endline "Right:";
  Array.iter (fun x -> print_set x; print_newline ()) (snd s);;

(** Empty sequent *)
let emptySeq () = 
  (Array.make numSets FSet.empty, Array.make numSets FSet.empty);;

(** Copy a sequent *)
let copySeq s =
  (Array.copy (fst s), Array.copy (snd s));;

(** Check if a sequent is a subset of another *)
let subSeq sub super =
  let return = ref true in
  for i = 0 to numSets - 1 do
    return := !return && (FSet.subset (fst sub).(i) (fst super).(i));
    return := !return && (FSet.subset (snd sub).(i) (snd super).(i))
  done;
  !return;;

(** Bit operations.
    Implemented as an alternative to sets.
    Individual bits of an int array are used to denote belonging.
    These allow for fast set and get operations, as well as
    efficient memory usage, on collections of formula.
 *)
let bsintsize = Sys.word_size - 1;;
let atomsBS = ref 0;;

(** Check if a formula (as integer) exists in a bitset *)
let memBS bs f = 
  let idx = f / bsintsize in
  let pos = f mod bsintsize in
  let mask = 1 lsl pos in
  (bs.(idx) land mask > 0);;

(** Set a bit *)
let setBS bs f =
  let idx = f / bsintsize in
  let pos = f mod bsintsize in
  let mask = 1 lsl pos in
  bs.(idx) <- bs.(idx) lor mask;;

(** Clear a bit *)
let clearBS bs f =
  let idx = f / bsintsize in
  let pos = f mod bsintsize in
  let mask = lnot (1 lsl pos) in
  bs.(idx) <- bs.(idx) land mask;;

(** Return the set difference "bs1 - bs2" *)
let diffBS bs1 bs2 =
  let len = Array.length bs1 in
  assert (len = Array.length bs2);
  let ret = Array.make len 0 in
  for i = 0 to len - 1 do
    ret.(i) <- bs1.(i) land (lnot bs2.(i));
  done;
  ret;;


(********** Initialisation **********)
(** Function to iterate through formula and find positive atoms
    @param f Formula to scan (as integer)
    @param pos BSet to store positive atoms in
    @param neg BSet to store negative atoms in
    @param cur Current polarity (1 for true, -1 for false, 0 for both)
 *)
let rec getStrongPolarity f pos neg cur =
  match !arrayType.(f) with
    0
  | 1 -> ()
  | 2 ->
      (match cur with
        1 -> setBS pos f
      | 0 -> setBS pos f; setBS neg f
      | _ -> setBS neg f)
  (* EQU is an AND of two implications, which cancel out in polarity *)
  | 3 ->
      getStrongPolarity !arrayDest1.(f) pos neg 0;
      getStrongPolarity !arrayDest2.(f) pos neg 0
  | 4 -> (* IMP *)
    (match cur with
      1 ->
      getStrongPolarity !arrayDest1.(f) pos neg (-1);
      getStrongPolarity !arrayDest2.(f) pos neg 1
    | 0 ->
      getStrongPolarity !arrayDest1.(f) pos neg 0;
      getStrongPolarity !arrayDest2.(f) pos neg 0
    | _ ->
      getStrongPolarity !arrayDest1.(f) pos neg 1;
      getStrongPolarity !arrayDest2.(f) pos neg (-1))
  | 5
  | 6 -> 
      getStrongPolarity !arrayDest1.(f) pos neg cur;
      getStrongPolarity !arrayDest2.(f) pos neg cur
  | _ -> invalid_arg "getStrongPolarity: unknown formula type";;

(** Return positive atoms of a formula as a list
    @param f Input formula (as integer)
    @return List of integers
 *)
let getPosAtoms f =
  let pos = Array.make !atomsBS 0 in
  let neg = Array.make !atomsBS 0 in
  getStrongPolarity f pos neg 1;
  let atomList = ref [] in
  let tSet = diffBS pos neg in
  (* Convert BSet into integer list *)
  for w=0 to !atomsBS -1 do
    let word = ref tSet.(w) in
    if !word = 0 then ()
    else begin
      (* if word is not empty, iterate over bits *)
      for b=0 to bsintsize - 1 do
        let value = !word land 1 in
        word := !word lsr 1;
        if value > 0 then begin
          (* find corresponding atom, using w and b *)
          let atom = w * bsintsize + b in
          atomList := !atomList @ [atom]
        end
      done 
    end
  done;
  !atomList;;

(** Normalise a formula by converting EQU into an AND formula
    @param f The formula to convert (as an integer)
    @return The new formula (as an integer)
 *)
let normalise f = 
  match !arrayType.(f) with
  | 3 ->
      (* Get left and right sides of equivalence formula *)
      let f1 = !arrayDest1.(f) in
      let f2 = !arrayDest2.(f) in
      (* Check if "f1 => f2" and "f2 => f1" exist, if not add them *)
      let imp1 = (IMP (!arrayFormula.(f1), !arrayFormula.(f2))) in
      let imp2 = (IMP (!arrayFormula.(f2), !arrayFormula.(f1))) in
      (* Special case of findAdd, with known subformula *)
      let findAddK fml d1 d2 =
        try begin
          Hashtbl.find !htF fml
        end
        with Not_found -> addF fml d1 d2
      in
      let idx_imp1 = findAddK imp1 f1 f2 in
      let idx_imp2 = findAddK imp2 f2 f1 in
      (* Check if overall "(f1 => f2) & (f2 => f1)" exists, if not add it *)
      let idx_and = findAddK (AND (imp1, imp2)) idx_imp1 idx_imp2 in
      (* Update arrayAtom *)
      if (!sw_hmatch) then begin
        !arrayAtom.(idx_and) <- !arrayAtom.(f);
        !arrayAtom.(idx_imp1) <- getPosAtoms idx_imp1;
        !arrayAtom.(idx_imp2) <- getPosAtoms idx_imp2
      end;
      idx_and
  | _ -> f;;


(** Initial setup to simplify rule applications
    Converts a formula into Left and Right sublists
    @param f Initial formula
 *)
let init f =
  let left = Array.make numSets FSet.empty in
  let right = Array.make numSets FSet.empty in
  (* Setup arrays *)
  let normf = ref TRUE in
  begin match f with
    EQU (f1, f2) -> normf := AND (IMP (f1, f2), IMP (f2, f1))
  | _ -> normf := f
  end;
  let (fml, fidx) = ppFormula !normf aRanking numberOfTypes in
  insert fidx right;
  (* Setup indices to TRUE and FALSE *)
  idx_F := Hashtbl.find !htF FALSE;
  idx_T := Hashtbl.find !htF TRUE;
  (* Setup atom array word size *)
  atomsBS := int_of_float (ceil (float !maxAtom /. float bsintsize));
  (* Compute positive occurences of atoms in all formulae *)
  if (!sw_hmatch) then begin
    arrayAtom := Array.make (Array.length !arrayFormula) [];
    for i=0 to !nrFormulae - 1 do
      !arrayAtom.(i) <- getPosAtoms i;
    done
  end;
  (left, right);;


(********** Optimisations **********)
(* Map from formulae to parent, for blame indentification in caching *)
type fSide =
  | LOOK
  | GAMMA
  | DELTA
type origin = fSide * MiscSolver.FSet.elt
type parMap = origin MiscSolver.FMap.t
type seqMap = { mutable lmap : parMap ref;
                mutable gmap : parMap ref;
                mutable dmap : parMap ref }

(** Add a mapping of formula f to its parent's mapping in map.
    Only does so if f does not already exist in side.
 *)
let updateMap f par map s side =
  match side with
    LOOK ->
    if (existsLook f (fst s)) then map 
    else FMap.add f par map
  | GAMMA ->
    if (exists f (fst s)) then map
    else FMap.add f par map
  | DELTA ->
    if (exists f (snd s)) then map
    else FMap.add f par map;;
(*
  if (FMap.mem f !map) then ()
  else map := FMap.add f par !map;;
*)

(** Find (side, parent) for a formula in a map
    @param f    input formula
    @param map  reference to map
    @param side side of f, when f is not in map
 *)
let getMap f map side =
  try FMap.find f map
  with Not_found -> (side, f);;

(* DEBUG map printing *)
let print_map map =
  FMap.iter (fun x (side, par) -> print_string (exportF x);
      print_string " maps to ";
      begin
        match side with
          LOOK -> print_string "LOOK: "
        | GAMMA -> print_string "GAMMA: "
        | DELTA -> print_string "DELTA: "
      end;
      print_endline (exportF par);
  ) map;;


(* Cache: store all proven true/false sequents *)
let trueSeq = ref Cache.empty
let falseSeq = ref Cache.empty

(* Switch when reduce cache checking, to ensure implications are checked *)
let doCache = ref false

(** Convert a fml to an int which differentiates between
    LOOK, GAMMA and DELTA.
    LOOK formulae f become 2f + 1
    GAMMA formula become 2f
    DELTA formula become -2f - 1
 *)
let convertFml2Int x side =
  match side with
    LOOK -> (2 * x) + 1
  | GAMMA -> 2 * x
  | DELTA -> ((-2) * x) - 1;;

(** Reverse of convertFml2Int
    Returns pair (x, fSide)
  *)
let convertInt2Fml x =
  (* DELTA if negative *)
  if (x < 0) then ((x + 1) / (-2), DELTA)
  (* GAMMA if even *)
  else if (x land 1 = 0) then (x / 2, GAMMA)
  (* LOOK otherwise *)
  else ((x - 1) / 2, LOOK);;

(** Convert a sequent to an ordered list. *)
let convertSeq s =
  let set = ref FSet.empty in
  for i=0 to numSets - 2 do
    FSet.iter (fun x ->
        set := FSet.add (convertFml2Int x GAMMA) !set) (fst s).(i);
    FSet.iter (fun x ->
        set := FSet.add (convertFml2Int x DELTA) !set) (snd s).(i);
  done;
  (*  Include compartment *)
  FSet.iter (fun x ->
      set := FSet.add (convertFml2Int x LOOK) !set) (fst s).(i_L);
  FSet.elements !set;;

(** Convert a int list back into a sequent *)
let convertBack l =
  let s = emptySeq () in
  List.iter (fun x ->
    let (f, side) = convertInt2Fml x in
    match side with
      LOOK -> insertLook f (fst s)
    | GAMMA -> insert f (fst s)
    | DELTA -> insert f (snd s)
  ) l;
  s;;


(** Add a formula to blame sequent
 *)
let add2Blame side fml blame =
    match side with
      LOOK -> insertLook fml (fst blame)
    | GAMMA -> insert fml (fst blame)
    | DELTA -> insert fml (snd blame);;

(** Set blame after hitting cache "src"
    @param blame Sequent
    @param src Int set
    @param lmap/gmap/dmap Map from formula to parents
 *)
let mergeCachehit blame src lmap gmap dmap =
  try
    FSet.iter (fun x ->
        let (f, side) = convertInt2Fml x in
        match side with
          LOOK -> let (pside, pfml) = getMap f lmap side in
            add2Blame pside pfml blame
        | GAMMA -> let (pside, pfml) = getMap f gmap side in
            add2Blame pside pfml blame
        | DELTA -> let (pside, pfml) = getMap f dmap side in
            add2Blame pside pfml blame
    ) src
  with Not_found ->
    print_endline "mergeCachehit: could not find formula origin";
    exit 1;;

(** Merge two sequents for blame, adding formulae from src
    @param blame Sequent
    @param src Sequent
    @param lmap/gmap/dmap Map (reference) from formula to parents
 *)
let mergeBlame blame src lmap gmap dmap =
  try begin
    for i = 0 to numSets - 2 do
      (* Left side of cache set *)
      FSet.iter (fun x ->
          let (side, parent) = getMap x gmap GAMMA in
          add2Blame side parent blame)
        (fst src).(i);
      (* Right side of cache set *)
      FSet.iter (fun x ->
          let (side, parent) = getMap x dmap DELTA in
          add2Blame side parent blame)
        (snd src).(i);
    done;
    FSet.iter (fun x ->
        let (side, parent) = getMap x lmap LOOK in
        add2Blame side parent blame)
      (fst src).(i_L);
  end
  with Not_found ->
    print_endline "mergeBlame: could not find formula origin";
    exit 1;;


(** Update blame after a branch returns *)
let updateBlame lmap gmap dmap blame =
  let doUpdate x oldlst map side =
    try begin
      let (side1, par) = getMap x map side in
      (* Update required if x did not exist originally *)
      if (x <> par) then begin
        if (side = LOOK) then deleteLook x oldlst
        else delete x oldlst;
        add2Blame side par blame
      end
    end
    with Not_found ->
      print_endline ("Blame updating: could not find parent of " ^ exportF x);
      exit 1
  in
  let b2 = copySeq blame in (* Copy to avoid double updating *)
  for i=0 to numSets - 2 do
    FSet.iter (fun x -> doUpdate x (fst blame) gmap GAMMA) (fst b2).(i);
    FSet.iter (fun x -> doUpdate x (snd blame) dmap DELTA) (snd b2).(i);
  done;
  FSet.iter (fun x -> doUpdate x (fst blame) lmap LOOK) (fst b2).(i_L);;

  

(********** Proof strategy / Heuristics **********)
(** Choice of formula to prove first *)
let chooseF set =
  FSet.min_elt set;;

(** Prioritise implications corresponding to modus ponens *)
let chooseImp s =
  let f = ref (chooseF (fst s).(i_IMP)) in
  if (FSet.is_empty (fst s).(i_AP)) then !f
  else begin
    (* Check if an instance of modus ponens is applicable *)
    try begin
    FSet.iter (fun x ->
        (* Check if left of implication exists in antecendent *)
        if (exists !arrayDest1.(x) (fst s)) then begin
          f := x;
          raise Found
        end) (fst s).(i_IMP);
    !f
    end with Found -> !f
  end;;


(** Try pick formula which contain atoms which match against those on the
    other side of sequent. Attempts to reduce branching.
 *)
let atomMatch s bf ba =
  let searchAtoms set check fml =
    List.iter (fun atm ->
      if (FSet.mem atm set) then begin
        bf := fml;
        ba := atm;
        raise Found
      end
    ) !arrayAtom.(check)
  in
  try 
  if (FSet.is_empty (fst s).(i_AP)) then begin
    if (FSet.is_empty (snd s).(i_AP)) then ()
    else begin
      (* Check or-left and imp-left *)
      FSet.iter (fun x -> searchAtoms (snd s).(i_AP) x x) (fst s).(i_OR);
      FSet.iter (fun x ->
          searchAtoms (snd s).(i_AP) !arrayDest2.(x) x) (fst s).(i_IMP)
    end
  end else begin
    (* Check and-right and imp-left *)
    FSet.iter (fun x -> searchAtoms (fst s).(i_AP) x x) (snd s).(i_AND);
    FSet.iter (fun x ->
        searchAtoms (fst s).(i_AP) !arrayDest1.(x) x) (fst s).(i_IMP);
    if (FSet.is_empty (snd s).(i_AP)) then ()
    else begin
      (* Check or-left and imp-left *)
      FSet.iter (fun x -> searchAtoms (snd s).(i_AP) x x) (fst s).(i_OR);
      FSet.iter (fun x ->
          searchAtoms (snd s).(i_AP) !arrayDest2.(x) x) (fst s).(i_IMP)
    end
  end;
  (* Return false if no atoms exist *)
  false;
  with Found -> true;;

(* Check atoms within subformula, stopping at IMPs *)
let rec searchSubfml check f bf atoms =
  if not (!arrayType.(check) = 5 || !arrayType.(check) = 6) then ()
  else begin
    List.iter (fun x ->
      if (FSet.mem x atoms) then begin
        bf := f;
        raise Found
      end
    ) !arrayAtom.(check)
  end;
  match !arrayType.(check) with
    6
  | 5 ->
      searchSubfml !arrayDest1.(check) f bf atoms;
      searchSubfml !arrayDest2.(check) f bf atoms
  | _ -> ();;

let subfmlMatch candidates atoms bf swap = 
  try
  FSet.iter (fun x -> searchSubfml !arrayDest1.(x) x bf atoms) candidates;
  swap := true;
  FSet.iter (fun x -> searchSubfml !arrayDest2.(x) x bf atoms) candidates;
  swap := false;
  false
  with Found -> true;;


(* Swap branch search order *)
let swapBranches s branch =
  let tmp = copySeq s in
  (* Don't use copySeq here as s is not a reference *)
  for i=0 to numSets - 1 do
    (fst s).(i) <- (fst !branch).(i);
    (snd s).(i) <- (snd !branch).(i);
  done;
  branch := tmp;;

(* Swap branch order in search to follow an atom *)
let swapAtomBranches s branch bf ba =
  match !arrayType.(!bf) with
    6
  | 5 -> if not (List.mem !ba !arrayAtom.(!arrayDest1.(!bf))) then
      swapBranches s branch
  | 4 -> if (List.mem !ba !arrayAtom.(!arrayDest2.(!bf))) then
      swapBranches s branch
  | _ -> invalid_arg "swapAtomBranches: incorrect branching formula chosen";;



(********** Simplifications **********)
(** Simplify a formula, using basic identities
    (x, x) is handled by prep in IntFormula.ml
    @param f Formula to simplify (IntFormula tree)
    @return Equivalent formula
 *)
let rec simplify f =
  match f with
    TRUE -> TRUE
  | FALSE -> FALSE
  | AP s -> AP s
  | AND (f1, f2) ->
    let left = simplify f1 in
    let right = simplify f2 in
    begin
    match left, right with
      TRUE, TRUE -> TRUE
    | TRUE, x -> x
    | x, TRUE -> x
    | FALSE, _ -> FALSE
    | _, FALSE -> FALSE
    | _, _ -> AND (left, right)
    end
  | OR (f1, f2) ->
    let left = simplify f1 in
    let right = simplify f2 in
    begin
    match left, right with
      TRUE, _ -> TRUE
    | _, TRUE -> TRUE
    | FALSE, x -> x
    | x, FALSE -> x
    | _, _ -> OR (left, right)
    end
  | IMP (f1, f2) ->
    let left = simplify f1 in
    let right = simplify f2 in
    begin
    match left, right with
      TRUE, FALSE -> FALSE
    | TRUE, x -> x
    | _, TRUE -> TRUE
    | FALSE, _ -> TRUE
    | _, _ -> IMP (left, right)
    end
  | EQU (f1, f2) ->
    let left = simplify f1 in
    let right = simplify f2 in
    begin
    match left, right with
      FALSE, TRUE -> FALSE
    | TRUE, FALSE -> FALSE
    | TRUE, x -> x
    | x, TRUE -> x
    | FALSE, x -> IMP (x, FALSE)
    | x, FALSE -> IMP (x, FALSE)
    | _, _ -> EQU (left, right) (* Lazy expansion AND (IMP (left, right), IMP (right, left)) *)
    end;;


(** Re-write (p0 => (p1 => p2)) to the equivalent ((p0 & p1) => p2) *)
let rec rewriteImps f =
  match f with
    TRUE -> TRUE
  | FALSE -> FALSE
  | AP s -> AP s
  | AND (f1, f2) -> AND (rewriteImps f1, rewriteImps f2)
  | OR (f1, f2) -> OR (rewriteImps f1, rewriteImps f2)
  | EQU (f1, f2) -> EQU (rewriteImps f1, rewriteImps f2)
  | IMP (f1, IMP (f2, f3)) -> rewriteImps
      (IMP (AND (rewriteImps f1, rewriteImps f2), rewriteImps f3))
  | IMP (f1, f2) -> IMP (rewriteImps f1, rewriteImps f2)



(********** Sequent calculus application **********)

(* Rules *)
(** Axioms: id, Top-right and Bottom-left
   A sequent is valid if we have the same formula in both Left and Right,
   or if we have Top on the right, or Bottom on the left.
   @param s Sequent to check for validity
   @return true if valid, false if not
 *)
let axioms s =
  (* 1 is FALSE, 0 is TRUE *)
  if (FSet.mem !idx_F (fst s).(i_AP) || FSet.mem !idx_T (snd s).(i_AP)) then
    true
  else begin
    (* Set intersection provided by Set runs in linear time *)
    let inters = ref (FSet.inter (fst s).(i_AP) (snd s).(i_AP)) in
    inters := FSet.union !inters (FSet.inter (fst s).(i_AND) (snd s).(i_AND));
    inters := FSet.union !inters (FSet.inter (fst s).(i_OR) (snd s).(i_OR));
    inters := FSet.union !inters (FSet.inter (fst s).(i_IMP) (snd s).(i_IMP));
    (* If the intersection is not empty, then rule-id applies *)
    not (FSet.is_empty !inters)
  end;;

(** Axioms, for subset caching
    @param s Sequent to check for validity
    @param blame Formula required for a proof
    @param gmap Map from formula on left of sequent to parent
    @param dmap Map from formula on right of sequent to parent
    @return true if valid, false if not
 *)
let axioms_cache s blame gmap dmap =
  (* Check for FALSE and TRUE in left and right respectively *)
  if (FSet.mem !idx_F (fst s).(i_AP)) then begin
    let (side, parent) = getMap !idx_F gmap GAMMA in
    add2Blame side parent blame;
    true
  end
  else if (FSet.mem !idx_T (snd s).(i_AP)) then begin
    let (side, parent) = getMap !idx_T dmap DELTA in
    add2Blame side parent blame;
    true
  end
  else begin
    let inters = ref (FSet.inter (fst s).(i_AP) (snd s).(i_AP)) in
    inters := FSet.union !inters (FSet.inter (fst s).(i_AND) (snd s).(i_AND));
    inters := FSet.union !inters (FSet.inter (fst s).(i_OR) (snd s).(i_OR));
    inters := FSet.union !inters (FSet.inter (fst s).(i_IMP) (snd s).(i_IMP));
    (* If the intersection is not empty, then rule-id applies *)
    if (not (FSet.is_empty !inters)) then begin
      (* Update for caching *)
      let f = FSet.choose !inters in
      let (side1, parent1) = getMap f gmap GAMMA in
      let (side2, parent2) = getMap f dmap DELTA in
      add2Blame side1 parent1 blame;
      add2Blame side2 parent2 blame;
      true
    end
    else false;
  end;;

(** Top-left and Bottom-right
    @param s Sequent on which the rule is to be applied
 *)
let top_bot s =
  (fst s).(i_AP) <- FSet.remove !idx_T (fst s).(i_AP);
  (snd s).(i_AP) <- FSet.remove !idx_F (snd s).(i_AP);;

(** AND-left
    @param s Sequent on which the rule is to be applied
    @param f And formula to apply rule on
    @param gmap Map from left subformula to parents
    @param dmap Map from right subformula to parents
 *)
let and_left s f gmap dmap blame =
  match !arrayType.(f) with
  | 6 ->
c_land := succ !c_land;
    let f1 = normalise !arrayDest1.(f) in
    let f2 = normalise !arrayDest2.(f) in
    delete f (fst s);
    (* Optimisations *)
    gmap := updateMap f1 (getMap f !gmap GAMMA) !gmap s GAMMA;
    gmap := updateMap f2 (getMap f !gmap GAMMA) !gmap s GAMMA;
    (* Insert after updateMap to allow checking *)
    insert f1 (fst s);
    insert f2 (fst s);
  | _ -> invalid_arg "Rule application: invalid AND formula.";;

(** AND-right
    @param s Sequent on which the rule is to be applied
    @param f Formula to apply rule to
    @param gmap Map from left subformula to parents
    @param dmap Map from right subformula to parents
    @return New sequent resulting from rule branching
 *)
let and_right s f gmap dmap blame =
  match !arrayType.(f) with
  | 6 ->
c_rand := succ !c_rand;
    let f1 = normalise !arrayDest1.(f) in
    let f2 = normalise !arrayDest2.(f) in
    delete f (snd s);
    let s2 = copySeq s in
    dmap := updateMap f1 (getMap f !dmap DELTA) !dmap s DELTA;
    dmap := updateMap f2 (getMap f !dmap DELTA) !dmap s2 DELTA;
    insert f1 (snd s);
    insert f2 (snd s2);
    s2
  | _ -> invalid_arg "Rule application: invalid AND formula.";;

(** OR-left
    @param s Sequent on which the rule is to be applied
    @param f Formula to apply rule to
    @param gmap Map from left subformula to parents
    @param dmap Map from right subformula to parents
    @return New sequent resulting from rule application
 *)
let or_left s f gmap dmap blame =
  match !arrayType.(f) with
  | 5 ->
c_lor := succ !c_lor;
    let f1 = normalise !arrayDest1.(f) in
    let f2 = normalise !arrayDest2.(f) in
    delete f (fst s);
    let s2 = copySeq s in
    gmap := updateMap f1 (getMap f !gmap GAMMA) !gmap s GAMMA;
    gmap := updateMap f2 (getMap f !gmap GAMMA) !gmap s2 GAMMA;
    insert f1 (fst s);
    insert f2 (fst s2);
    s2
  | _ -> invalid_arg "Rule application: invalid OR formula.";;

(** OR-right
    @param s Sequent on which the rule is to be applied
    @param f Formula to apply rule to
    @param gmap Map from left subformula to parents
    @param dmap Map from right subformula to parents
 *)
let or_right s f gmap dmap blame =
  match !arrayType.(f) with
  | 5 ->
c_ror := succ !c_ror;
    let f1 = normalise !arrayDest1.(f) in
    let f2 = normalise !arrayDest2.(f) in
    delete f (snd s);
    dmap := updateMap f1 (getMap f !dmap DELTA) !dmap s DELTA;
    dmap := updateMap f2 (getMap f !dmap DELTA) !dmap s DELTA;
    insert f1 (snd s);
    insert f2 (snd s);
  | _ -> invalid_arg "Rule application: invalid OR formula.";;

(** IMP-left
    @param s Sequent on which the rule is to be applied
    @param f Formula to apply rule to
    @param smap Map for first two premises
    @param smap3 Map for third premise
    @return List of sequents resulting from rule application
 *)
let imp_left s f smap smap3 blame =
  match !arrayType.(f) with
  | 4 ->
c_limp := succ !c_limp;
    let f1 = normalise !arrayDest1.(f) in
    let f2 = normalise !arrayDest2.(f) in
    let s1 = copySeq s in
    delete f (fst s1);
    let s2 = copySeq s1 in
    let s3 = (Array.copy (fst s1), Array.make numSets FSet.empty) in

    (* Apply changes to first premise, map updates must come first *)
    smap.gmap :=
        updateMap f2 (getMap f !(smap.gmap) GAMMA) !(smap.gmap) s1 GAMMA;
    insert f2 (fst s1);
    (* second premise *)
    smap.dmap :=
        updateMap f1 (getMap f !(smap.gmap) GAMMA) !(smap.dmap) s2 DELTA;
    smap.lmap :=
        updateMap f2 (getMap f !(smap.gmap) GAMMA) !(smap.lmap) s2 LOOK;
    insert f1 (snd s2);
    (fst s2).(i_L) <- FSet.add f2 (fst s2).(i_L);
    (* third premise *)
    smap3.dmap :=
        updateMap f1 (getMap f !(smap3.gmap) GAMMA) !(smap3.dmap) s3 DELTA;
    insert f1 (snd s3);
    FSet.iter (fun x ->
        (* lmap is always empty, as nobranch rules cannot modify it *)
        smap3.gmap := updateMap x (LOOK, x) !(smap3.gmap) s3 GAMMA;
        insert x (fst s3)
     ) (fst s3).(i_L);
    (fst s3).(i_L) <- FSet.empty;
    (* getmap from smap not smap3.gmap, to avoid additions from above *)
    smap3.lmap :=
        updateMap f2 (getMap f !(smap.gmap) GAMMA) !(smap3.lmap) s3 LOOK;
    (fst s3).(i_L) <- FSet.singleton f2;
    (* return premises *)
    [s1; s2; s3]
  | _ -> invalid_arg "Rule application: invalid l-IMP formula.";;

(** IMP-right
    @param s Sequent on which the rule is to be applied
    @param f Chosen right IMP formula
    @param smap Map for first premise
    @param smap2 Map for second premise
    @return New sequent resulting from rule application
 *)
let imp_right s f smap smap2 blame =
  match !arrayType.(f) with
  | 4 ->
c_rimp := succ !c_rimp;
    let f1 = normalise !arrayDest1.(f) in
    let f2 = normalise !arrayDest2.(f) in
    let s1 = copySeq s in
    delete f (snd s1);
    let s2 = (Array.copy (fst s1), Array.make numSets FSet.empty) in
    (* first premise *)
    smap.gmap :=
        updateMap f1 (getMap f !(smap.dmap) DELTA) !(smap.gmap) s1 GAMMA;
    smap.dmap :=
        updateMap f2 (getMap f !(smap.dmap) DELTA) !(smap.dmap) s1 DELTA;
    insert f1 (fst s1);
    insert f2 (snd s1);
    (* second premise *)
    smap2.gmap :=
        updateMap f1 (getMap f !(smap2.dmap) DELTA) !(smap2.gmap) s2 GAMMA;
    smap2.dmap :=
        updateMap f2 (getMap f !(smap2.dmap) DELTA) !(smap2.dmap) s2 DELTA;
    (* move lookahead formula into second premise *)
    FSet.iter (fun x ->
        smap2.gmap := updateMap x (LOOK, x) !(smap2.gmap) s2 GAMMA;
        insert x (fst s2)
     ) (fst s2).(i_L);
    (fst s2).(i_L) <- FSet.empty;
    insert f1 (fst s2);
    insert f2 (snd s2);
    [s1; s2]
  | _ -> invalid_arg "Rule application: invalid first-IMP formula.";;


(** Apply all possible non-branching rules to a Sequent *)
let rec no_branch s gmap dmap blame =
  try begin
    top_bot s;
    (* AND-left *)
    while (not (FSet.is_empty (fst s).(i_AND))) do
      and_left s (chooseF (fst s).(i_AND)) gmap dmap blame
    done;
    (* OR-right *)
    while (not (FSet.is_empty (snd s).(i_OR))) do
      or_right s (chooseF (snd s).(i_OR)) gmap dmap blame
    done;
    (* Check if we have created any more non-branching formulae *)
    if (FSet.is_empty (fst s).(i_AND) && FSet.is_empty (snd s).(i_OR))
    then ()
    else no_branch s gmap dmap blame
  end;
  with Not_found -> print_endline "No_branch: unexpected operation on empty set.";
  exit 1;;


(** Main loop. Basic algorithm overview:
    1. Saturate: Apply all invertible rules
      a. Apply non-branching rules and check for validity
      b. Apply branching rules
    2. Choose a right implication
      a. If none, then return not valid
    3. If right-first has not been applied to this formula
      a. Jump then apply the right first rule
      b. Don't jump and apply the right rest rule
    Go to 1.

    @param s Sequent to prove
    @param blame Formula required for a proof (backjumping/cache)
 *)
let rec mainl s blame =
  nodes := succ !nodes;
  (* Cache cleanup, every 2^14 nodes *)
(*
  if (!nodes land 0x3fff = 0) then begin
    trueSeq := Cache.trimSubset !trueSeq;
    trueSeq := Cache.cleanCache !trueSeq;
    falseSeq := Cache.cleanCache !falseSeq;
  end;
*)

  (* Create local maps to track origins of formula *)
  let gmap = ref FMap.empty in
  let dmap = ref FMap.empty in

  (* Apply non-branching rules *)
  no_branch s gmap dmap blame;

  (* Check axioms *)
  if (axioms_cache s blame !gmap !dmap) then true
  else try begin
    (* Only check cache every 2 nodes *)
    if (!sw_cache3 && (not !doCache) && (!nodes land 0b1 > 0)) then
        raise Not_found
    else begin
      doCache := false;
      (* Check cache *)
      let hit = ref FSet.empty in
      let slist = convertSeq s in
      if (Cache.findSubset slist !trueSeq hit) then begin

(* TODO: remove debug *)
(*
print_endline (string_of_int !nodes);
print_endline "CACHE HIT:";
print_seq s;
print_endline "\nFROM CACHED ENTRY:";
print_seq (convertBack (FSet.elements !hit));
print_newline ();
*)

        mergeCachehit blame !hit FMap.empty !gmap !dmap;
        c_cache := succ !c_cache;
        true
      end else
        if (Cache.existsSuperset slist !falseSeq) then begin
          (* No need to merge if false, everything will be added to fCache *)
          c_cache := succ !c_cache;
          false
        end else raise Not_found
    end
  end with Not_found -> try begin

    (* Perform branching rules *)
    let branch = ref s in
    let pbranches () =
      try begin
      (* Prove branches *)
      if (mainl s blame) then begin
        (* If first branch is true, setup new blame for second *)
        let blame2 = emptySeq () in
        (* If backjumping switch is on *)
        if (!sw_bjump && (subSeq blame !branch)) then begin
          c_bjump := succ !c_bjump;
          (* update cache *)
          updateBlame FMap.empty !gmap !dmap blame;
          if (!sw_cachemore) then
              trueSeq := Cache.add (convertSeq blame) !trueSeq;
          raise Valid
        end;
        (* If bjump not set, or does not apply, process second branch *)
        if (mainl !branch blame2) then begin
          updateBlame FMap.empty !gmap !dmap blame;
          mergeBlame blame blame2 FMap.empty !gmap !dmap;
          true
        end else false
      end
      (* could not prove first branch *)
      else false
      end with Valid -> true
    in (* pbranches *)

    (* If heuristics don't apply, saturate as usual *)
    begin
      (* AND-right *)
      if (not (FSet.is_empty (snd s).(i_AND))) then begin
        let f = chooseF (snd s).(i_AND) in
        branch := and_right s f gmap dmap blame;
        pbranches ()
      end else begin
        (* OR-left *)
        if (not (FSet.is_empty (fst s).(i_OR))) then begin
          let f = chooseF (fst s).(i_OR) in
          branch := or_left s f gmap dmap blame;
          pbranches ()
        end else
          (* If we reach this point, the sequent is saturated *)
          choose s blame gmap dmap
      end
    end
  end
  with Not_found -> begin
    print_endline "Mainl: unexpected operation (empty set or find)";
    exit 1
  end

(** Choose a combination of left and right implication formula.
    gmap and dmap must be passed, as we have not branched yet.
 *)
and choose s blame gmap dmap =
  let premises = ref [] in
  (* Keep copy of premises for invalid caching *)
  let premCopy = ref (emptySeq ()) in
  try begin
    (* Try all left implications *)
    if (not (FSet.is_empty (fst s).(i_IMP))) then
      FSet.iter (fun f ->
        (* Create new maps for this implication.
           Copy gmap and dmap changes from no_branch rules *)
        let smap = { lmap=ref FMap.empty;
                     gmap=ref (FMap.map (fun x -> x) !gmap);
                     dmap=ref (FMap.map (fun x -> x) !dmap) } in
        let smap3 = { lmap=ref FMap.empty;
                     gmap=ref (FMap.map (fun x -> x) !gmap);
                     dmap=ref (FMap.map (fun x -> x) !dmap) } in
        (* Apply imp_left *)
        premises := imp_left s f smap smap3 blame;

(*  Recurse on premises.
    First two premises are invertible:
      Failures lead to Invalid.
      Success just means continue to next premise.
    The final premise is non-invertible:
      Success leads to valid.
      Failure mean we have to try another implication.
 *)
        (* Premise 1 *)
        let newBlame1 = emptySeq () in
        premCopy := copySeq (List.hd !premises);
        doCache := true;
        if (mainl (List.hd !premises) newBlame1) then begin
          if (!sw_cache) then
            trueSeq := Cache.add (convertSeq newBlame1) !trueSeq;
        end else raise Invalid;
        (* Premise 2 *)
        let newBlame2 = emptySeq () in
        premCopy := copySeq (List.nth !premises 1);
        doCache := true;
        if (mainl (List.nth !premises 1) newBlame2) then begin
          if (!sw_cache) then
            trueSeq := Cache.add (convertSeq newBlame2) !trueSeq;
        end else raise Invalid;
        (* Premise 3 *)
        let newBlame3 = emptySeq () in
        premCopy := copySeq (List.nth !premises 2);
        doCache := true;
        if (mainl (List.nth !premises 2) newBlame3) then begin
          (* Merge all blames *)
          mergeBlame blame newBlame1 !(smap.lmap) !(smap.gmap) !(smap.dmap);
          mergeBlame blame newBlame2 !(smap.lmap) !(smap.gmap) !(smap.dmap);
          mergeBlame blame newBlame3 !(smap3.lmap) !(smap3.gmap) !(smap3.dmap);
(* TODO remove debug
print_endline "adding to cache";
print_seq (convertBack (convertSeq blame));
print_seq (convertBack (convertSeq newBlame3));
print_seq newBlame3;
*)
          if (!sw_cache) then begin
            trueSeq := Cache.add (convertSeq newBlame3) !trueSeq;
            trueSeq := Cache.add (convertSeq blame) !trueSeq
          end;
          raise Valid

        end else begin
          (* Do not raise Invalid. Cache, then move to next implication *)
          if(!sw_cache) then
            falseSeq := Cache.add (convertSeq !premCopy) !falseSeq;
        end
      ) (fst s).(i_IMP);
    if (not (FSet.is_empty (snd s).(i_IMP))) then
      FSet.iter (fun f ->
        (* Create new maps for this implication.
           Copy gmap and dmap changes from no_branch rules *)
        let smap = { lmap=ref FMap.empty;
                     gmap=ref (FMap.map (fun x -> x) !gmap);
                     dmap=ref (FMap.map (fun x -> x) !dmap) } in
        let smap2 = { lmap=ref FMap.empty;
                     gmap=ref (FMap.map (fun x -> x) !gmap);
                     dmap=ref (FMap.map (fun x -> x) !dmap) } in
        (* Apply imp_right *)
        premises := imp_right s f smap smap2 blame;

        (* Premise 1: invertible *)
        let newBlame1 = emptySeq () in
        premCopy := copySeq (List.hd !premises);
        doCache := true;
        if (mainl (List.hd !premises) newBlame1) then begin
          if (!sw_cache) then
            trueSeq := Cache.add (convertSeq newBlame1) !trueSeq;
        end else raise Invalid;
        (* Premise 2: non-invertible *)
        let newBlame2 = emptySeq () in
        premCopy := copySeq (List.nth !premises 1);
        doCache := true;
        if (mainl (List.nth !premises 1) newBlame2) then begin
          (* Merge all blames *)
          mergeBlame blame newBlame1 !(smap.lmap) !(smap.gmap) !(smap.dmap);
          mergeBlame blame newBlame2 !(smap2.lmap) !(smap2.gmap) !(smap2.dmap);
          if (!sw_cache) then begin
            trueSeq := Cache.add (convertSeq newBlame2) !trueSeq;
            trueSeq := Cache.add (convertSeq blame) !trueSeq
          end;
          raise Valid
        end else begin
          (* Do not raise Invalid. Cache, then move to next implication *)
          if(!sw_cache) then
            falseSeq := Cache.add (convertSeq !premCopy) !falseSeq;
        end
      ) (snd s).(i_IMP);
    (* No remaining applicable rules, add to invalid cache *)
    if (!sw_cache) then falseSeq := Cache.add (convertSeq s) !falseSeq;
    false
  end
  with Valid -> true
    | Invalid ->
      if (!sw_cache) then
        falseSeq := Cache.add (convertSeq !premCopy) !falseSeq;
      false;;


(** Method to call to run a sequent proof
    @param s Sequent to prove
 *)
let prove s = mainl s (emptySeq ());;
