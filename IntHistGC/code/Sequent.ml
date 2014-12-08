(** Sequent rules and application for intuitionistic propositional logic
    @author Jesse Wu, u5009927@anu.edu.au

    Brief implementation details.
    A set of axioms {A}  and conjecture C will be interpreted as:
      empty ::= {A} => C

    A sequent Gamma ::= Delta will be divided into Left and Right formula.
    These will be arrays of sets corresponding to each connective.
    Currently:
    Left = [{Atoms}, {AND}, {OR}, {IMP}, {Blocked IMP}]
    Right = [{Atoms}, {AND}, {OR}, {IMP}, {Right first IMP}]

    The Blocked IMP set contains implications which are prevented from
    being applied to rules (except id) until unblocked by a IMP-first.

    The Right first IMP set simply keeps track of implications which
    have had the IMP_first rule applied to them.
 *)

open IntFormula
open MiscSolver
open IntMisc

(* Switches for optimisations *)
let sw_bjump = ref false
let sw_cache = ref false
let sw_cachemore = ref false
let sw_cache3 = ref false
let sw_simp = ref false
let sw_simpExt = ref false
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
(* Blocked left implications, and right-first tracking list *)
let i_B = 4
let i_R = 4

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

(** Checks if a formula exists in a sequent antecedent.
    Includes blocked left list.
 *)
let existsLeft f lst =
  match !arrayType.(f) with
    0
  | 1
  | 2 -> FSet.mem f lst.(i_AP)
  | 6 -> FSet.mem f lst.(i_AND)
  | 5 -> FSet.mem f lst.(i_OR)
  | 4 -> FSet.mem f lst.(i_IMP) || FSet.mem f lst.(i_B)
  | 3 -> false (*invalid_arg "Exists: EQU are not stored in sequents"*)
  | _ -> invalid_arg "Exists: Unknown formula type.";;


(** Print all formula within a set *)
let print_set set =
  FSet.iter (fun x -> print_string ((exportF x) ^ "; ")) set;;

(** Print a sequent *)
let print_seq s =
  Array.iter print_set (fst s);
  print_string " ::= ";
  (* Omit right-first tracking list *)
  for i = 0 to numSets - 2 do
    print_set (snd s).(i)
  done;
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
  for i = 0 to numSets - 2 do
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
type origin = bool * MiscSolver.FSet.elt
type parMap = origin MiscSolver.FMap.t ref

(** Add a mapping of fml to parent's mapping in map.
    Only does so if fml does not already exist.
 *)
let updateMap f par map s side =
  if side then begin
    if (existsLeft f (fst s)) then ()
    else map := FMap.add f par !map
  end else begin
    if (exists f (snd s)) then ()
    else map := FMap.add f par !map
  end;;
(*
  if (FMap.mem f !map) then ()
  else map := FMap.add f par !map;;
*)

(** Find (side, parent) for a formula in a map *)
let getMap f map side =
  try FMap.find f !map
  with Not_found -> (side, f);;

(* DEBUG map printing *)
let print_maps lmap rmap =
  print_endline "LEFT MAP";
  FMap.iter (fun x (side, par) -> print_string (exportF x);
      print_string " maps to ";
      print_endline (exportF par);) lmap;
  print_endline "RIGHT MAP";
  FMap.iter (fun x (side, par) -> print_string (exportF x);
      print_string " maps to ";
      print_endline (exportF par);) rmap;;


(* Cache: store all proven true/false sequents *)
let trueSeq = ref Cache.empty
let falseSeq = ref Cache.empty

(* Switch to reduce cache checking *)
let doCache = ref false

(** Convert a sequent to an ordered list.
    Formulae in the succedent are represented by negative integers.
 *)
let convertSeq s =
  let set = ref FSet.empty in
  for i=0 to numSets - 2 do
    set := FSet.union (fst s).(i) !set;
    FSet.iter (fun x -> set := FSet.add ((-1) * x) !set) (snd s).(i);
  done;
  set := FSet.union (fst s).(i_B) !set;
  FSet.elements !set;;

(** Set blame after hitting cache "src"
    @param blame Sequent
    @param src Int set
    @param lmap/rmap Map from formula to parents
 *)
let mergeCachehit blame src lmap rmap =
  try
    FSet.iter (fun x ->
        if (x < 0) then begin
          let (side, parent) = getMap ((-1) * x) rmap false in
          if (side) then
            insert parent (fst blame)
          else insert parent (snd blame)
        end
        else begin
          let (side, parent) = getMap x lmap true in
          if (side) then
            insert parent (fst blame)
          else insert parent (snd blame)
        end) src
  with Not_found ->
    print_endline "mergeCachehit: could not find formula origin";
    exit 1;;

(** Merge two sequents for blame, adding formulae from src
    @param blame Sequent
    @param src Sequent
    @param lmap/rmap Map from formula to parents
 *)
let mergeBlame blame src lmap rmap =
  try begin
    for i = 0 to numSets - 2 do
      (* Left side of cache set *)
      FSet.iter (fun x ->
          let (side, parent) = getMap x lmap true in
          if (side) then
            insert parent (fst blame)
          else insert parent (snd blame))
        (fst src).(i);
      (* Right side of cache set *)
      FSet.iter (fun x ->
          let (side, parent) = getMap x rmap false in
          if (side) then
            insert parent (fst blame)
          else insert parent (snd blame))
        (snd src).(i);
    done
  end
  with Not_found ->
    print_endline "mergeBlame: could not find formula origin";
    exit 1;;


(** Update cache after a branch returns *)
let updateBlame lmap rmap blame =
  let doUpdate x oldlst map side =
    try begin
      let (side1, par) = getMap x map side in
      (* Update required if x did not exist originally *)
      if (x <> par) then begin
        delete x oldlst;
        if side1 then insert par (fst blame)
        else insert par (snd blame)
      end
    end
    with Not_found ->
      print_endline ("Cache updating: could not find parent of " ^ exportF x);
      exit 1
  in
  (* We are iterating over blame only, so no need to check bIMPs *)
  let b2 = copySeq blame in (* Copy to avoid double updating *)
  for i=0 to numSets - 2 do
    FSet.iter (fun x -> doUpdate x (fst blame) lmap true) (fst b2).(i);
    FSet.iter (fun x -> doUpdate x (snd blame) rmap false) (snd b2).(i);
  done;;

  

(********** Proof strategy / Heuristics **********)
(** Choice of formula to prove first *)
let chooseF set =
  FSet.min_elt set;;

exception Found

(** Prioritise implications corresponding to modus ponens *)
let chooseImp s =
  let f = ref (chooseF (fst s).(i_IMP)) in
  if (FSet.is_empty (fst s).(i_AP)) then !f
  else begin
    (* Check if an instance of modus ponens is applicable *)
    try begin
    FSet.iter (fun x ->
        (* Check if left of implication exists in antecendent *)
        if (existsLeft !arrayDest1.(x) (fst s)) then begin
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
    | _, _ -> EQU (left, right) (* AND (IMP (left, right), IMP (right, left)) *)
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



(** Substitute occurrences of a particular subformula
    @param f Original formula (as an integer)
    @param sub Subformula to replace (as an integer)
    @param sign Replacement for sub (TRUE or FALSE)
    @param partial Indicate whether only partial substitution is allowed
    @return Formula after replacement (IntFormula tree)
 *)
let rec substitute f sub sign partial =
  assert (sign = TRUE || sign = FALSE);
  if (f = sub) then sign
  else begin
    (* If f has no subformulae, then it cannot be simplified *)
    if (!arrayDest1.(f) < 0) then !arrayFormula.(f)
    else begin
      let left = ref TRUE in
      let right = ref TRUE in
      (* If partial is set and sign is FALSE, only apply partial substitution.
         In particular, this means subformula of implications are unchanged *)
      if (partial &&
          sign = FALSE &&
          (!arrayType.(f) = 4 || !arrayType.(f) = 3)) then begin
        left := !arrayFormula.(!arrayDest1.(f));
        right := !arrayFormula.(!arrayDest2.(f))
      end
      else begin
        left := substitute !arrayDest1.(f) sub sign partial;
        right := substitute !arrayDest2.(f) sub sign partial
      end;
      match !arrayType.(f) with
        3 -> EQU (!left, !right)
      | 4 -> IMP (!left, !right)
      | 5 -> OR (!left, !right)
      | 6 -> AND (!left, !right)
      | _ -> invalid_arg "Substitute: unexpected formula type."
    end
  end;;

(** Apply simplification on a sequent
    @param s Original sequent
    @param f Formula to replace (integer representation)
    @param side Side of sequent from which f originated
    @param sign Replacement for f (TRUE or FALSE)
    @param lmap Map from formula to their parents, for caching
    @param rmap Map from formula to their parents, for caching
    @param keepCopy Determine if a copy of f should be maintained
    @param partial Indicate whether only partial substitution is allowed
 *)
let replace s f side sign lmap rmap keepCopy partial =
  let s_new = emptySeq () in
  (* Keep one copy of f *)
  if keepCopy then begin
    if side then begin
      if exists f (fst s) then begin
        insert f (fst s_new);
        delete f (fst s)
      end
    end
    else begin
      if exists f (snd s) then begin
        insert f (snd s_new);
        delete f (snd s)
      end
    end
  end;
  let replacement x side =
    (* Replace subformula and simplify *)
    let fml = ref (substitute x f sign partial) in
    fml := simplify !fml;
    begin
      match !fml with
        EQU (f1, f2) -> fml := AND (IMP (f1, f2), IMP (f2, f1))
      | _ -> ()
    end;
    let f_idx = findAdd !fml in
    if (side) then lmap := FMap.add f_idx (FMap.find x !lmap) !lmap
    else rmap := FMap.add f_idx (FMap.find x !rmap) !rmap;
    f_idx
  in
  (* Check for f and replace as necessary *)
  for i=0 to numSets - 2 do
    FSet.iter (fun x -> insert (replacement x true) (fst s_new)) (fst s).(i);
    FSet.iter (fun x -> insert (replacement x false) (snd s_new)) (snd s).(i);
  done;
  (* TODO: Compare benefits/detriments of considering bIMPs *) 
(*
  FSet.iter (fun x ->
      let newFml = replacement x true in
      if (x = newFml) then (fst s_new).(i_B) <- FSet.add x (fst s_new).(i_B)
      else insert newFml (fst s_new))
    (fst s).(i_B);
  (fst s).(i_B) <- (fst s_new).(i_B);
*)
  (* Replace original formula sets with new ones *)
  for i=0 to numSets - 2 do
    (fst s).(i) <- (fst s_new).(i);
    (snd s).(i) <- (snd s_new).(i)
  done;;

(** Function to iterate through formula and find polarity of atoms
    pos and neg are for T-permanence and ~T-permanence.
    wpos and wneg are for F-permanence.
    @param f Formula to scan (as integer)
    @param (w)pos BSet to store positive atoms in
    @param (w)neg BSet to store negative atoms in
    @param cur Current polarity (1 for true, -1 for false, 0 for both)
    @param wcur Current polarity (true or false for weak negative polarity)
 *)
let rec getPolarity f pos neg wpos wneg cur wcur =
  match !arrayType.(f) with
    0
  | 1 -> ()
  | 2 ->
      if wcur then setBS wneg f
      else setBS wpos f;
      (match cur with
        1 -> setBS pos f
      | 0 -> setBS pos f; setBS neg f
      | _ -> setBS neg f)
  (* EQU is an AND of two implications, which cancel out in polarity *)
  | 3 ->
      if wcur then begin
        getPolarity !arrayDest1.(f) pos neg wpos wneg 0 true;
        getPolarity !arrayDest2.(f) pos neg wpos wneg 0 true;
      end
      else begin
        getPolarity !arrayDest1.(f) pos neg wpos wneg 0 false;
        getPolarity !arrayDest2.(f) pos neg wpos wneg 0 false;
      end
  | 4 -> (* IMP *)
    let tmpPol = ref false in
    if wcur then tmpPol := true;
    (match cur with
      1 ->
      getPolarity !arrayDest1.(f) pos neg wpos wneg (-1) false;
      getPolarity !arrayDest2.(f) pos neg wpos wneg 1 !tmpPol
    | 0 ->
      getPolarity !arrayDest1.(f) pos neg wpos wneg 0 false;
      getPolarity !arrayDest2.(f) pos neg wpos wneg 0 !tmpPol
    | _ ->
      getPolarity !arrayDest1.(f) pos neg wpos wneg 1 false;
      getPolarity !arrayDest2.(f) pos neg wpos wneg (-1) !tmpPol)
  | 5
  | 6 -> 
      getPolarity !arrayDest1.(f) pos neg wpos wneg cur wcur;
      getPolarity !arrayDest2.(f) pos neg wpos wneg cur wcur
  | _ -> invalid_arg "getPolarity: unknown formula type";;


(** Apply permanence rules on all possible atoms.
    Utilises a bit string to indicate available atoms.
    @param bs Bit string representation of atoms
    See function "replace" for explanation of other parameters.
 *)
let doPerm bs s side sign lmap rmap keepCopy partial =
  (* iterate over words (integers) *)
  for w=0 to !atomsBS - 1 do
    let word = ref bs.(w) in
    if !word = 0 then ()
    else begin
      (* if word is not empty, iterate over bits *)
      for b=0 to bsintsize - 1 do
        let value = !word land 1 in
        word := !word lsr 1;
        if value > 0 then begin
          (* find corresponding atom, using w and b *)
          let atom = w * bsintsize + b in
          (* perform replacement *)
          replace s atom side sign lmap rmap keepCopy partial
        end
      done 
    end
  done;;


(** Simplification handler
    @param s Sequent to simplify
    @param f Formula to simplify
    @param side Side of sequent from which f originated
    @param sign Replacement for f (TRUE or FALSE)
    @params lmap rmap blame Requirements for caching
 *)
let doSimplify s f side sign lmap rmap blame =
  (* "Replace" rules: do nothing if simplification switch not set *)
  if (!sw_simp = false) then ()
  else begin
    let fml = !arrayFormula.(f) in
    match sign, fml with
    (* Apply Replace-~T if applicable *)
    | TRUE, IMP (_, FALSE) ->
        let f_first = normalise !arrayDest1.(f) in
        (* Corner case: add to blame if LHS already exists in antecedent *)
        if (!sw_cache && side && (exists f_first (fst s))) then begin
            let (f_side, f_par) = FMap.find f_first !lmap in
            if (f_side) then insert f_par (fst blame)
            else insert f_par (snd blame)
        end;
        if (side) then lmap := FMap.add f_first (FMap.find f !lmap) !lmap
        else rmap := FMap.add f_first (FMap.find f !rmap) !rmap;
        (* Apply simplification rule *)
        replace s f_first side FALSE lmap rmap false true;
        (* Keep a copy of ~T := T => False *)
        if (side) then insert f (fst s)
        else insert f (snd s)
    (* Otherwise, apply Replace-T or Replace-F *)
    | _ -> replace s f side sign lmap rmap true true
  end;
  (* "Permanence rules": do nothing if switch not set *)
  if (!sw_simpExt = false) then ()
  else begin
    (* Find all variables which occur only positively or negatively *)
    let pos = Array.make !atomsBS 0 in
    let neg = Array.make !atomsBS 0 in
    let wpos = Array.make !atomsBS 0 in
    let wneg = Array.make !atomsBS 0 in
    for i=0 to numSets - 2 do
      FSet.iter
          (fun x -> getPolarity x pos neg wpos wneg 1 true) (fst s).(i);
      FSet.iter
          (fun x -> getPolarity x pos neg wpos wneg (-1) false) (snd s).(i);
    done;
    FSet.iter (fun x -> getPolarity x pos neg wpos wneg 1 true) (fst s).(i_B);

    (* Check for an atom which only occurs positively *)
    let tSet = diffBS pos neg in
      doPerm tSet s true TRUE lmap rmap false false;
    (* Check negative atoms, note full substitution *)
    let fSet = diffBS neg pos in
      doPerm fSet s true FALSE lmap rmap false false;
    (* Weakly negative atoms for F-permanence, only partial substitution *)
    let wfSet = diffBS wpos wneg in
      doPerm wfSet s true FALSE lmap rmap false true;
  end;;



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
    inters := FSet.union !inters (FSet.inter (fst s).(i_B) (snd s).(i_IMP));
    (* If the intersection is not empty, then rule-id applies *)
    not (FSet.is_empty !inters)
  end;;

(** Axioms, for subset caching
    @param s Sequent to check for validity
    @param blame Formula required for a proof
    @param lmap Map from formula on left of sequent to parent
    @param rmap Map from formula on right of sequent to parent
    @return true if valid, false if not
 *)
let axioms_cache s blame lmap rmap =
  (* Check for FALSE and TRUE in left and right respectively *)
  if (FSet.mem !idx_F (fst s).(i_AP)) then begin
    let (side, parent) = getMap !idx_F lmap true in
    if (side) then insert parent (fst blame)
    else insert parent (snd blame);
    true
  end
  else if (FSet.mem !idx_T (snd s).(i_AP)) then begin
    let (side, parent) = getMap !idx_T rmap false in
    if (side) then insert parent (fst blame)
    else insert parent (snd blame);
    true
  end
  else begin
    let inters = ref (FSet.inter (fst s).(i_AP) (snd s).(i_AP)) in
    inters := FSet.union !inters (FSet.inter (fst s).(i_AND) (snd s).(i_AND));
    inters := FSet.union !inters (FSet.inter (fst s).(i_OR) (snd s).(i_OR));
    inters := FSet.union !inters (FSet.inter (fst s).(i_IMP) (snd s).(i_IMP));
    inters := FSet.union !inters (FSet.inter (fst s).(i_B) (snd s).(i_IMP));
    (* If the intersection is not empty, then rule-id applies *)
    if (not (FSet.is_empty !inters)) then begin
      (* Update for caching *)
      let f = FSet.choose !inters in
      let (side1, parent1) = getMap f lmap true in
      let (side2, parent2) = getMap f rmap false in
      if (side1) then
        insert parent1 (fst blame)
      else insert parent1 (snd blame);
      if (side2) then
        insert parent2 (fst blame)
      else insert parent2 (snd blame);
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
    @param lmap Map from left subformula to parents
    @param rmap Map from right subformula to parents
 *)
let and_left s f lmap rmap blame =
  match !arrayType.(f) with
  | 6 ->
c_land := succ !c_land;
    let f1 = normalise !arrayDest1.(f) in
    let f2 = normalise !arrayDest2.(f) in
    delete f (fst s);
    (* Optimisations *)
    updateMap f1 (getMap f lmap true) lmap s true;
    updateMap f2 (getMap f lmap true) lmap s true;
    (* Insert after updateMap to allow checking *)
    insert f1 (fst s);
    insert f2 (fst s);
    doSimplify s f1 true TRUE lmap rmap blame;
    doSimplify s f2 true TRUE lmap rmap blame;
  | _ -> invalid_arg "Rule application: invalid AND formula.";;

(** AND-right
    @param s Sequent on which the rule is to be applied
    @param f Formula to apply rule to
    @param lmap Map from left subformula to parents
    @param rmap Map from right subformula to parents
    @return New sequent resulting from rule branching
 *)
let and_right s f lmap rmap blame =
  match !arrayType.(f) with
  | 6 ->
c_rand := succ !c_rand;
    let f1 = normalise !arrayDest1.(f) in
    let f2 = normalise !arrayDest2.(f) in
    delete f (snd s);
    let s2 = copySeq s in
    updateMap f1 (getMap f rmap false) rmap s false;
    updateMap f2 (getMap f rmap false) rmap s2 false;
    insert f1 (snd s);
    insert f2 (snd s2);
    doSimplify s f1 false FALSE lmap rmap blame;
    doSimplify s2 f2 false FALSE lmap rmap blame;
    s2
  | _ -> invalid_arg "Rule application: invalid AND formula.";;

(** OR-left
    @param s Sequent on which the rule is to be applied
    @param f Formula to apply rule to
    @param lmap Map from left subformula to parents
    @param rmap Map from right subformula to parents
    @return New sequent resulting from rule application
 *)
let or_left s f lmap rmap blame =
  match !arrayType.(f) with
  | 5 ->
c_lor := succ !c_lor;
    let f1 = normalise !arrayDest1.(f) in
    let f2 = normalise !arrayDest2.(f) in
    delete f (fst s);
    let s2 = copySeq s in
    updateMap f1 (getMap f lmap true) lmap s true;
    updateMap f2 (getMap f lmap true) lmap s2 true;
    insert f1 (fst s);
    insert f2 (fst s2);
    doSimplify s f1 true TRUE lmap rmap blame;
    doSimplify s2 f2 true TRUE lmap rmap blame;
    s2
  | _ -> invalid_arg "Rule application: invalid OR formula.";;

(** OR-right
    @param s Sequent on which the rule is to be applied
    @param f Formula to apply rule to
    @param lmap Map from left subformula to parents
    @param rmap Map from right subformula to parents
 *)
let or_right s f lmap rmap blame =
  match !arrayType.(f) with
  | 5 ->
c_ror := succ !c_ror;
    let f1 = normalise !arrayDest1.(f) in
    let f2 = normalise !arrayDest2.(f) in
    delete f (snd s);
    updateMap f1 (getMap f rmap false) rmap s false;
    updateMap f2 (getMap f rmap false) rmap s false;
    insert f1 (snd s);
    insert f2 (snd s);
    doSimplify s f1 false FALSE lmap rmap blame;
    doSimplify s f2 false FALSE lmap rmap blame
  | _ -> invalid_arg "Rule application: invalid OR formula.";;

(** IMP-left
    @param s Sequent on which the rule is to be applied
    @param f Formula to apply rule to
    @param lmap Map from left subformula to parents
    @param rmap Map from right subformula to parents
    @return New sequent resulting from rule application
 *)
let imp_left s f lmap rmap blame =
  match !arrayType.(f) with
  | 4 ->
c_limp := succ !c_limp;
    let f1 = normalise !arrayDest1.(f) in
    let f2 = normalise !arrayDest2.(f) in
    delete f (fst s);
    let s2 = copySeq s in
    (* add copy of implication to left's blocked list *)
    (fst s).(i_B) <- FSet.add f (fst s).(i_B);
    updateMap f1 (getMap f lmap true) rmap s false;
    updateMap f2 (getMap f lmap true) lmap s2 true;
    insert f1 (snd s);
    insert f2 (fst s2);
    doSimplify s f1 false FALSE lmap rmap blame;
    doSimplify s2 f2 true TRUE lmap rmap blame;
    s2
  | _ -> invalid_arg "Rule application: invalid l-IMP formula.";;

(** IMP-right-first
    @param s Sequent on which the rule is to be applied
    @param f Chosen right IMP formula
    @param lmap Map from left subformula to parents
    @param rmap Map from right subformula to parents
 *)
let imp_first s f lmap rmap blame =
  match !arrayType.(f) with
  | 4 ->
c_rimp := succ !c_rimp;
    let f1 = normalise !arrayDest1.(f) in
    let f2 = normalise !arrayDest2.(f) in
    (* delete atoms and implications in the right array *)
    (snd s).(i_AP) <- FSet.empty;
    (snd s).(i_IMP) <- FSet.empty;
    (* unblock all of left's blocked implications *)
    (fst s).(i_IMP) <- (fst s).(i_B);
    (fst s).(i_B) <- FSet.empty;
    (* add copy of implication to right's right-first list *)
    (snd s).(i_R) <- FSet.add f (snd s).(i_R);
    (* apply changes due to implication itself *)
    updateMap f1 (getMap f rmap false) lmap s true;
    updateMap f2 (getMap f rmap false) rmap s false;
    insert f1 (fst s);
    insert f2 (snd s)
    (*
    doSimplify s f2 false FALSE lmap rmap blame;
    doSimplify s f1 true TRUE lmap rmap blame
    *)
  | _ -> invalid_arg "Rule application: invalid first-IMP formula.";;
  
(** IMP-right-rest
    @param s Sequent on which the rule is to be applied
    @param f Chosen right IMP formula
    @param lmap Map from left subformula to parents
    @param rmap Map from right subformula to parents
    @return New sequent after rule application
 *)
let imp_rest s f lmap rmap blame =
  match !arrayType.(f) with
  | 4 ->
    let f2 = normalise !arrayDest2.(f) in
    delete f (snd s);
    updateMap f2 (getMap f rmap false) rmap s false;
    insert f2 (snd s);
    doSimplify s f2 false FALSE lmap rmap blame
  | _ -> invalid_arg "Rule application: invalid rest-IMP formula.";;


(** Apply all possible non-branching rules to a Sequent *)
let rec no_branch s lmap rmap blame =
  try begin
    top_bot s;
    (* AND-left *)
    while (not (FSet.is_empty (fst s).(i_AND))) do
      and_left s (chooseF (fst s).(i_AND)) lmap rmap blame
    done;
    (* OR-right *)
    while (not (FSet.is_empty (snd s).(i_OR))) do
      or_right s (chooseF (snd s).(i_OR)) lmap rmap blame
    done;
    (* IMP-right-rest *)
    let set = ref (FSet.inter (snd s).(i_IMP) (snd s).(i_R)) in
    while (not (FSet.is_empty !set)) do
      let f = chooseF !set in
      imp_rest s f lmap rmap blame;
      set := FSet.remove f !set
    done;
    (* Check if we have created any more non-branching formulae *)
    if (FSet.is_empty (fst s).(i_AND)
          && FSet.is_empty (snd s).(i_OR)
            && FSet.is_empty (FSet.inter (snd s).(i_IMP) (snd s).(i_R)))
    then ()
    else no_branch s lmap rmap blame
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
  let lmap = ref FMap.empty in
  let rmap = ref FMap.empty in

  (* Apply non-branching rules *)
  no_branch s lmap rmap blame;

  (* Check axioms *)
  if (axioms_cache s blame lmap rmap) then true
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
        mergeCachehit blame !hit lmap rmap;
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

    (* Not in cache, perform branching rules *)
    let branch = ref s in
    let pbranches () =
      (* Prove branches *)
      if (mainl s blame) then begin
        (* If first branch is true, setup new blame for second *)
        let blame2 = emptySeq () in
        (* For backjumping, check if blame is a subset of branch *)
        if (!sw_bjump) then begin
          let base = copySeq !branch in
          (fst base).(i_IMP) <- FSet.union (fst base).(i_IMP) (fst base).(i_B);
          if (subSeq blame base) then begin
            c_bjump := succ !c_bjump;
            (* update cache, using lmap and rmap *)
            updateBlame lmap rmap blame;
            if (!sw_cachemore) then
                trueSeq := Cache.add (convertSeq blame) !trueSeq;
            true
          end
          (* If backjumping doesn't apply, process branch *)
          else if (mainl !branch blame2) then begin
            updateBlame lmap rmap blame;
            mergeBlame blame blame2 lmap rmap;
            true
          end else false
        end
        (* bjump not set *)
        else begin
          if (mainl !branch blame2) then begin
            updateBlame lmap rmap blame;
            mergeBlame blame blame2 lmap rmap;
            true
          end else false
        end
      end
      (* could not prove first branch *)
      else false
    in (* pbranches *)

    (* Try to pick a formula which where one branch closes *)
    let bf = ref (-1) in
    let ba = ref (-1) in
    if (!sw_hmatch && atomMatch s bf ba) then begin
      assert (exists !bf (fst s) || exists !bf (snd s));
      begin match !arrayType.(!bf) with
        6 -> branch := and_right s !bf lmap rmap blame;
      | 5 -> branch := or_left s !bf lmap rmap blame;
      | 4 -> branch := imp_left s !bf lmap rmap blame;
      | _ -> invalid_arg "mainl: incorrect branching formula chosen"
      end;
      (* Reverse depth-first choice if necessary to following matching atom *)
      swapAtomBranches s branch bf ba;
      pbranches ()
    end else begin
    (* Try subformula matching on n-ary operators (AND and OR) *)
    let swap = ref false in
    if (!sw_hmatch &&
        (subfmlMatch (fst s).(i_OR) (snd s).(i_AP) bf swap ||
        subfmlMatch (snd s).(i_OR) (fst s).(i_AP) bf swap)) then begin
      assert (exists !bf (fst s) || exists !bf (snd s));
      begin match !arrayType.(!bf) with
        6 -> branch := and_right s !bf lmap rmap blame;
      | 5 -> branch := or_left s !bf lmap rmap blame;
      | _ -> invalid_arg "mainl: incorrect branching formula chosen"
      end;
      if !swap then swapBranches s branch;
      pbranches ()

    (* If heuristics don't apply, saturate as usual *)
    end else begin
      (* AND-right *)
      if (not (FSet.is_empty (snd s).(i_AND))) then begin
        let f = chooseF (snd s).(i_AND) in
        branch := and_right s f lmap rmap blame;
        pbranches ()
      end else begin
        (* OR-left *)
        if (not (FSet.is_empty (fst s).(i_OR))) then begin
          let f = chooseF (fst s).(i_OR) in
          branch := or_left s f lmap rmap blame;
          pbranches ()
        end else begin
          (* IMP-left *)
          if (not (FSet.is_empty (fst s).(i_IMP))) then begin
            let f = chooseImp s in
            branch := imp_left s f lmap rmap blame;
            pbranches ()
          end
          (* If we reach this point, the sequent is saturated *)
          else choose s blame lmap rmap
        end
      end
    end
    end
  end
  with Not_found -> begin
    print_endline "Mainl: unexpected operation (empty set or find)";
    exit 1
  end

(** Choose a right implication formula.
    lmap and rmap must be passed, as we have not branched yet.
 *)
and choose s blame lmap rmap =
  if (not (FSet.is_empty (snd s).(i_IMP))) then begin
    (* This implication has not been seen before, apply right-first *)
    let f = chooseF (snd s).(i_IMP) in
    (* Copy sequent and apply imp-right-first *)
    let newSeq = copySeq s in
    let lmap2 = ref (FMap.map (fun x -> x) !lmap) in
    let rmap2 = ref (FMap.map (fun x -> x) !rmap) in
    (* usedFormula will be updated with all formula used in a proof *)
    let usedFormula = emptySeq () in
    imp_first newSeq f lmap2 rmap2 usedFormula;
    (* Keep a copy of sequent after imp_first application, for caching *)
    let cache_copy = copySeq newSeq in
    doCache := true;
    (* Recurse *)
    if mainl newSeq usedFormula then begin
      (* Tell parent what formula are important for a proof *)
      mergeBlame blame usedFormula lmap2 rmap2;
      if (!sw_cache) then begin
        (* Add key formula from this point on to cache *)
        trueSeq := Cache.add (convertSeq blame) !trueSeq;
      end;
      true
    end
    else begin
      (* If false, update cache then choose another formula *)
      if (!sw_cache) then begin
        falseSeq := Cache.add (convertSeq cache_copy) !falseSeq;
      end;
      (snd s).(i_IMP) <- FSet.remove f (snd s).(i_IMP);
      choose s blame lmap rmap
    end
  end
  (* Empty set: no remaining applicable rules, return *)
  else begin
    if (!sw_cache) then falseSeq := Cache.add (convertSeq s) !falseSeq;
    false
  end;;


(** Method to call to run a sequent proof
    @param s Sequent to prove
 *)
let prove s = mainl s (emptySeq ());;
