(** Sequent application with model printing.
    See Sequent.ml for further implementation details.
    @author Jesse Wu, u5009927@anu.edu.au

 *)

open Sequent
open MiscSolver

(* Counters *)
let world = ref 0
let maxdepth = ref 0
let c_cache = ref 0
let c_bjump = ref 0

(* Graphviz edge printing enums *)
let edge_OR = 0
let edge_AND = 1
let edge_LIMP = 2
let edge_RIMP = 3

(* Caching *)
module C = Map.Make (struct type t = sequent let compare = compare end)
let tCache = ref C.empty
let fCache = ref C.empty
let lastHit = ref (emptySeq ())

(* Cache checking, and cache hit printing *)
let check key bind s w oc =
  if subSeq key s then begin
    lastHit := key;
    output_string oc (string_of_int w ^ "[xlabel=");
    output_string oc (string_of_int bind ^ "]\n");
    true
  end
  else false;;

(* Find if a sequent is in the cache *)
let findSeq s cache cType w oc =
  let base = copySeq s in
  (fst base).(i_IMP) <- FSet.union (fst base).(i_B) (fst base).(i_IMP);
  let return = ref false in
  if cType then
    C.iter (fun key bind ->
        return := !return || (check key bind base w oc)) cache
  else
    C.iter (fun key bind ->
        return := !return || (check base bind key w oc)) cache;
  !return;;


(* Printing utilities *)
(* Buffers offer faster concatenation than the '^' operator *)
let set_to_buf set =
  let b = Buffer.create (FSet.cardinal set) in
  FSet.iter (fun x -> Buffer.add_string b (IntMisc.exportF x ^ ", ")) set;
  b;;

let output_seq s oc =
  Array.iter (fun x -> Buffer.output_buffer oc (set_to_buf x)) (fst s);
  output_string oc "&#10;::=&#10;";
  for i = 0 to numSets - 2 do
    Buffer.output_buffer oc (set_to_buf (snd s).(i))
  done;;

let print_node w s oc =
  output_string oc (string_of_int w);
  output_string oc (" [label=<w" ^ (string_of_int w) ^ ">, ");
  output_string oc "tooltip=\"";
  output_seq s oc;
  output_string oc ("\"]\n");;

let print_edge w1 w2 etype oc =
  output_string oc (string_of_int w1);
  output_string oc " -> ";
  output_string oc (string_of_int w2);
  match etype with
  | 0 -> output_string oc " [style=dotted]\n";
  | 1 -> output_string oc " [style=dashed]\n";
  | 2 -> output_string oc " [color=black]\n";
  | 3 -> output_string oc " [color=blue]\n";
  | _ -> output_string oc "\n";;

let print_false w oc =
  output_string oc (string_of_int w ^ " [color=\"red\"]\n");;

let print_cache w key cache oc =
  try begin
    let cacheW = C.find key !cache in
    output_string oc (string_of_int w ^ "[xlabel=");
    output_string oc (string_of_int cacheW ^ "]\n");
  end
  with Not_found -> ();;


(** Main loop
    1. Saturate: Apply all rules except IMP-right-first and IMP-right-rest
      a. Apply non-branching rules and check for validity
      b. Apply branching rules
    2. Choose a right implication
      a. If none, then return not valid
    3. If right-first has not been applied to this formula
      a. Jump then apply the right first rule
      b. Don't jump and apply the right rest rule
    Go to 1.

    @param s Sequent to prove
    @param w World number (for printing)
    @param d Current depth (right-imp jumps)
    @param blame Formula required for a proof
    @param oc Output channel
    @param p Enable or suppres node printing
 *)
let rec mainl s w d blame oc p =
  (* Create local maps to track origins of formula *)
  let lmap = ref FMap.empty in
  let rmap = ref FMap.empty in

  (* Apply non-branching rules *)
  no_branch s lmap rmap blame;
  if p then print_node w s oc;
  maxdepth := max !maxdepth d;
  (* Check axioms *)
  if (axioms_cache s blame lmap rmap) then true
  else
  (* Check cache *)
  if findSeq s !tCache true w oc then begin
    mergeBlame blame !lastHit lmap rmap;
    c_cache := succ !c_cache;
    true
  end
  else begin
    if findSeq s !fCache false w oc then begin
      print_false w oc;
      c_cache := succ !c_cache;
      false
    end
    (* Not in cache, perform branching rules *)
    else try begin
      let branch = ref s in
      let pbranches etype =
        let w1 = !world + 1 in
        let w2 = !world + 2 in
        world := !world + 2;
        print_edge w w1 etype oc;
        print_edge w w2 etype oc;

        (* Prove branches *)
        if (mainl s w1 d blame oc true) then begin
          let blame2 = emptySeq () in
          (* For backjumping, check if blame is a subset of branch *)
          if (!sw_bjump) then begin
            let base = copySeq !branch in
            (fst base).(i_IMP) <- FSet.union (fst base).(i_IMP) (fst base).(i_B);
            if (subSeq blame base) then begin
              output_string oc (string_of_int w ^ "[xlabel=bjump]");
              c_bjump := succ !c_bjump;
              updateBlame lmap rmap blame;
              if (!sw_cachemore) then
                  tCache := C.add blame w !tCache;
              true
            end
            (* If backjumping doesn't apply, process branch *)
            else if (mainl !branch w2 d blame2 oc true) then begin
              (* update cache, using lmap and rmap *)
              updateBlame lmap rmap blame;
              mergeBlame blame blame2 lmap rmap;
              true
            end
            else begin print_false w oc; false end
          end
          (* bjump not set *)
          else begin
            if (mainl !branch w2 d blame2 oc true) then begin
              updateBlame lmap rmap blame;
              mergeBlame blame blame2 lmap rmap;
              true
            end
            else begin print_false w oc; false end
          end
        end
        (* could not prove first branch *)
        else begin print_false w oc; false end
      in

      (* Try to pick a formula which where one branch closes *)
      let bf = ref (-1) in
      let ba = ref (-1) in
      if (!sw_hmatch && atomMatch s bf ba) then begin
        assert (exists !bf (fst s) || exists !bf (snd s));
        let btype = ref 0 in
        begin match !arrayType.(!bf) with
          6 -> branch := and_right s !bf lmap rmap blame; btype := edge_AND
        | 5 -> branch := or_left s !bf lmap rmap blame; btype := edge_OR
        | 4 -> branch := imp_left s !bf lmap rmap blame; btype := edge_LIMP
        | _ -> invalid_arg "mainl: incorrect branching formula chosen"
        end;
        (* Reverse depth-first choice if necessary to following matching atom *)
        swapAtomBranches s branch bf ba;
        pbranches !btype
      end else begin
      (* Try subformula matching on n-ary operators (AND and OR) *)
      let swap = ref false in
      if (!sw_hmatch && 
          (subfmlMatch (fst s).(i_OR) (snd s).(i_AP) bf swap ||
          subfmlMatch (snd s).(i_OR) (fst s).(i_AP) bf swap)) then begin
        assert (exists !bf (fst s) || exists !bf (snd s));
        let btype = ref 0 in
        begin match !arrayType.(!bf) with
          6 -> branch := and_right s !bf lmap rmap blame; btype := edge_AND
        | 5 -> branch := or_left s !bf lmap rmap blame; btype := edge_OR
        | _ -> invalid_arg "mainl: incorrect branching formula chosen"
        end;
        if !swap then swapBranches s branch;
        pbranches !btype

      (* If heuristics didn't apply, saturate as usual *)
      end else begin
        (* AND-right *)
        if (not (FSet.is_empty (snd s).(i_AND))) then begin
          let f = chooseF (snd s).(i_AND) in
          branch := and_right s f lmap rmap blame;
          pbranches edge_AND
        end
        else begin
          (* OR-left *)
          if (not (FSet.is_empty (fst s).(i_OR))) then begin
            let f = chooseF (fst s).(i_OR) in
            branch := or_left s f lmap rmap blame;
            pbranches edge_OR
          end
          else begin
            (* IMP-left *)
            if (not (FSet.is_empty (fst s).(i_IMP))) then begin
              let f = chooseImp s in
              branch := imp_left s f lmap rmap blame;
              pbranches edge_LIMP
            end
            (* If we reach this point, the sequent is saturated *)
            else choose s w d blame lmap rmap oc
          end
        end
      end
      end
    end
    with Not_found -> print_endline "Error: unexpected operation on empty set.";
    exit 1
  end

(* Choose a right implication formula *)
and choose s w d blame lmap rmap oc =
  if (not (FSet.is_empty (snd s).(i_IMP))) then begin
    (* This implication has not been seen before, use right-first *)
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
    (* Modelling *)
    world := !world + 1;
    print_edge w !world edge_RIMP oc;
    (* Only one right imp needs to be true *)
    if mainl newSeq !world (d+1) usedFormula oc true then begin
      updateBlame lmap2 rmap2 usedFormula;
      (* Tell parent what formula are important for a proof *)
      mergeBlame blame usedFormula lmap2 rmap2;
      if (!sw_cache) then begin
        (* Add key formula from this point on to cache *)
        tCache := C.add blame w !tCache;
      end;
      true
    end
    else begin
      (* If false, update cache then choose another formula *)
      if (!sw_cache) then begin
        fCache := C.add cache_copy w !fCache;
      end;
      (snd s).(i_IMP) <- FSet.remove f (snd s).(i_IMP);
      choose s w d blame lmap rmap oc
    end
  end
  (* Empty set: no remaining applicable rules, return *)
  else begin
    print_false w oc;
    if (!sw_cache) then fCache := C.add s w !fCache;
    false
  end;;

(** Method to call to run a sequent proof
    @param s Sequent to prove
    @param oc Output channel for model printing
  *)
let prove s oc = mainl s 0 0 (emptySeq ()) oc true;;
