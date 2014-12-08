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
  output_string oc "Lookahead: ";
  Buffer.output_buffer oc (set_to_buf (fst s).(i_L));
  output_string oc "&#10;Sequent:&#10;";
  for i = 0 to numSets - 2 do
    Buffer.output_buffer oc (set_to_buf (fst s).(i))
  done;
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
  | 0 -> output_string oc " [color=black,style=dotted]\n";
  | 1 -> output_string oc " [color=black]\n";
  | 2 -> output_string oc " [color=blue,style=dashed]\n";
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
    @param p Enable or suppress node printing
 *)
let rec mainl s w d blame oc p =
  (* Create local maps to track origins of formula *)
  let gmap = ref FMap.empty in
  let dmap = ref FMap.empty in

  (* Apply non-branching rules *)
  no_branch s gmap dmap blame;
  if p then print_node w s oc;
  maxdepth := max !maxdepth d;
    (* Check axioms *)
  if (axioms_cache s blame !gmap !dmap) then true
  else
  (* Check cache *)
  if findSeq s !tCache true w oc then begin
    mergeBlame blame !lastHit FMap.empty !gmap !dmap;
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
        (* TODO: backjumping *)
        let w1 = !world + 1 in
        let w2 = !world + 2 in
        world := !world + 2;
        print_edge w w1 etype oc;
        print_edge w w2 etype oc;
        (* Prove branches *)
        if (mainl s w1 d blame oc true) then begin
          (* If first branch is true, setup new blame for second *)
          let blame2 = emptySeq () in
          if (mainl !branch w2 d blame oc true) then begin
            updateBlame FMap.empty !gmap !dmap blame;
            mergeBlame blame blame2 FMap.empty !gmap !dmap;
            true
          end else begin print_false w oc; false end
        end
        (* could not prove first branch *)
        else begin print_false w oc; false end
      in

      (* Saturate *)
      begin
        (* AND-right *)
        if (not (FSet.is_empty (snd s).(i_AND))) then begin
          let f = chooseF (snd s).(i_AND) in
          branch := and_right s f gmap dmap blame;
          pbranches edge_AND
        end else begin
          (* OR-left *)
          if (not (FSet.is_empty (fst s).(i_OR))) then begin
            let f = chooseF (fst s).(i_OR) in
            branch := or_left s f gmap dmap blame;
            pbranches edge_OR
          end else
            (* If we reach this point, the sequent is saturated *)
            choose s w d blame gmap dmap oc
        end
      end
    end
      with Not_found -> print_endline "Error: unexpected operation on empty set.";
      exit 1
  end

(* Choose a right implication formula *)
and choose s w d blame gmap dmap oc =
  let premises = ref [] in
  (* Keep copy of premises for invalid caching *)
  let premCopy = ref (emptySeq ()) in
  let cWorld = ref 0 in
  try begin
    (* try left implications *)
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

        (* Recurse on premises *)
        (* Premise 1 *)
        let newBlame1 = emptySeq () in
        premCopy := copySeq (List.hd !premises);
        world := !world + 1; cWorld := !world;
        print_edge w !world edge_LIMP oc;
        if (mainl (List.hd !premises) !world (d+1) newBlame1 oc true) then begin
          if (!sw_cache) then tCache := C.add newBlame1 !cWorld !tCache;
        end else raise Invalid;
        (* Premise 2 *)
        let newBlame2 = emptySeq () in
        premCopy := copySeq (List.nth !premises 1);
        world := !world + 1; cWorld := !world;
        print_edge w !world edge_LIMP oc;
        if (mainl (List.nth !premises 1) !world (d+1) newBlame2 oc true) then begin
          if (!sw_cache) then tCache := C.add newBlame2 !cWorld !tCache;
        end else raise Invalid;
        (* Premise 3 *)
        let newBlame3 = emptySeq () in
        premCopy := copySeq (List.nth !premises 2);
        world := !world + 1; cWorld := !world;
        print_edge w !world edge_LIMP oc;
        if (mainl (List.nth !premises 2) !world (d+1) newBlame3 oc true) then begin
          (* Merge all blames *)
          mergeBlame blame newBlame1 !(smap.lmap) !(smap.gmap) !(smap.dmap);
          mergeBlame blame newBlame2 !(smap.lmap) !(smap.gmap) !(smap.dmap);
          mergeBlame blame newBlame3 !(smap3.lmap) !(smap3.gmap) !(smap3.dmap);
          if (!sw_cache) then begin
            tCache := C.add newBlame3 !cWorld !tCache;
            tCache := C.add blame w !tCache
          end;
          raise Valid
        end else begin
          (* Do not raise Invalid. Cache, then move to next implication *)
          if (!sw_cache) then fCache := C.add !premCopy w !fCache;
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
        world := !world + 1; cWorld := !world;
        print_edge w !world edge_RIMP oc;
        if (mainl (List.hd !premises) !world (d+1) newBlame1 oc true) then begin
          if (!sw_cache) then tCache := C.add newBlame1 !cWorld !tCache;
        end else raise Invalid;
        (* Premise 2: non-invertible *)
        let newBlame2 = emptySeq () in
        premCopy := copySeq (List.nth !premises 1);
        world := !world + 1; cWorld := !world;
        print_edge w !world edge_RIMP oc;
        if (mainl (List.nth !premises 1) !world (d+1) newBlame2 oc true) then begin
          (* Merge all blames *)
          mergeBlame blame newBlame1 !(smap.lmap) !(smap.gmap) !(smap.dmap);
          mergeBlame blame newBlame2 !(smap2.lmap) !(smap2.gmap) !(smap2.dmap);
          if (!sw_cache) then begin
            tCache := C.add newBlame2 !cWorld !tCache;
            tCache := C.add blame w !tCache
          end;
          raise Valid
        end else begin
          (* Do not raise Invalid. Cache, then move to next implication *)
          if (!sw_cache) then fCache := C.add !premCopy w !fCache;
        end;
      ) (snd s).(i_IMP);
    (* No remaining applicable rules, add to invalid cache *)
    if (!sw_cache) then fCache := C.add s w !fCache;
    print_false w oc;
    false;
  end
  with Valid -> true
    | Invalid -> 
        if (!sw_cache) then fCache := C.add !premCopy !cWorld !fCache;
        print_false w oc;
        false;;

(** Method to call to run a sequent proof
    @param s Sequent to prove
    @param oc Output channel for model printing
  *)
let prove s oc = mainl s 0 0 (emptySeq ()) oc true;;
