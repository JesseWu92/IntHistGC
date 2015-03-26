(** Sequent based theorem prover for propositional intuitionistic logic
    @author Jesse Wu, u5009927@anu.edu.au
 *)

open IntFormula
module Sq = Sequent
module M = Model

(* Flags determining whether a model or statistics will be printed *)
let mflag = ref false
let pflag = ref false
let file = ref ""

(* Model interpretation *)
let model_usage oc file =
  let bname = Filename.basename file in
  output_string oc "/*\n";
  output_string oc "Generate visual of model using Graphviz:\n";
  output_string oc ("\tdot -Tsvg -o " ^ bname ^ ".svg " ^ bname ^ ".gv\n");
  output_string oc ("The resulting svg can be viewed using most modern browsers.");
  output_string oc " Note that Graphviz version 2.29 or newer is required to produce xlabels (to indicate backjumping and caching hits).\n\n";
  output_string oc "Hover over nodes to see corresponding sequent.\n";
  output_string oc "Sequents are shown as:\n\tGamma\n\t::=\n\tDelta\n";
  output_string oc "Nodes without \"w\" indicate branches not required to be expanded during search.\n";
  output_string oc "External labels \"x\" indicate a sequent has been previously proven (at node \"x\").\n";
  output_string oc "Provable sequents will be supersets of \"x\".\nUnprovable sequents will be subsets of \"x\".\n";
  output_string oc "\nLegend:\n";
  output_string oc "Red nodes indicate worlds which are not true.\n";
  output_string oc "Dotted edges indicate branching to (left) OR rules.\n";
  output_string oc "Dashed edges indicate branching to (right) AND rules.\n";
  output_string oc "Solid black edges indidate branching due to left-IMP rules.\n";
  output_string oc "Solid blue edges indicate jumps to due to right-IMP rules.\n";
  output_string oc "*/\n\n";;

(* Main: parse file and check for validity *)
let main =
  (* Options *)
  let opts = Arg.align [
    ("-m",
      Arg.Unit (fun () -> mflag := true),
      " Output derivation graph in formula.gv");
    ("-p",
      Arg.Unit (fun () -> pflag := true),
      " Print statistics");
    ("-none",
      Arg.Unit (fun () ->
          Sq.sw_bjump := false;
          Sq.sw_cache := false;
          Sq.sw_cachemore := false;
          Sq.sw_cache3 := false),
      " Do not apply any optimisations (default configuration)");
    ("-b",
      Arg.Unit (fun () -> Sq.sw_bjump := true),
      " Apply backjumping");
    ("-c",
      Arg.Unit (fun () -> Sq.sw_cache := true),
      " Cache at right-imp jumps");
    ("-c2",
      Arg.Unit (fun () -> Sq.sw_cachemore := true),
      " Cache at backjumping points");
    ("-c3",
      Arg.Unit (fun () -> Sq.sw_cache3 := true),
      " Attempt cache lookups only every second node");
    ("-hm",
      Arg.Unit (fun () -> Sq.sw_hmatch := true),
      " Heuristic to prioritise rules which may result in (atom) clashes");
    ] in
  (* Read options, non-switch argument is interpreted as input file *)
  Arg.parse opts (fun x -> file := x) "Usage: ./prover [options] formula.txt";
  if (Array.length Sys.argv < 2 || !file = "") then
    begin
    print_endline "Usage: ./prover [options] formula.txt";
    print_endline "To display options: ./prover -help";
    exit 1
    end
  else begin
    (* Open file *)
    let chan = open_in !file in
    let fml = ref (importFormula_ic chan) in
    close_in chan;

    (* Pre-processing *)
    fml := Sq.rewriteImps !fml;
    fml := Sq.simplify !fml;
    fml := prep !fml;
    (* Print formula *)
(*
    print_string "Processed formula: ";
    print_endline (exportFormula !fml);
*)

    (* Apply sequent rules *)
    let seq = Sq.init !fml in
    if (!mflag) then begin
      (* Get base name of input file *)
      let basename = Filename.chop_extension !file in
      let oc = open_out (basename ^ ".gv") in
      model_usage oc basename;
      output_string oc "digraph \"";
      output_string oc (Filename.basename basename);
      output_string oc "\" {\n";
      output_string oc "node [shape=circle]\n";

      (* Prove *)
      if (M.prove seq oc) then print_endline "valid."
      else print_endline "not valid.";

      output_string oc "}";
      close_out oc;
      print_endline ("See \"" ^ basename ^ ".gv\" for instructions on generating and interpreting derivation graph.");

      if !pflag then begin
      print_string "Processed formula: ";
      print_endline (exportFormula !fml);
      print_endline ("Nodes: " ^ (string_of_int !M.world));
      print_endline ("Max depth: " ^ (string_of_int !M.maxdepth));
      print_endline ("left AND rules: " ^ (string_of_int !Sq.c_land));
      print_endline ("right AND branches: " ^ (string_of_int !Sq.c_rand));
      print_endline ("left OR rules: " ^ (string_of_int !Sq.c_lor));
      print_endline ("right OR branches: " ^ (string_of_int !Sq.c_ror));
      print_endline ("left IMP branches: " ^ (string_of_int !Sq.c_limp));
      print_endline ("right IMP jumps: " ^ (string_of_int !Sq.c_rimp));
      print_endline ("Cache hits: " ^ (string_of_int !M.c_cache));
      print_endline ("Backjump hits: " ^ (string_of_int !M.c_bjump));
      end;
    end
    else begin
      (* Prove without printing model *)
      if (Sq.prove seq) then print_endline "valid."
      else print_endline "not valid.";
      if !pflag then begin
        print_endline ("Nodes: " ^ (string_of_int !Sq.nodes));
        print_endline ("left AND rules: " ^ (string_of_int !Sq.c_land));
        print_endline ("right AND branches: " ^ (string_of_int !Sq.c_rand));
        print_endline ("left OR rules: " ^ (string_of_int !Sq.c_lor));
        print_endline ("right OR branches: " ^ (string_of_int !Sq.c_ror));
        print_endline ("left IMP branches: " ^ (string_of_int !Sq.c_limp));
        print_endline ("right IMP jumps: " ^ (string_of_int !Sq.c_rimp));
        print_endline ("Cache hits: " ^ (string_of_int !Sq.c_cache));
        print_endline ("Backjump hits: " ^ (string_of_int !Sq.c_bjump));
        print_endline ("Valid cache size: " ^
            string_of_int (Cache.size !Sq.trueSeq));
        print_endline ("Invalid cache size: " ^
            string_of_int (Cache.size !Sq.falseSeq))
      end
    end
  end;;
