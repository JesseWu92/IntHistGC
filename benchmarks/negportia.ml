(* c_n => portrait is in casket i *)
let cask n = "c" ^ (string_of_int n)

(* i_n => inscription n is true *)
let ins n = "i" ^ (string_of_int n)

let _ =
  if (Array.length Sys.argv < 2) then begin
    print_endline "Usage: ./portia n";
    exit 1;
  end;
  let n = int_of_string Sys.argv.(1) in
  print_endline "(";
  (* Caskets *)
  print_string "(";
  for i=1 to n do
    print_string "(";
    for j=1 to n do
      if (j = i) then print_string (cask j)
      else print_string ("~" ^ cask j);
      if not (j = n) then print_string " & "
    done;
    print_string ")";
    if not (i = n) then print_string " | "
    else print_endline ")"
  done;
  (* Normal inscriptions *)
  for i=1 to n-1 do
    print_endline ("& (" ^ ins i ^ " <=> " ^ cask i ^ ")")
  done;
  (* Final inscription *)
  print_string ("& (" ^ ins n ^ " <=> (");
  for i=1 to n do
    print_string "(";
    for j=1 to n do
      if (j = i) then print_string (ins j)
      else print_string ("~" ^ ins j);
      if not (j = n) then print_string " & "
    done;
    print_string ")";
    if not (i = n) then print_string " | "
    else print_endline "))"
  done;
  print_endline (") => " ^ cask 1)


