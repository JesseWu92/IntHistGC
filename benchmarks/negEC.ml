let atom n = "p" ^ (string_of_int n)
let neg n = "~p" ^ (string_of_int n)

let _ =
  if (Array.length Sys.argv < 2) then begin
    print_endline "Usage: ./EC n";
    exit 1;
  end;
  let n = int_of_string Sys.argv.(1) in

  print_endline "(";
  for i=1 to n-1 do
    print_endline ("~(" ^ atom i ^ " & " ^ atom (i + 1) ^ ") &")
  done;
  print_endline ("~(" ^ atom n ^ " & " ^ atom 1 ^ ")");

  print_endline ") => (";

  for i=1 to n-1 do
    print_endline (neg i ^
        " | " ^ neg (i + 1) ^
        " | (" ^ neg i ^ " | " ^ neg (i+1) ^ ") |")
  done;
    print_endline (neg n ^
        " | " ^ neg 1 ^
        " | (" ^ neg n ^ " | " ^ neg 1 ^ ") )")

