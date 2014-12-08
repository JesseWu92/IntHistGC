let atom i = "p" ^ (string_of_int i)

let dest = Array.make 100 0

let _ =
  if (Array.length Sys.argv < 2) then begin
    print_endline "Usage: ./impure n";
    exit 1;
  end;
  let n = int_of_string Sys.argv.(1) in

  assert (n <= 100);

  for i = 1 to n-1 do
    print_string ("(" ^ (atom i) ^ " => " ^ atom i ^ ") & ");
  done;

  print_string ("(" ^ (atom n) ^ " => " ^ atom n ^ ")");

  print_newline ()
