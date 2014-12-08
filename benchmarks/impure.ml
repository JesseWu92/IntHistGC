let atom i = "p" ^ (string_of_int i)

let dest = Array.make 100 0

let rec output size n =
  if (size <= 1) then print_string (atom n)
  else begin
    print_string "(";
    output (dest.(size - 1)) n;
    print_string "=>";
    output (dest.(size - 1)) n;
    print_string ")"
  end

let _ =
  if (Array.length Sys.argv < 2) then begin
    print_endline "Usage: ./impure size num";
    exit 1;
  end;
  let size = int_of_string Sys.argv.(1) in
  let n = int_of_string Sys.argv.(2) in

  assert (n <= 100 && size <= 20);

  for i = 1 to size do
    dest.(i) <- i;
  done;

  for i = 1 to n - 1 do
    output size i;
    print_string " & ";
  done;
  output size n;
  print_newline ()
