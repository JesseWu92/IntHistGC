let atom = "p"

let f = Array.make 5 ""
let dest1 = Array.make 50 0
let dest2 = Array.make 50 0
let dest3 = Array.make 50 0

let rec output n =
  if (n <= 4) then print_string f.(n)
  else begin
    print_string "(";
    output (dest1.(n));
    print_string "=>(";
    output (dest2.(n));
    print_string "|";
    output (dest3.(n));
    print_string "))"
  end

let _ =
  if (Array.length Sys.argv < 2) then begin
    print_endline "Usage: ./nishimura n";
    exit 1;
  end;
  let n = int_of_string Sys.argv.(1) in

  assert (n <= 50);

  f.(0) <- "(p & ~p)";
  f.(1) <- "p";
  f.(2) <- "(~p)";
  f.(3) <- "(~(~p))";
  f.(4) <- "((~(~p))=>p)";

  for i = 5 to n do
    dest1.(i) <- i - 1;
    dest2.(i) <- i - 3;
    dest3.(i) <- i - 4;
  done;

  output n
