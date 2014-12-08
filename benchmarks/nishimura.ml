let atom = "p"

let f = Array.make 5 ""
let dest1 = Array.make 100 0
let dest2 = Array.make 100 0
let con = Array.make 100 ""

let rec output n =
  if (n <= 4) then print_string f.(n)
  else begin
    print_string "(";
    output (dest1.(n));
    print_string con.(n);
    output (dest2.(n));
    print_string ")"
  end

let _ =
  if (Array.length Sys.argv < 2) then begin
    print_endline "Usage: ./nishimura n";
    exit 1;
  end;
  let n = int_of_string Sys.argv.(1) in

  assert (n <= 100);

  f.(0) <- "(p & ~p)";
  f.(1) <- "p";
  f.(2) <- "(~p)";
  f.(3) <- "(p|(~p))";
  f.(4) <- "((p|(~p))=>p)";

  for i = 1 to (n / 2) do
    con.(2 * i + 3) <- "|";
    con.(2 * i + 4) <- "=>";
    dest1.(2 * i + 3) <- 2 * i + 1;
    dest2.(2 * i + 3) <- 2 * i + 2;
    dest1.(2 * i + 4) <- 2 * i + 3;
    dest2.(2 * i + 4) <- 2 * i + 1
  done;

  output n
