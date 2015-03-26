(** This module implements Intuitionistic formulae
    (e.g. parsing, printing, (de-)constructing, ...).
    @author Jimmy Thomson
 *)


module A = AltGenlex


(** A general exception for all kinds of errors
    that can happen in the tableau procedure.
    More specific information is given in the argument. 
 *)
exception IntException of string


(** Defines INT formulae.
 *)
type formula = 
  | TRUE
  | FALSE
  | AP of string
  | EQU of formula * formula
  | IMP of formula * formula
  | OR of formula * formula
  | AND of formula * formula


(** Determines the size of a formula.
    Basically, it counts the symbols (without parentheses) of a formula, 
    @param f A formula.
    @return The size of f.
 *)
let rec sizeFormula f =
  match f with
  | TRUE 
  | FALSE 
  | AP _ -> 1
  | EQU (f1, f2) 
  | IMP (f1, f2)
  | OR (f1, f2)  
  | AND (f1, f2) -> succ (sizeFormula f1 + sizeFormula f2)


(** Appends a string representation of a formula to a string buffer.
    Parentheses are ommited where possible
    where the preference rules are defined as usual.
    @param sb A string buffer.
    @param f A formula.
 *)
let rec exportFormula_buffer sb f =
  let prio n lf =
    let prionr = function
	  | EQU _ -> 0
      | IMP _  -> 2 
      | OR _ -> 3
      | AND _ -> 4
      | _ -> 5
    in
    if true || prionr lf < n then begin
      Buffer.add_char sb '(';
      exportFormula_buffer sb lf;
      Buffer.add_char sb ')'
    end
    else exportFormula_buffer sb lf
  in
  match f with
  | TRUE -> Buffer.add_string sb "True"
  | FALSE -> Buffer.add_string sb "False"
  | AP s -> Buffer.add_string sb s
  | EQU (f1, f2) ->
	  prio 0 f1;
	  Buffer.add_string sb " <=> ";
	  prio 0 f2;
  | IMP (f1, f2) ->
      prio 3 f1;
      Buffer.add_string sb " => ";
      prio 3 f2
  | OR (f1, f2) ->
      prio 4 f1;
      Buffer.add_string sb " | ";
      prio 4 f2
  | AND (f1, f2) ->
      prio 5 f1;
      Buffer.add_string sb " & ";
      prio 5 f2

(** Converts a formula into a string representation.
    Parentheses are ommited where possible
    where the preference rules are defined as usual.
    @param f A formula.
    @return A string representing f.
 *)
let exportFormula f =
  let size = sizeFormula f in
  let sb = Buffer.create (2 * size) in
  exportFormula_buffer sb f;
  Buffer.contents sb

let mk_exn s = IntException s


(** These functions parse a token stream to obtain a formula.
    It is a standard recursive descent procedure.
    @param ts A token stream.
    @return The resulting (sub-)formula.
    @raise IntException if ts does not represent a formula.
 *)
let rec parse_equ ts =
  let f1 = parse_imp ts in
  match Stream.peek ts with
  | None -> f1
  | Some (A.Kwd "<=>") ->
      Stream.junk ts;
      let f2 = parse_equ ts in
		EQU (f1, f2)
  | _ -> f1

(** These functions parse a token stream to obtain a formula.
    It is a standard recursive descent procedure.
    @param ts A token stream.
    @return The resulting (sub-)formula.
    @raise IntException if ts does not represent a formula.
 *)
and parse_imp ts =
  let f1 = parse_or ts in
  match Stream.peek ts with
  | None -> f1
  | Some (A.Kwd "=>") ->
      Stream.junk ts;
      let f2 = parse_imp ts in
      IMP (f1, f2)
  | _ -> f1

(** These functions parse a token stream to obtain a formula.
    It is a standard recursive descent procedure.
    @param ts A token stream.
    @return The resulting (sub-)formula.
    @raise IntException if ts does not represent a formula.
 *)
and parse_or ts =
  let f1 = parse_and ts in
  match Stream.peek ts with
  | None -> f1
  | Some (A.Kwd "|") ->
      Stream.junk ts;
      let f2 = parse_or ts in
      OR (f1, f2)
  | _ -> f1

(** These functions parse a token stream to obtain a formula.
    It is a standard recursive descent procedure.
    @param ts A token stream.
    @return The resulting (sub-)formula.
    @raise IntException if ts does not represent a formula.
 *)
and parse_and ts =
  let f1 = parse_rest ts in
  match Stream.peek ts with
  | None -> f1
  | Some (A.Kwd "&") ->
      Stream.junk ts;
      let f2 = parse_and ts in
      AND (f1, f2)
  | _ -> f1

(** These functions parse a token stream to obtain a formula.
    It is a standard recursive descent procedure.
    @param ts A token stream.
    @return The resulting (sub-)formula.
    @raise IntException if ts does not represent a formula.
 *)
and parse_rest ts =
  match Stream.next ts with
  | A.Kwd "(" -> 
      let f = parse_equ ts in
      let _ =
        match Stream.next ts with
        | A.Kwd ")" -> ()
        | t -> A.printError mk_exn ~t ~ts "\")\" expected: "
      in
      f
  | A.Kwd "~" ->
      let f = parse_rest ts in
      IMP (f, FALSE)
  | A.Kwd "True" -> TRUE
  | A.Kwd "False" -> FALSE
  | A.Ident s -> AP s
  | t -> A.printError mk_exn ~t ~ts 
        ("\"~\", \"(\", \"True\", \"False\", \"DIA\", \"BOX\", \"AID\", \"XOB\", or <ident> expected: ")
        
let keywords =
  ["(";")";"<=>";"=>";"|";"&";"~";"True";"False"]

let lexer = A.make_lexer keywords

(** Parses a string to obtain a formula.
    @param s A string representing a formula.
    @return The resulting formula.
    @raise IntException if s does not represent a formula.
 *)
let importFormula s =
  let ts = lexer s in
  try
    begin
      let f = parse_equ ts in
      let _ =
        match Stream.peek ts with
        | None -> ()
        | Some _ -> A.printError mk_exn ~ts "EOS expected: "
      in
      f
    end
  with Stream.Failure -> A.printError mk_exn ~ts "unexpected EOS"

let lexer_ic = A.make_lexer_file ~comment:"%" keywords

(** Parses an input channel to obtain a formula.
    @param ic An input channel.
    @return The conjunction of all formulae read from ic.
    @raise IntException if s does not represent a formula.
 *)
let importFormula_ic ic =
  let ts = lexer_ic ic in
  let rec readFormula acc =
    match Stream.peek ts with
    | None -> acc
    | Some _ ->
        let f = parse_equ ts in
        let nacc = AND (acc, f) in
        readFormula nacc
  in
  try
    let f = parse_imp ts in
    readFormula f
  with Stream.Failure -> A.printError mk_exn ~ts "unexpected EOS"



(** The number of constructors of type formula.
 *)
let numberOfTypes = 7

(** Maps a formula to an integer representing its type (e.g. or-formula).
    The assignment of integers to types is arbitrary,
    but it is guaranteed that different types 
    map to different integers
    and that the codomain of this function is [0..numberOfTypes-1].
    @param f A formula.
    @return An integer that represents the type of f.
 *)
let getTypeFormula f = 
  match f with
  | TRUE -> 0
  | FALSE -> 1
  | AP _ -> 2
  | EQU _ -> 3
  | IMP _ -> 4
  | OR _ -> 5
  | AND _ -> 6

(** Generates a function comp that compares two formula.
    The order that is defined by comp is lexicograhic.
    It depends on the given ranking of types of formulae.
    @param order A list containing exactly the numbers 0 to numberOfTypes-1.
    Each number represents a type
    and the list therefore induces a ranking on the types
    with the smallest type being the first in the list.
    @return A function comp that compares two formula.
    comp f1 f2 returns 0 iff f1 is equal to f2, 
    -1 if f1 is smaller than f2, and
    1 if f1 is greater than f2.
    @raise Failure if order is not of the required form.
 *)
let generateCompare order =
  let rec listOK = function
    | 0 -> true
    | n ->
        let nn = pred n in
        if List.mem nn order then listOK nn
        else false
  in
  let _ = 
    if (List.length order <> numberOfTypes) || not (listOK numberOfTypes) then
      raise (Failure "generateCompare: argument is not in the correct form")
  in
  let arrayOrder = Array.make numberOfTypes 0 in
  let _ = 
    for i = 0 to (numberOfTypes - 1) do
      let ty = List.nth order i in
      arrayOrder.(ty) <- i
    done
  in
  let rec comp f1 f2 =
    match f1, f2 with
    | TRUE, TRUE
    | FALSE, FALSE -> 0
    | AP s1, AP s2 ->
        let x = (String.length s1) - (String.length s2) in
        if (x = 0) then compare s1 s2
        else x
    | OR (f1a, f1b), OR (f2a, f2b)
    | AND (f1a, f1b), AND (f2a, f2b)
    | EQU (f1a, f1b), EQU (f2a, f2b)
    | IMP (f1a, f1b), IMP (f2a, f2b) ->
        let res1 = comp f1a f2a in
        if res1 <> 0 then res1
        else comp f1b f2b
    | _ ->
        let t1 = getTypeFormula f1 in
        let r1 = arrayOrder.(t1) in
        let t2 = getTypeFormula f2 in
        let r2 = arrayOrder.(t2) in
        if r1 < r2 then (-1) else 1
  in
  comp



(** Defines a ranking of the different types of formulae
    such that the ranking of the types corresponds
    to the ranking of the tableau rules.
 *)
let aRanking = [
      getTypeFormula TRUE;
      getTypeFormula FALSE;
      getTypeFormula (AP "");
      getTypeFormula (EQU (TRUE, TRUE));
      getTypeFormula (IMP (TRUE, TRUE));
      getTypeFormula (OR (TRUE, TRUE));
      getTypeFormula (AND (TRUE, TRUE))]

(*let aRanking = [ getTypeFormula (AND (TRUE, TRUE));
				 getTypeFormula (OR (TRUE, TRUE));
                 getTypeFormula TRUE;
                 getTypeFormula FALSE;
				 getTypeFormula (EQU (TRUE, TRUE));
				 getTypeFormula (IMP (TRUE, TRUE));
                 getTypeFormula (AP "")]
*)

(* Formula pre-processing *)
(* Comparator *)
let intFCompare = generateCompare aRanking;;
let rec prep f =
  match f with
  | TRUE -> TRUE
  | FALSE -> FALSE
  | AP s -> AP s
  | AND (f1, f2) ->
      let first = prep f1 in
      let second = prep f2 in
      let x = intFCompare first second in
      (match x with
      | 0 -> first
      | _ when x < 0 -> AND (first, second)
      | _ -> AND (second, first))
  | OR (f1, f2) ->
      let first = prep f1 in
      let second = prep f2 in
      let x = intFCompare first second in
      (match x with
      | 0 -> first
      | _ when x < 0 -> OR (first, second)
      | _ -> OR (second, first))
  | IMP (f1, f2) ->
      let first = prep f1 in
      let second = prep f2 in
      let x = intFCompare first second in
      (match x with
      | 0 -> TRUE
      | _ -> IMP (first, second))
  | EQU (f1, f2) ->
      let first = prep f1 in
      let second = prep f2 in
      let x = intFCompare first second in
      match x with
      | 0 -> TRUE
      | _ when x < 0 -> EQU (first, second)
      | _ -> EQU (second, first)


(** Calculates all formulae
    which may be created in the tableau procedure (i.e. a kind of Fischer-Ladner closure).
    @param compF A function that compares formulae.
    @param f The initial formula of the tableau procedure
    @return A list containing all formulae of the closure of f in increasing order.
 *)
let detClosure compF f =
  let module TSet = Set.Make(
    struct
      type t = formula
      let (compare : t -> t -> int) = compF
    end
   )
  in
  let rec detC fs f =
    if TSet.mem f fs then fs
    else
      let nfs = TSet.add f fs in
      match f with
      | TRUE
      | FALSE
      | AP _ -> nfs
	  | EQU (f1, f2)
	  | IMP (f1, f2)
      | OR (f1, f2)
      | AND (f1, f2) ->
          let nfs = detC nfs f1 in
          detC nfs f2
  in
  let tset = TSet.empty in
  let tset = TSet.add TRUE tset in
  let tset = TSet.add FALSE tset in
  let rset = detC tset f in
  TSet.elements rset
