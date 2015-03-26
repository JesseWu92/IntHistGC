(** Set-trie implementation for fast sequent lookups, see
    http://link.springer.com/chapter/10.1007%2F978-3-642-40511-2_10#
 *)

(** Map from integers to tries *)
module TMap = Map.Make(
  struct
    type t = int
    let compare (x : int) y = compare x y
  end)


(** Nodes (label, flag, counter), to represent set paths.
    Flag indicates end of a set.
    Counter counts lookup hits. *)
type node = int * bool * int ref

(** Set-trie, a node may have arbitrarily many children *)
type trie = T of node option * trie TMap.t

(** Empty trie *)
let empty = T (None, TMap.empty)

(* Exception for early termination of subset operations *)
exception Found

(** Return the sub-trie corresponding to x if it exists *)
let find x t = match (x, t) with
    _, T (None, _) -> raise Not_found
  | x, T (Some n, m) -> TMap.find x m

(** Check if a list l exists in trie t *)
let rec mem l t = match (l, t) with
    [], T (None, _) -> false
  | [], T (Some (_, flag, _), _) -> flag
  | x::xs, T (_, m) -> try mem xs (TMap.find x m) with Not_found -> false


(** Add a list l to trie t *)
let rec add l t =
  let new_trie x = T (Some (x, false, ref 0), TMap.empty) in
  match (l, t) with
    [], T (Some (l, _, c), m) -> T (Some (l, true, c), m)
  | x::xs, T (n, m) ->
      let t1 = try TMap.find x m with Not_found -> new_trie x in
      let t2 = add xs t1 in
      T (n, TMap.add x t2 m)
  | [], T (None, _) -> t


(** Remove a list l from trie t *)
let rec remove l t = match (l, t) with
    [], T (Some (x, _, _), m) -> T (Some (x, false, ref 0), m)
  | x::xs, T (n, m) -> (
    try begin
      let t1 = remove xs (TMap.find x m) in
      match t1 with
        T (Some (x, false, _), m1) when TMap.is_empty m1 ->
            T (n, TMap.remove x m)
      | _ -> T (n, TMap.add x t1 m)
    end with Not_found -> t)
  | [], T (None, _) -> t
  

(** Count number of cached elements in trie t *)
let rec size t =
  let count = ref 0 in
  let recurse m = TMap.iter (fun k v -> count := !count + (size v)) m in
  match t with
    T (Some  (x, true, _), m ) -> count := succ !count; recurse m; !count
  | T (n, m) -> recurse m; !count

(** Check if a tree t contains a subset of an ordered list l.
    
    Original Algorithm:
    if (node.flag is set) then true;
    if (l is empty) then false;
    found = false;
    if (node has child labeled l.head) then
      found = existsSubset l.tail child;
    if (not found) then existsSubset l.tail t
    else true;
 *)
let rec existsSubset l t = match (l, t) with
    _, T (Some (x, true, c), _) -> c := succ !c; true
  | [], _ -> false
  | x::xs, T (n, m) -> (
      try begin
        let t1 = TMap.find x m in
        if (existsSubset xs t1) then raise Found;
        existsSubset xs t
      end with
          Not_found -> existsSubset xs t
        | Found -> true)
  
(** Check if a tree t contains a superset of an ordered list l

    Algorithm:
    if (l is empty) then true;
    found = false;
    for (each child c of node with c <= l.head) & (while not found)
      if (c is labeled l.head) then
        found = existsSuperset l.tail c
      else
        found = existsSuperset l c
    return found
 *)
let rec existsSuperset l t =
  let recurse head tail key child =
    if (head < key) then ()
    else if (head = key) then begin
      if (existsSuperset tail child) then raise Found
    end
    else if (existsSuperset (head::tail) child) then raise Found
  in
  match (l, t) with
      [], _ -> true
    | x::xs, T (n, m) -> (
        try begin
          TMap.iter (recurse x xs) m;
          false
        end with Found -> true)

(** Find a subset of l in trie t if one exists.
    @return Subset as an int set
 *)
let rec findSubset l t set = match (l, t) with
    _, T (Some (x, true, c), _) -> c := succ !c; true
  | [], _ -> false
  | x::xs, T (n, m) -> (
      try begin
        let t1 = TMap.find x m in
        if (findSubset xs t1 set) then raise Found;
        findSubset xs t set
      end with
          Not_found -> findSubset xs t set
        | Found -> set := MiscSolver.FSet.add x !set; true)


(** Trim redundant entries for a subset only cache *)
let rec trimSubset t = match t with
    T (Some (x, true, c), _) -> T (Some (x, true, c), TMap.empty)
  | T (n, m) ->
      let m1 = ref TMap.empty in
      TMap.iter (fun k v -> m1 := TMap.add k (trimSubset v) !m1) m;
      T (n, !m1)

(** Clear entries with no hits *)
let rec cleanCache t = match t with
    T (Some (l, flag, c), m) when (!c > 0) ->
        T (Some (l, flag, c), m)
  | T (Some (_, _, c), m) when (!c = 0) && (TMap.is_empty m) ->
        T (None, TMap.empty)
  | T (n, m) ->
      let m1 = ref TMap.empty in
      TMap.iter (fun k v ->
          let t1 = cleanCache v in
          match t1 with
            T (Some n1, _) -> m1 := TMap.add k (cleanCache v) !m1
          | _ -> ()) m;
      match T (n, !m1) with
        T (Some (_, _, c), m2) when (!c = 0) && (TMap.is_empty m2) ->
            T (None, TMap.empty)
      | _ -> T (n, !m1)

(*
let _ =
  let trie = ref empty in
  trie := add [0;1] !trie;
  trie := add [0;1;2] !trie;
  trie := add [1;2] !trie;
  print_endline (string_of_bool  (existsSubset [-1;0;1] !trie));
  print_endline (string_of_int (size !trie));
  trie := trimSubset !trie;
  trie := cleanCache !trie;
  print_endline (string_of_int (size !trie));
*)
