module TMap :
  sig
    type key = int
    type +'a t
    val empty : 'a t
    val is_empty : 'a t -> bool
    val mem : key -> 'a t -> bool
    val add : key -> 'a -> 'a t -> 'a t
    val singleton : key -> 'a -> 'a t
    val remove : key -> 'a t -> 'a t
    val merge :
      (key -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t
    val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int
    val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
    val iter : (key -> 'a -> unit) -> 'a t -> unit
    val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
    val for_all : (key -> 'a -> bool) -> 'a t -> bool
    val exists : (key -> 'a -> bool) -> 'a t -> bool
    val filter : (key -> 'a -> bool) -> 'a t -> 'a t
    val partition : (key -> 'a -> bool) -> 'a t -> 'a t * 'a t
    val cardinal : 'a t -> int
    val bindings : 'a t -> (key * 'a) list
    val min_binding : 'a t -> key * 'a
    val max_binding : 'a t -> key * 'a
    val choose : 'a t -> key * 'a
    val split : key -> 'a t -> 'a t * 'a option * 'a t
  end

type node = int * bool * int ref
type trie = T of node option * trie TMap.t
val empty : trie

val find : TMap.key -> trie -> trie
val mem : TMap.key list -> trie -> bool
val add : TMap.key list -> trie -> trie
val remove : TMap.key list -> trie -> trie
val size : trie -> int


val existsSubset : TMap.key list -> trie -> bool
val existsSuperset : TMap.key list -> trie -> bool
val findSubset : TMap.key list -> trie -> MiscSolver.FSet.t ref -> bool
val trimSubset : trie -> trie
val cleanCache : trie -> trie
