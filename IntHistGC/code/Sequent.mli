type sequent = MiscSolver.FSet.t array * MiscSolver.FSet.t array

val sw_simp : bool ref
val sw_simpExt : bool ref
val sw_cache : bool ref
val sw_cachemore : bool ref
val sw_cache3 : bool ref
val sw_bjump : bool ref
val sw_hmatch : bool ref

(* definitions *)
val numSets : int
val i_AP : int
val i_AND : int
val i_OR : int
val i_IMP : int
val i_B : int
val i_R : int

(* statistics *)
val nodes : int ref
val c_land : int ref
val c_rand : int ref
val c_lor : int ref
val c_ror : int ref
val c_limp : int ref
val c_rimp : int ref
val c_cache : int ref
val c_bjump : int ref

(* util *)
val findAdd : IntFormula.formula -> int
val insert : MiscSolver.FSet.elt -> MiscSolver.FSet.t array -> unit
val delete : MiscSolver.FSet.elt -> MiscSolver.FSet.t array -> unit
val exists : MiscSolver.FSet.elt -> MiscSolver.FSet.t array -> bool
val print_set : MiscSolver.FSet.t -> unit
val print_seq : sequent -> unit
val print_dbg_seq : sequent -> unit

val emptySeq : unit -> sequent
val copySeq : sequent -> sequent
val subSeq : sequent -> sequent -> bool

(* optimisations *)
(* map from formulae to parent, for blame indentification in caching *)
type origin = bool * MiscSolver.FSet.elt
type parMap = origin MiscSolver.FMap.t ref

val updateMap : MiscSolver.FSet.elt -> origin -> parMap -> sequent -> bool -> unit
val getMap : MiscSolver.FMap.key -> parMap -> bool -> origin
val print_maps : origin MiscSolver.FMap.t -> origin MiscSolver.FMap.t -> unit

(* caching *)
val trueSeq : Cache.trie ref
val falseSeq : Cache.trie ref
val mergeBlame : sequent -> sequent -> parMap -> parMap -> unit
val updateBlame : parMap -> parMap -> sequent -> unit

(* heuristics *)
val chooseF : MiscSolver.FSet.t -> MiscSolver.FSet.elt
val chooseImp : sequent -> MiscSolver.FSet.elt
val atomMatch : sequent -> MiscSolver.FSet.elt ref -> MiscSolver.FSet.elt ref -> bool
val subfmlMatch : MiscSolver.FSet.t -> MiscSolver.FSet.t -> MiscSolver.FSet.elt ref -> bool ref -> bool
val swapBranches : sequent -> sequent ref -> unit
val swapAtomBranches : sequent -> sequent ref -> MiscSolver.FSet.elt ref -> MiscSolver.FSet.elt ref -> unit


(* simplification *)
val simplify : IntFormula.formula -> IntFormula.formula
val rewriteImps : IntFormula.formula -> IntFormula.formula
val substitute : MiscSolver.FSet.elt -> MiscSolver.FSet.elt -> IntFormula.formula -> bool -> IntFormula.formula
val replace : sequent -> MiscSolver.FSet.elt -> bool -> IntFormula.formula -> parMap -> parMap -> bool -> bool -> unit
val getPolarity : MiscSolver.FSet.elt -> int array -> int array -> int array -> int array -> int -> bool -> unit
val doSimplify : sequent -> MiscSolver.FSet.elt -> bool -> IntFormula.formula -> parMap -> parMap -> sequent -> unit

(* setup *)
val init : IntFormula.formula -> sequent

(* calculus rules *)
val axioms : sequent -> bool
val axioms_cache : sequent -> sequent -> parMap -> parMap -> bool
val top_bot : sequent -> unit
val and_left : sequent -> MiscSolver.FSet.elt -> parMap -> parMap -> sequent -> unit
val and_right : sequent -> MiscSolver.FSet.elt -> parMap -> parMap -> sequent -> sequent
val or_left : sequent -> MiscSolver.FSet.elt -> parMap -> parMap -> sequent -> sequent
val or_right : sequent -> MiscSolver.FSet.elt -> parMap -> parMap -> sequent -> unit
val imp_left : sequent -> MiscSolver.FSet.elt -> parMap -> parMap -> sequent -> sequent
val imp_first : sequent -> MiscSolver.FSet.elt -> parMap -> parMap -> sequent -> unit
val imp_rest : sequent -> MiscSolver.FSet.elt -> parMap -> parMap -> sequent -> unit

(* main search functions *)
val no_branch : sequent -> parMap -> parMap -> sequent ->  unit
val mainl : sequent -> sequent -> bool
val prove : sequent -> bool
