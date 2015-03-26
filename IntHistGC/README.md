# IntHistGC

**Version 1.29**

See paper:

R. Goré, J. Thomson, J. Wu. A History-Based Theorem Prover for Intuitionistic Propositional Logic using Global Caching: IntHistGC System Description. IJCAR 2014. LNCS (LNAI) 8562, pp. 262-268, Springer (2014).

---

**Installation Pre-requisites:**

* Ensure ocaml 3.12 is installed (ocamldep, ocamlc and ocamlopt.opt).
  * ocamlopt.opt is not strictly necessary -
    changing "ocamlopt.opt" to "ocamlopt" in "makefile" merely slows compile time

* For viewing of proof model, Graphviz (dot) is required.
  * Graphviz 2.29 or later is required for some graph features.

---

**Instructions:**

*Compile:*

    make


*Run:*

    ./prover [options] formula.txt


*To see available options use:*

    ./prover -help

*Output:*

* A statement regarding validity
  * With '-m', a graph corresponding to the sequent proof process


*Formula Syntax:*
*   negation:       ~ p
*   conjunction:    p & q
*   disjunction:    p | q
*   implication:    p => q
*   equivalence:    (p <=> q)

---

Notes:
*   negation (~ p) is interpreted as (p => false)
*   equivalence (p <=> q) is interpreted as ((p => q) & (q => p))

