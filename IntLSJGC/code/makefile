OCAMLC := ocamlc
OCAMLOPT := ocamlopt.opt
OCAMLDEP := ocamldep
OCAMLFLAGS := #-g
OCAMLOPTFLAGS := -ccopt -O2 -inline 100 -unsafe #-g

SOURCES := altGenlex.cmo IntFormula.cmo MiscSolver.cmo IntMisc.cmo Cache.cmo Sequent.cmo Model.cmo
SOURCESC := $(SOURCES:.cmo=.cmx)
PROGRAM := prover.cmx
EXEC := $(PROGRAM:.cmx=)

all: $(SOURCESC) $(PROGRAM)
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -o $(EXEC) $^

dbg: $(SOURCESC) $(PROGRAM)
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -p -o $(EXEC) $^

%.cmi: %.mli .depend
	$(OCAMLC) $(OCAMLFLAGS) $<

%.cmo: %.ml .depend
	$(OCAMLC) $(OCAMLFLAGS) -c $<

%.cmx: %.ml .depend
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -c $<

.depend:
	$(OCAMLDEP) *.mli *.ml > .depend

-include .depend

.PHONY: clean

clean:
	-rm -rf *.cm[iox] *.o *~ .*~ .depend
	-rm -rf $(EXEC)
