ROOT=Main.fst
FSTAR_HOME?=../../../FStar
EVERPARSE_HOME?=../..
KREMLIN_HOME?=$(EVERPARSE_HOME)/../kremlin

INCLUDE_PATHS=
OTHERFLAGS?=
FSTAR=$(FSTAR_HOME)/bin/fstar.exe $(OTHERFLAGS) $(addprefix --include , $(INCLUDE_PATHS) $(EVERPARSE_HOME)/src/3d/prelude) --already_cached 'Prims FStar -FStar.Getopt'

all: 3d prelude

test: demo

demo: all
	+$(MAKE) -C tests test

.PHONY: all prelude test

prelude:
	+$(MAKE) -C prelude

3d: ocaml/Main.native
	cp ocaml/Main.native 3d

.depend: 
	$(FSTAR) --odir ocaml --dep full $(ROOT) --extract '* -Prims -FStar' > .depend

include .depend

ocaml/Main.native: $(ALL_ML_FILES) ocaml/parser.mly ocaml/lexer.mll
	rm -f ocaml/Main.native
	+$(MAKE) -C ocaml Main.native

%.checked:
	$(FSTAR) $< --cache_checked_modules
	touch $@

%.ml:
	$(FSTAR) $(notdir $(subst .checked,,$<)) --codegen OCaml --extract_module $(basename $(notdir $(subst .checked,,$<))) --odir ocaml

test.native: ast.ml lexer.mll parser.mly test.ml
	rm -f test.native
	ocamlbuild -use-menhir -tag thread -use-ocamlfind -quiet -pkg batteries -pkg menhirLib $@

clean:
	rm -rf *.checked $(ALL_ML_FILES) *~


FSTAR_OPTIONS=$(OTHERFLAGS) $(addprefix --include , $(EVERPARSE_HOME)/src/lowparse $(KREMLIN_HOME)/kremlib)

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS)