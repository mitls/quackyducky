all: verify_and_build_weaken_tac_plugin extract

FSTAR_HOME?=$(realpath ../../../../FStar)
KREMLIN_HOME?=$(realpath ../../../../kremlin)
OTHERFLAGS?=
EVERPARSE_HOME=../../..

FSTAR_OPTIONS=$(addprefix --include , $(EVERPARSE_HOME)/src/lowparse $(KREMLIN_HOME)/kremlib $(KREMLIN_HOME)/kremlib/obj) --z3rlimit_factor 8 --max_fuel 0 --max_ifuel 2 --initial_ifuel 2 --z3cliopt 'smt.qi.eager_threshold=100'
FSTAR=$(FSTAR_HOME)/bin/fstar.exe $(FSTAR_OPTIONS) $(OTHERFLAGS) --cmi

ROOT=$(wildcard *.fst)
ALREADY_CACHED=--already_cached '+Prims +LowStar +FStar +LowParse +C +Spec.Loops'

.depend: $(ROOT)
	$(FSTAR) --dep full $(ROOT) $(ALREADY_CACHED) --extract '* -Prims' > .depend

include .depend

verify_and_build_weaken_tac_plugin: WeakenTac.cmxs

WeakenTac.cmxs: $(ALL_CHECKED_FILES)
	$(FSTAR) --extract 'LowParse.Norm LowParse.TacLib WeakenTac' --codegen Plugin WeakenTac.fst
	env OCAMLPATH=$(FSTAR_HOME)/bin/ ocamlfind ocamlopt -w -8 -shared -package fstar-tactics-lib -o WeakenTac.cmxs LowParse_Norm.ml LowParse_TacLib.ml WeakenTac.ml

extract: ../EverParse.h

EverParse.rsp: $(ALL_KRML_FILES)
	for f in $^ ; do echo $$f ; done > $@

../EverParse.h: EverParse.rsp
	$(KREMLIN_HOME)/krml \
	  -skip-compilation \
	  -skip-makefiles \
	  -bundle 'C.\*,FStar.\*,LowStar.\*[rename=SHOULDNOTBETHERE]' \
	  -bundle 'LowParse.Low.ErrorCode+EverParse3d.InputBuffer.Aux+Prelude.StaticHeader+ResultOps+EverParse3d.InputStream.Buffer.Aux=Prims,LowParse.\*,Prelude,Prelude.\*,Actions,WeakenTac,EverParse3d.\*[rename=EverParse,rename-prefix]' \
	  -warn-error -9@4 \
	  -fnoreturn-else -fparentheses -fcurly-braces -fmicrosoft \
	  -header ../noheader.txt \
	  -minimal \
	  -add-include 'EverParse:"EverParseEndianness.h"' \
	  -static-header 'Prelude.StaticHeader,LowParse.Low.Base,ResultOps,LowParse.Low.ErrorCode,EverParse3d.InputBuffer.Aux,EverParse3d.InputStream.\*' \
	  -no-prefix LowParse.Slice \
	  -no-prefix LowParse.Low.BoundedInt \
	  -no-prefix EverParse3d.InputBuffer.Aux \
	  -tmpdir .. \
	  -fextern-c \
	  @$^
	! test -e ../EverParse.c
	! test -e ../SHOULDNOTBETHERE.h

%.krml:
	$(FSTAR) $(notdir $(subst .checked,,$<)) --codegen Kremlin --extract_module $(basename $(notdir $(subst .checked,,$<)))
	touch $@

%.checked:
	$(FSTAR) $< --cache_checked_modules $(ALREADY_CACHED)
	touch $@

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS)

.PHONY: all verify extract clean verify_and_build_weaken_tac_plugin

clean:
	rm -f *.checked *.krml ../EverParse.h EverParse.rsp ../Makefile.basic ../Makefile.include .depend *.o *.cmi *.cmx *.cmxs WeakenTac.ml LowParse_TacLib.ml
