# This file is only to verify LowParse as a library, i.e. to place all
# LowParse.*.checked files in this directory instead of a cache. This
# is to allow users to directly pick from these .checked files instead
# of rebuilding them. This Makefile assumes that everything else from
# the F* standard library and KreMLib is already built (and fails otherwise)

all: verify-all

ifndef FSTAR_HOME
  FSTAR_EXE=$(shell which fstar.exe)
  ifneq ($(.SHELLSTATUS),0)
    FSTAR_HOME=../../../FStar
  endif
endif
ifdef FSTAR_HOME
  FSTAR_EXE=$(FSTAR_HOME)/bin/fstar.exe
endif

ifndef KREMLIN_HOME
  KREMLIB=$(shell ocamlfind query kremlin)
  ifneq ($(.SHELLSTATUS),0)
    KREMLIN_HOME=../../../kremlin
  endif
endif
ifdef KREMLIN_HOME
  KREMLIB=$(KREMLIN_HOME)/kremlib
endif
INCLUDE_KREMLIN=--include $(KREMLIB) --include $(KREMLIB)/obj

# for Steel
INCLUDE_PATHS += $(FSTAR_HOME)/ulib/experimental

FSTAR_OPTIONS += --use_hints --cache_checked_modules $(addprefix --include , $(INCLUDE_PATHS)) $(INCLUDE_KREMLIN) --already_cached *,-LowParse

LOWPARSE_FILES=$(wildcard LowParse.*.fst) $(wildcard LowParse.*.fsti)

clean:
	rm -rf *.checked *.source .depend

.depend: $(LOWPARSE_FILES)
	$(FSTAR_EXE) $(FSTAR_OPTIONS) $(OTHERFLAGS) --dep full $(LOWPARSE_FILES) > $@

include .depend

verify-all: $(ALL_CHECKED_FILES)

$(ALL_CHECKED_FILES): %.checked:
	$(FSTAR_EXE) $(FSTAR_OPTIONS) $(OTHERFLAGS) $<
	touch $@

.PHONY: all verify-all clean %.fst-in %.fsti-in fstar-test

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS) $(OTHERFLAGS)


# For F* testing purposes, cf. FStarLang/FStar@fc30456a163c749843c50ee5f86fa22de7f8ad7a

FSTAR_TEST_FILES= LowParse.Bytes.fst LowParse.Bytes32.fst		  \
	     LowParse.Spec.Base.fst LowParse.SLow.Base.fst	  \
	     LowParse.Spec.Combinators.fst			  \
	     LowParse.SLow.Combinators.fst LowParse.Spec.Enum.fst \
	     LowParse.SLow.Enum.fst

FSTAR_TEST_CHECKED_FILES=$(addsuffix .checked, $(FSTAR_TEST_FILES))

fstar-test: $(FSTAR_TEST_CHECKED_FILES)
