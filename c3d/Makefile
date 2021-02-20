.PHONY: test %.check

all: test

TEST_DIR=./tests
ALL_TESTS=$(filter-out %.preprocessed.h %/prelude.h, $(wildcard $(TEST_DIR)/*.h))

ifeq (${CLANG_BUILD},)
$(error "Please define $$CLANG_BUILD, it should point to your clang build directory")
endif

ifeq ($(OS),Windows_NT)
	SO = dll
else
ifeq ($(uname -s),Darwin)
	SO = dylib
else
	SO = so
endif
endif

OURCLANG=${CLANG_BUILD}/bin/clang
PLUGIN=./out/src/C3d.so

# This is the compiler that will be used to compile the plugin
# itself. It doesn't have to be clang: you can use gcc too, other
# compilers *may* work too, but we support only clang. You *could*
# also point this to ${OURCLANG}, but might #  be terribly slow if
# you compiled OURCLANG with debugging enabled. On changing this
# you should delete out/.
CC = clang

test: $(patsubst %.h,%.check,$(ALL_TESTS))
accept: $(patsubst %.h,%.accept,$(ALL_TESTS))

$(PLUGIN): src/C3d.cpp out
	make -C out/

$(TEST_DIR)/%.3d $(TEST_DIR)/%.preprocessed.h: $(TEST_DIR)/%.h $(PLUGIN) out 
	${OURCLANG} -mllvm -debug-only=c3d -std=c2x -fblocks -fplugin=$(PLUGIN) -include ./tests/prelude.h $< 2>$<.err || (cat $<.err ; false)

$(TEST_DIR)/%.check:	$(TEST_DIR)/%.3dcheck \
			$(TEST_DIR)/%.hcheck
	touch $@

$(TEST_DIR)/%.accept:	$(TEST_DIR)/%.3daccept \
			$(TEST_DIR)/%.haccept
	@true

$(TEST_DIR)/%.3daccept: $(TEST_DIR)/%.3d
	cp $< "$<.expected"

$(TEST_DIR)/%.haccept: $(TEST_DIR)/%.preprocessed.h
	cp $< "$<.expected"

$(TEST_DIR)/%.3dcheck: $(TEST_DIR)/%.3d $(TEST_DIR)/%.3d.expected
	diff -u --strip-trailing-cr "$<.expected" "$<"

$(TEST_DIR)/%.hcheck: $(TEST_DIR)/%.preprocessed.h $(TEST_DIR)/%.preprocessed.h.expected
	diff -u --strip-trailing-cr "$<.expected" "$<"

out:
	mkdir -p out
	cd out/ && cmake -D LLVM_BUILD_ROOT=${CLANG_BUILD}	\
		../

.DELETE_ON_ERROR:
.SECONDARY: $(patsubst %.h,%.3d,$(ALL_TESTS)) \
            $(patsubst %.h,%.preprocessed.h,$(ALL_TESTS))
