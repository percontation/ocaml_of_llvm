LLVM_CONFIG?=llvm-config-mp-8.0

export PATH:=$(shell $(LLVM_CONFIG) --bindir):$(PATH)

.PHONY: all clean

all: build/combined.bc

clean:
	touch build/_
	rm -Rf build/*

MYFLAGS:=-emit-llvm -target le32-unknown-nacl -Oz -nostdlibinc -isystem pdclib/include -isystem pdclib_platform/include

build/xed-ex1.bc: xed/examples/xed-ex1.c
	clang $(MYFLAGS) -Ixed/include/public -Ixed/include/public/xed -Ixed/include/private -Ixed/obj -Ixed/obj/include-private $^ -c -o $@

build/xed-examples-util.bc: xed/examples/xed-examples-util.c
	clang $(MYFLAGS) -Ixed/include/public -Ixed/include/public/xed -Ixed/include/private -Ixed/obj -Ixed/obj/include-private $^ -c -o $@

build/%.bc: %.c
	clang $(MYFLAGS) $^ -c -o $@

build/%.bc: %.cpp
	clang++ $(MYFLAGS) $^ -c -o $@

build/combined.bc: $(wildcard libxed/*.o) build/libc.bc build/xed-ex1.bc build/xed-examples-util.bc build/printf.bc
	llvm-link $^ | opt -name-anon-globals -instnamer -internalize -internalize-public-api-list=main -argpromotion -loweratomic -lowerinvoke -Oz -o $@
