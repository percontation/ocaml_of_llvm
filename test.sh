#!/bin/sh
set -xe
dune build _build/default/src/ocaml_of_llvm.exe
make -C linkopt all
echo '---running ocaml_of_llvm---'
OCAMLRUNPARAM=b ./_build/default/src/ocaml_of_llvm.exe ./linkopt/build/combined.bc > testprog.ml
echo '---compiling testprog.ml---'
OCAMLRUNPARAM=l=9999 ocamlfind ocamlc -linkpkg -package num -g testprog.ml -o testprog
#OCAMLRUNPARAM=l=9999 ocamlfind ocamlopt -linkpkg -package num -g testprog.ml -o testprog
echo '---running test.ml---'
OCAMLRUNPARAM=b ./testprog 55
echo '---success!---'
