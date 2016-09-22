SOURCES = stdlib.ml common.ml lang.ml langExt.ml parser.mly lexer.mll prover.ml catt.ml
RESULT = catt
ANNOTATE = true

all: dnc
	./catt test.catt

conflicts:
	rm -f parser.conflicts
	menhir --explain parser.mly
	less parser.conflicts

include OCamlMakefile
