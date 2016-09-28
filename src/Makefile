SOURCES = stdlib.ml common.ml lang.ml langExt.ml parser.mly lexer.mll prover.ml catt.ml
RESULT = catt
ANNOTATE = true

all: dnc
	./catt test.catt

web: web.ml dc
	$(OCAMLC) -annot -I `ocamlfind query js_of_ocaml` -pp "camlp4o -I `ocamlfind query js_of_ocaml` pa_js.cmo" -c web.ml
	$(OCAMLC) -I `ocamlfind query js_of_ocaml` js_of_ocaml.cma $(IMPL_CMO) web.cmo -o $(RESULT)
	js_of_ocaml $(RESULT)

conflicts:
	rm -f parser.conflicts
	menhir --explain parser.mly
	less parser.conflicts

include OCamlMakefile
