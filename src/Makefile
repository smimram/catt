SOURCES = extlib.ml common.ml lang.ml langExt.ml parser.mly lexer.mll prover.ml catt.ml
RESULT = catt
ANNOTATE = true

DOC_FILES = lang.ml prover.ml catt.ml
OCAMLDOCFLAGS := -sort

all: dnc
	./catt test.catt
	./catt eh.catt

web: web.ml dc
	$(OCAMLC) -annot -I `ocamlfind query js_of_ocaml` -pp "camlp4o -I `ocamlfind query js_of_ocaml` pa_js.cmo" -c web.ml
	$(OCAMLC) -I `ocamlfind query js_of_ocaml` js_of_ocaml.cma $(IMPL_CMO) web.cmo -o $(RESULT)
	js_of_ocaml $(RESULT)

conflicts:
	rm -f parser.conflicts
	menhir --explain parser.mly
	less parser.conflicts

include OCamlMakefile
