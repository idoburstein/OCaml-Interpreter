all: expr evaluation miniml evaltest 

expr: expr.ml
	ocamlbuild -use-ocamlfind expr.byte

evaluation: evaluation.ml
	ocamlbuild -use-ocamlfind evaluation.byte

miniml: miniml.ml
	ocamlbuild -use-ocamlfind miniml.byte

evaltest: evaltest.ml
	ocamlbuild -use-ocamlfind evaltest.byte
