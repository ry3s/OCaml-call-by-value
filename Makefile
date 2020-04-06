SOURCES = syntax.ml type.ml eval.ml print.ml lexer.mll parser.mly main.ml
RESULT  = main

YFLAGS = -v

all: byte-code byte-code-library

-include OCamlMakefile
