# DistCheck
Testing distributed code snippets

To compiler the code:
ocamlbuild -use-menhir -use-ocamlfind -I storeParser -I parserCode main.ml main.native

To execute:
./main.native parserCode/tcase2.txt storeParser/tsem1.txt
