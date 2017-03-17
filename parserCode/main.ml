open TempOp

(* Parse a string into an ast *)
let parse s =
  let lexbuf = Lexing.from_string s in
  let ast = CodeParser.goal CodeLexer.read lexbuf in
  ast
