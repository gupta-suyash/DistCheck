open TempOp

let filename = Sys.argv.(1)

(* Parse the buffer into an ast *)
let parse fbuf =
  let ast = CodeParser.goal CodeLexer.read fbuf in
  pp_code ast


let main () = 
	let input = open_in filename in 
		let filebuf = Lexing.from_channel input in 
		parse filebuf

let _ = main ()

