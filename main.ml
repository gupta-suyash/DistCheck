open Printf
open TempOp
open ContractLang

let testcase = Sys.argv.(1)
let storesem = Sys.argv.(2)

(* Parse the testcase into an ast *)
let parse cdbuf stbuf =
  let cdast = CodeParser.goal CodeLexer.read cdbuf in
  let stast = ContractParser.goal ContractLexer.read stbuf in
  (pp_code cdast; printf "\n"; pp_st stast)

let main () = 
	let test = open_in testcase in 
	let cdbuf = Lexing.from_channel test in 
	let store = open_in storesem in 
	let stbuf = Lexing.from_channel store in	
	parse cdbuf stbuf

let _ = main ()


