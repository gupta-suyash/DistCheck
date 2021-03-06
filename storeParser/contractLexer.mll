(* header *)

{
open ContractParser
}

let white = [' ' '\t']+
let letter = ['a'-'z' 'A'-'Z']
let id = letter+
let newline = ['\n']+

(* Rules *)

rule read =
  parse
	| white 		{ read lexbuf }
	| newline 	{ read lexbuf }
	| "("   		{ LPAREN }
	| ")"   		{ RPAREN }
	| "->"			{ IMPLIES }
	| ":"			{ COLON }
	| ","			{ COMMA }
	| "."			{ DOT }
	| "&&"			{ AND }
	| "||"			{ OR }
	| "v"			{ UNION }
	| "^"			{ INTER }
	| "+"			{ PLUS }
	| "forall"		{ FORALL }
	| "R"			{ R }
	| "W"			{ W }
	| "A"			{ RW }
	| "vis"			{ VIS }
	| "so"			{ SO }
	| "sameobj"		{ SAMEOBJ }
	| id    		{ ID (Lexing.lexeme lexbuf) }
	| eof   		{ EOF }

(* And that's the end of the lexer definition. *)

