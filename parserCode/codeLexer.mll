(* header *)

{
open CodeParser
}

let white = [' ' '\t']+
let digit = ['0'-'9']
let int = '-'? digit+
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
	| "="   		{ EQUALS }
	| "~"				{ NOT }	
	| "->"			{ IMPLIES }
	| ":"				{ COLON }
	| ";"				{ SEMICOLON }
	| "--"			{ DDASH }
	| "{"				{ LBRACE }
	| "}"				{ RBRACE }
	| "\\/"			{ OR }
	| "^"			{ AND }
	| "exists"	{ EXISTS }
	| "forall"	{ FORALL } 
	| "read"		{ READ }
	| "write"		{ WRITE }
	| "Test"		{ TEST }
	| id    		{ ID (Lexing.lexeme lexbuf) }
	| int   		{ INT (int_of_string (Lexing.lexeme lexbuf)) }
	| eof   		{ EOF }

(* And that's the end of the lexer definition. *)

