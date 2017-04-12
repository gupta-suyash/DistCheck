
(* The type of tokens. *)

type token = 
  | WRITE
  | TEST
  | SEMICOLON
  | RPAREN
  | READ
  | RBRACE
  | OR
  | NOT
  | LPAREN
  | LBRACE
  | INT of (int)
  | IMPLIES
  | ID of (string)
  | FORALL
  | EXISTS
  | EQUALS
  | EOF
  | DDASH
  | COLON
  | AND

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val goal: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (TempOp.code)
