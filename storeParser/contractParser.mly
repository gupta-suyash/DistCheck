(* Header *)

%{
open ContractLang
%}

(* Tokens *)

%token <string> ID
%token LPAREN
%token RPAREN
%token IMPLIES
%token COLON
%token COMMA
%token DOT
%token OR
%token AND
%token FORALL
%token R
%token W
%token O
%token UNION
%token INTER
%token PLUS
%token VIS
%token SO
%token SAMEOBJ
%token EOF


(* Define start point *)
%start <ContractLang.stsem> goal

%%

goal:
		| g = stsem; EOF { g }

stsem:
		| c = contract; { [c] }
		| c = contract m = stsem { c :: m }

contract:
		| FORALL; p = parameterList; DOT; prop = property
		  { {param=p; prp=prop;} }
		
parameterList:
		| p = parameter { [p] }
		| p = parameter m = parameterList { p :: m }

parameter:
		| LPAREN; x = ID; COLON; 
		  y = opType; RPAREN { (x,y) }

opType:
		| R { Read }
		| W { Write }
		| O { Any }

property:
		| r = relation; 
		  LPAREN; x = ID; COMMA; y = ID; RPAREN { Patom(r,(x,y)) }
		| LPAREN; p1 = property; OR; p2 = property; RPAREN
		  { Por(p1,p2) }
		| LPAREN; p1 = property; AND; p2 = property; RPAREN 
		  { Pand(p1,p2) }
		| LPAREN; p1 = property; IMPLIES; p2 = property; RPAREN 
		  { Pimplies(p1,p2) }

relation:
		| VIS { Vis }
		| SO { So }
		| SAMEOBJ { Sameobj }
		| LPAREN; r1 = relation; UNION; r2 = relation; RPAREN
		  { Union(r1,r2) }
		| LPAREN; r1 = relation; INTER; r2 = relation; RPAREN
		  { Inter(r1,r2) }
		| r1 = relation; PLUS; { Rplus r1 }

