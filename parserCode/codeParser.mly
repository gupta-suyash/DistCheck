(* Header *)

%{
open RwOperations
%}

(* Tokens *)

%token <int> INT
%token <string> ID
%token LPAREN
%token RPAREN
%token EQUALS
%token NOT
%token IMPLIES
%token COLON
%token SEMICOLON
%token DDASH
%token LBRACE
%token RBRACE
%token OR
%token AND
%token EXISTS
%token FORALL
%token READ
%token WRITE
%token IF
%token THEN
%token ELSE
%token TEST
%token EOF

(* Associativity and Precedence *)
%left OR
%left AND
%right IMPLIES
%nonassoc NOT 

(* Define start point *)
(*%start <TempOp.code> goal*)
%start <RwOperations.code> goal

%%

goal:
		| g = code; EOF { g }

code:
		| LBRACE; s = initList; RBRACE; 
		  p = program; TEST; COLON; 
		  c = constr { {init=s; pg=p; cns=c;} } 

initList:
		| i = initial { [i] }
		| i = initial m = initList { i :: m }

initial:
		| x = ID; EQUALS; y = INT; 
		  SEMICOLON { (x,y) } 

program:
		| s = session { [s] }
		| s = session m = program { s :: m }

session:
		| x = INT; 
		  tl = statementList; 
		  DDASH { {sid=x; oper=tl;} }

statementList:
		| t = statement { [t] }
		| t = statement m = statementList { t :: m }

statement:
		| t = taggedOper { TagOper t }
		| ite = ifstatement { IfElse ite }

ifstatement:
		| x = ID; COLON; IF; r = rwop; EQUALS; y = INT; 
		  THEN; LBRACE; st = statementList; RBRACE; 
		  ELSE; LBRACE; se = statementList; RBRACE
		  { {ifrd=(x,r); ifval=y; thenwr=st; elsewr=se;} } 	

taggedOper:	
		| x = ID; COLON; r = rwop SEMICOLON { (x,r) }
		

rwop:
		| READ; x = ID { Read x }
		| WRITE; x = ID; EQUALS; y = INT { Write(x,y) }

constr:
		| EXISTS; LPAREN; p = prop; RPAREN 
		  { ExistsStates p }
		| FORALL; LPAREN; p = prop; RPAREN { ForallStates p }
		| NOT; EXISTS; LPAREN; p = prop; RPAREN 
		  { NotExistsState p }

prop:
		| x = ID; COLON; y = ID; EQUALS; z = INT
		  { Atom(x,(y,z)) } 
		| NOT; p = prop { Not p }
		| p1 = prop; AND; 	p2 = prop { And (p1 :: p2 :: []) }
		| p1 = prop; OR; 	p2 = prop { Or (p1 :: p2 :: []) }
		| p1 = prop; IMPLIES; 	p2 = prop 
		  { Implies (p1,p2) }

