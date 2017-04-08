open Z3
open Z3.Symbol
open Z3.Sort
open Z3.Expr
open Z3.Boolean
open Z3.FuncDecl
open Z3.Arithmetic
open Z3.Arithmetic.Integer

open RwOperations
open Printf

(* asserts an atomic constraint. 
cpair	- consists of the instruction label, and value to check. *)
let assertAtom ctx rval cpair efftbl = 
	(*printf "-----%s\n" (fst cpair);*)
	let eff = Hashtbl.find efftbl (fst cpair) in 
	let f1 = mk_app ctx rval [eff] in
	mk_eq ctx f1 (Integer.mk_numeral_i ctx (snd (snd cpair))) 
	
(* asserts the property.
p	- type of property. *)
let rec assertProperty ctx rval p efftbl  = 
	match p with 
	| Atom (i,v) -> assertAtom ctx rval (i,v) efftbl
	| Not v -> assertNot ctx rval v efftbl
	| And v -> ((*printf "came to and"; *)
			assertAnd ctx rval (List.hd v) (List.tl v) efftbl)
	| Or v -> assertOr ctx rval (List.hd v) (List.tl v) efftbl
	| Implies (v1,v2) -> assertImplies ctx rval v1 v2 efftbl

and assertNot ctx rval p efftbl = 
				(mk_not ctx (assertProperty ctx rval p efftbl))

and assertAnd ctx rval chd ctl efftbl = 
	match ctl with 
	| [] -> assertProperty ctx rval chd efftbl
	| h::t -> let eq = assertProperty ctx rval h efftbl in 
			mk_and ctx 
			(eq :: (assertAnd ctx rval chd t efftbl)::[])

and assertOr ctx rval chd ctl efftbl = 
	match ctl with 
	| [] -> assertProperty ctx rval chd efftbl 
	| h::t -> let eq = assertProperty ctx rval h efftbl in 
			mk_or ctx 
			(eq :: (assertAnd ctx rval chd t efftbl)::[])

and assertImplies ctx rval pfst psnd efftbl = 
	let eq1 = assertProperty ctx rval pfst efftbl in
	let eq2 = assertProperty ctx rval psnd efftbl in
	mk_implies ctx eq1 eq2

(* Asserts the constraints. 
ctx	- context
rval	- z3 function declaration for rval
cnstr	- testcase constraint
efftbl	- hashtable of effects. *)
let assertConstraints ctx rval cnstr efftbl =
	match cnstr with 
	| ForallStates p 
	| ExistsStates p  (* TODO - Make negative constraint. *)
	| NotExistsState p -> 
		assertProperty ctx rval p efftbl
