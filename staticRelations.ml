open Z3
open Z3.Symbol
open Z3.Sort
open Z3.Expr
open Z3.Boolean
open Z3.Goal
open Z3.Probe
open Z3.Solver
open Z3.Model
open Z3.FuncDecl
open Z3.Enumeration
open Z3.Arithmetic
open Z3.Arithmetic.Integer

open RwOperations
open TestMethods
open Printf

(* Asserts forall effect2, (so effect1 effect2) = true (if possible) 
op	- effect1 *)
(* Extra but correct bindings being generated. 
No use of trasitivity property then. *)
let rec relateSo ctx so op oplist efftbl = 
	match oplist with 
	| [] -> []
	| h::t -> match h with (s,opr) -> 
		  let eff1 = Hashtbl.find efftbl op in
		  let eff2 = Hashtbl.find efftbl s in
		  let fapp = mk_app ctx so [eff1;eff2] in 
		  (mk_eq ctx fapp (mk_true ctx) :: 
			   relateSo ctx so op t efftbl) 

let rec setSoBinding ctx so oplist efftbl =
	match oplist with 
	| [] -> []
	| h::t -> match h with (s,op) ->
		  List.append (setSoBinding ctx so t efftbl)
		  (relateSo ctx so s t efftbl)

(* Sets so bindings. 
ctx	- context
so	- so method
prog	- testcase
efftbl	- hashtable of effects. *)
let rec assertSoBinding ctx so prog efftbl = 
	match prog with 
	| [] -> []
	| h::t -> List.append (assertSoBinding ctx so t efftbl)
			(setSoBinding ctx so h.oper efftbl)


(* Asserts (same effect1 effect2) == true, (if possible) 
s1	- label of effect1
v1	- program variable in effect1. *)			
let rec relateSame ctx same oplist s1 v1 efftbl = 
	match oplist with 
	| [] -> []
	| h::t -> match h with (s2,e2) -> 
		  match e2 with 
		  | Read v2 -> 	if (String.compare v1 v2) == 0
				then 	let eff1 = Hashtbl.find efftbl s1 in
		  			let eff2 = Hashtbl.find efftbl s2 in
		  			let fapp = mk_app ctx same [eff1;eff2] in 
		  			mk_eq ctx fapp (mk_true ctx) :: 
			   		relateSame ctx same t s2 v2 efftbl
				else 	relateSame ctx same t s1 v1 efftbl
		  | Write v ->  if (String.compare v1 (fst v)) == 0
				then 	let eff1 = Hashtbl.find efftbl s1 in
		  			let eff2 = Hashtbl.find efftbl s2 in
		  			let fapp = mk_app ctx same [eff1;eff2] in 
		  			mk_eq ctx fapp (mk_true ctx) :: 
			   		relateSame ctx same t s2 (fst v) efftbl
				else 	relateSame ctx same t s1 v1 efftbl

(* op1	- string representation of program variable. *)
let rec setSameBinding ctx same oplist op1 efftbl = 
	match oplist with
	| [] -> []
	| h::t -> match h with (s,op2) -> 
		  match op2 with 
		  | Read n -> 	if (String.compare n op1) == 0
				then relateSame ctx same t s n efftbl
				else setSameBinding ctx same t op1 efftbl
		  | Write v ->	if (String.compare (fst v) op1) == 0 
				then relateSame ctx same t s (fst v) efftbl
				else setSameBinding ctx same t op1 efftbl

(* Sets same binding.
ctx	- context
same	- z3 function declaration for sameobject
oplist	- list of all instructions
prgvar	- unique program variables
efftbl	- hashtable for effects. *)
let rec assertSameBinding ctx same oplist prgvar efftbl = 
	match prgvar with 
	| [] -> []
	| h::t -> List.append (assertSameBinding ctx same oplist t efftbl) 
			(setSameBinding ctx same oplist h efftbl)


let rec makeOrOfVal ctx frval iand andlist =
	match andlist with 
	| [] -> (let elem = snd iand in mk_eq ctx frval elem) 
	| h::t -> let elem = snd h in 
		  let eq = mk_eq ctx frval elem in 
		  mk_or ctx [eq;(makeOrOfVal ctx frval iand t)]

let rec addVisRel ctx vis rval rd wrts efftbl velse = 
	match wrts with 
	| [] -> []
	| h::t -> match h with (s1,e1) -> 
		  let esort = Integer.mk_sort ctx in 
		  let efvar = (Expr.mk_const ctx 
				(Symbol.mk_string ctx ("e"^s1))) esort in
		  let eff1 = Hashtbl.find efftbl (fst rd) in
		  let eff2 = Hashtbl.find efftbl s1 in
		  let f2 = mk_app ctx rval [eff2] in
		  let f3 = mk_app ctx vis [eff2;eff1] in
		  let fite = mk_ite ctx f3 f2 velse in
		  ((mk_eq ctx efvar fite), efvar) :: 
		  (addVisRel ctx vis rval rd t efftbl velse)

let rec getVisWrites ctx vis rval rd oplist efftbl velse = 
	match oplist with 
	| [] -> []
	| h::t -> if (checkVar (snd rd) (snd h))
		  then List.append (getVisWrites ctx vis rval rd t efftbl velse) 
			(addVisRel ctx vis rval rd (h::[]) efftbl velse)
		  else (getVisWrites ctx vis rval rd t efftbl velse)

(* Adding vis relations for reads to writes in other sessions. *)
let rec addVisOther ctx vis rval rd sid wrlist efftbl velse = 
	match wrlist with 
	| [] -> []
	| h::t -> if h.sid != sid 
		  then List.append (addVisOther ctx vis rval rd sid t efftbl velse)
			(getVisWrites ctx vis rval rd h.oper efftbl velse)
		  else  (addVisOther ctx vis rval rd sid t efftbl velse)

let rec retEquations eqset = 
	match eqset with 
	| [] -> [] 
	| h::t -> (fst h) :: (retEquations t)

let setVisRelations ctx vis rval init rd sid ownwrt wrlist efftbl =
	let inwrts = Hashtbl.find_all ownwrt rd in 	
	let len = List.length inwrts in  
	let incond = List.hd (List.rev inwrts) in
	let velse = (	match incond with (s,op) -> 
		   	match op with
			| Read n -> Integer.mk_numeral_i ctx 0
			| Write v -> Integer.mk_numeral_i ctx (snd v)) in
	let wrset = (	if len > 1 
			then let wrts = List.tl (List.rev inwrts) in
			     addVisRel ctx vis rval rd wrts efftbl velse
			else 	[]) in
        
	let othasrt = addVisOther ctx vis rval rd sid wrlist efftbl velse in
	let cwset = List.append wrset othasrt in	
	let eff1 = Hashtbl.find efftbl (fst rd) in
 	let f2 = mk_app ctx rval [eff1] in
	let anset = (if (List.length cwset) == 0 
		    then [(mk_eq ctx f2 velse)]
		    else (if (List.length cwset) == 1 
			  then (let evar = snd (List.hd cwset) in
				let eq = mk_eq ctx f2 evar in
				let elem = fst (List.hd cwset) in [elem;eq])
			  else (let orlst = (makeOrOfVal ctx f2 (List.hd cwset) 
					(List.tl cwset)) in  
				let vislst = retEquations cwset in 
				orlst :: vislst))) in 
	anset

(*
ctx	- context
vis	- z3 function declaration for vis.
rval	- z3 function declaration for rval (return value).
init	- initial condition
totops	- list of all operations
ownwrt	- hashtable of reads consisting of same session writes (use chains).
wrlist	- session-wise list of all writes.
efftbl	- hashtable of effects. 
sidtb	- effect to session-id hashtable. *)
let rec assertVisRel ctx vis rval init totops ownwrt wrlist efftbl sidtb = 
	match totops with
	| [] -> []
	| h::t -> List.append (assertVisRel ctx vis rval init t ownwrt wrlist efftbl sidtb) 
		 (match h with (s,op) ->
		  match op with 
		  | Read s -> let sid = Hashtbl.find sidtb h in
			setVisRelations ctx vis rval init h sid ownwrt wrlist efftbl
		  | _ -> [])


