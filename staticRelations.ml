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


(* Adding Vis and rel -> (and (= (rval a) (rval b)) (vis b a)) 
ctx	- context
vis	- z3 function declaration for vis.
rval	- z3 function declaration for rval (return value).
rd	- read instruction
wrts	- preceeding writes of the read.
efftbl	- hashtable of effects. *)
let rec addVisRel ctx vis rval rd wrts efftbl = 
	match wrts with 
	| [] -> []
	| h::t -> match h with (s1,e1) -> 
		  let eff1 = Hashtbl.find efftbl (fst rd) in
		  let eff2 = Hashtbl.find efftbl s1 in
		  let f1 = mk_app ctx rval [eff1] in
		  let f2 = mk_app ctx rval [eff2] in
		  let f3 = mk_app ctx vis [eff2;eff1] in
		  let f4 = mk_true ctx in 
		  let eqval = mk_eq ctx f1 f2 in 
		  let eqvis = mk_eq ctx f3 f4 in
		  mk_and ctx [eqval;eqvis] :: 
		  (addVisRel ctx vis rval rd t efftbl)

let rec getVisWrites ctx vis rval rd oplist efftbl = 
	match oplist with 
	| [] -> []
	| h::t -> if (checkVar (snd rd) (snd h))
		  then List.append (getVisWrites ctx vis rval rd t efftbl) 
			(addVisRel ctx vis rval rd (h::[]) efftbl)
		  else (getVisWrites ctx vis rval rd t efftbl)

(* Adding vis relations for reads to writes in other sessions. *)
let rec addVisOther ctx vis rval rd sid wrlist efftbl = 
	match wrlist with 
	| [] -> []
	| h::t -> if h.sid != sid 
		  then List.append (addVisOther ctx vis rval rd sid t efftbl)
			(getVisWrites ctx vis rval rd h.oper efftbl)
		  else  (addVisOther ctx vis rval rd sid t efftbl)

let rec mkOtherAnd ctx vis rval eff1 rd otrwrt efftbl eq = 
	match otrwrt with 
	| [] -> eq
	| h::t -> if checkVar (snd rd) (snd h) 
		  then (match h with (s,e) ->
		  	let eff2 = Hashtbl.find efftbl s in
		  	let f = mk_app ctx vis [eff2;eff1] in 
		  	let nf = mk_not ctx f in
		  	let andeff = mkOtherAnd ctx vis rval eff1 rd t efftbl eq in 
		  	mk_and ctx [nf;andeff])
		  else mkOtherAnd ctx vis rval eff1 rd t efftbl eq


(* And a set of relations
eq	- the z3 eq statement created earlier. 
ntwrt	- list of relatons. *)
let rec mkAllAnd ctx eq ntwrt = 
	match ntwrt with 
	| [] -> eq
	| h::t -> mk_and ctx [h;(mkAllAnd ctx eq t)]


(* Adding Vis rel -> (= (vis b a) false) 
vis	- z3 function declaration for vis.
rd	- read instruction
wrts	- preceeding writes of the read.
efftbl	- hashtable of effects. *)
let rec addNotVisRel ctx vis rd wrts efftbl = 
	match wrts with 
	| [] -> []
	| h::t -> match h with (s1,e1) -> 
		  let eff1 = Hashtbl.find efftbl (fst rd) in
		  let eff2 = Hashtbl.find efftbl s1 in
		  let f1 = mk_app ctx vis [eff2;eff1] in
		  let f2 = mk_false ctx in 
		  (mk_eq ctx f1 f2 ::
		  addNotVisRel ctx vis rd t efftbl)


let rec addNotVisOtherSess ctx vis rd oplist efftbl = 
	match oplist with 
	| [] -> [] 
	| h::t -> if checkVar (snd rd) (snd h) 
		  then List.append (addNotVisOtherSess ctx vis rd t efftbl) 
				(addNotVisRel ctx vis rd [h] efftbl)
		  else (addNotVisOtherSess ctx vis rd t efftbl)

let rec addNotOtherVis ctx vis rd sid wrlist efftbl = 
	match wrlist with 
	| [] -> []
	| h::t -> if h.sid != sid 
		  then List.append (addNotOtherVis ctx vis rd sid t efftbl) 
				(addNotVisOtherSess ctx vis rd h.oper efftbl)
		  else (addNotOtherVis ctx vis rd sid t efftbl)

 
(* Sets all the static vis relations
vis	- z3 function declaration for vis.
rval	- z3 function declaration for rval (return value).
init	- initial condition
rd	- read instruction
sid	- session id for read effect.
ownwrt	- hashtable of reads consisting of same session writes (use chains).
wrlist	- session-wise list of all writes.
efftbl	- hashtable of effects. *)
let setVisRelations ctx vis rval init rd sid ownwrt wrlist efftbl = 
	let inwrts = Hashtbl.find_all ownwrt rd in 	
	let len = List.length inwrts in  
	let wrset = (	if len > 1 
			then	let wrts = List.tl (List.rev inwrts) in
				addVisRel ctx vis rval rd wrts efftbl
			else 	[]) in 
	let othasrt = addVisOther ctx vis rval rd sid wrlist efftbl in 
	let cwset = List.append wrset othasrt in 
	 
	let initwrt = List.hd (List.rev inwrts) in
	let eff = Hashtbl.find efftbl (fst rd) in
	let fapp = mk_app ctx rval [eff] in 
	let eq = mk_eq ctx fapp (
		match initwrt with (s,op) -> 
		match op with
		| Read n -> Integer.mk_numeral_i ctx 0
		| Write v -> Integer.mk_numeral_i ctx (snd v)) in 
	let ntwrt1 = (	if len > 1
			then let wrts = List.tl (List.rev inwrts) in
				addNotVisRel ctx vis rd wrts efftbl
			else []) in 

	let ntwrt2 = addNotOtherVis ctx vis rd sid wrlist efftbl in 
	let ntwrt = List.append ntwrt1 ntwrt2 in
	let visinit = mkAllAnd ctx eq ntwrt in

	let aset = visinit :: cwset in
	let wset = (  if (List.length aset) == 1 
			then aset
			else [makeOrOfAnd ctx (List.hd aset) (List.tl aset)]) in
	wset


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


