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
op1	- instruction for effect1 *)
(* Extra but correct bindings being generated. 
No use of trasitivity property then. *)
let rec relateSo ctx so op1 oplist efftbl =
	match oplist with
	| [] -> []
	| h::t -> match op1 with (s1,opr1) -> 
		  match h with (s2,opr2) -> 
		  if checkVar opr1 opr2 
		  then	let eff1 = Hashtbl.find efftbl s1 in
			let eff2 = Hashtbl.find efftbl s2 in
			let fapp = mk_app ctx so [eff1;eff2] in 
			(mk_eq ctx fapp (mk_true ctx)) :: 
			relateSo ctx so op1 t efftbl
		  else	relateSo ctx so op1 t efftbl

let rec setSoBinding ctx so oplist efftbl =
	match oplist with 
	| [] -> []
	| h::t -> List.append (setSoBinding ctx so t efftbl) 
				(relateSo ctx so h t efftbl)


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


(* VIS relations. *)
(* Makes vis implication. 
wr	- The effect in visibility relation with read effect. *)
let makeVisImply ctx vis rval rd wr ieff efftbl = 
	let eff1 = Hashtbl.find efftbl (fst rd) in
	let eff2 = Hashtbl.find efftbl (fst wr) in
	let fvis = mk_app ctx vis [eff2;eff1] in
	let fval = mk_app ctx rval [eff2] in
	let eq = mk_eq ctx ieff fval in
	let imply = mk_implies ctx eq fvis in imply

(*
rd	- read effect
ieff	- temporary effect variable
totwrts	- set of all writes. *)
let rec addAllVis ctx vis rval rd ieff totwrts efftbl = 
	match totwrts with 
	| [] -> [] 
	| h::t -> (makeVisImply ctx vis rval rd h ieff efftbl) :: 
			(addAllVis ctx vis rval rd ieff t efftbl)

(* equates all rvals. 
wr	- the write effect in visibility relation with read effect. *)
let makeRvals ctx rval ieff wr efftbl = 
	let eff2 = Hashtbl.find efftbl (fst wr) in
	let fval = mk_app ctx rval [eff2] in
	mk_eq ctx ieff fval

(*
ieff	- temporary effect variable.
wrhd	- write at the head of the write list.
wrset	- remaining writes in the writelist. *)
let rec addAllRval ctx rval ieff velse wrset efftbl = 
	match wrset with 
	| [] -> mk_eq ctx ieff velse
	| h::t -> let pr = makeRvals ctx rval ieff h efftbl in 
		  mk_or ctx [pr; (addAllRval ctx rval ieff velse t efftbl)]

(* Gets all the writes. *)
let rec getVisWrites rd oplist = 
	match oplist with 
	| [] -> []
	| h::t -> if (checkVar (snd rd) (snd h))
		  then h :: (getVisWrites rd t)
		  else (getVisWrites rd t)

let rec addVisOther rd sid wrlist = 
	match wrlist with 
	| [] -> []
	| h::t -> List.append (addVisOther rd sid t) (
		  if h.sid != sid 
		  then	(getVisWrites rd h.oper) 
		  else  [])

(* Makes negation of all the vis. 
wr	- the write effect in visibility relation with read effect. *)
let makeNotVis ctx vis rd wr efftbl = 
	let eff1 = Hashtbl.find efftbl (fst rd) in
	let eff2 = Hashtbl.find efftbl (fst wr) in
	let fvis = mk_app ctx vis [eff2;eff1] in
	mk_not ctx fvis

(*
wrhd	- write at the head of the write list.
wrlist	- remaining writes in the writelist. *) 
let rec allVisNot ctx vis rd wrhd wrlist efftbl = 
	match wrlist with 
	| [] -> makeNotVis ctx vis rd wrhd efftbl
	| h::t -> let exp =  makeNotVis ctx vis rd h efftbl in 
		  mk_and ctx [exp; (allVisNot ctx vis rd wrhd t efftbl)]


let setVisRelations ctx vis rval init rd sid ownwrt wrlist efftbl =
	let inwrts = Hashtbl.find_all ownwrt rd in 	
	let len = List.length inwrts in  
	let incond = List.hd (List.rev inwrts) in
	let velse = (	match incond with (s,op) -> 
		   	match op with
			| Read n -> Integer.mk_numeral_i ctx 0
			| Write v -> Integer.mk_numeral_i ctx (snd v)) in
	let wrset = (	if len > 1 
			then List.tl (List.rev inwrts)
			else []) in 
	let othrwrt = addVisOther rd sid wrlist in 
	let totwrts = List.append wrset othrwrt in

	let sint = Integer.mk_sort ctx in	
	let ieff = (Expr.mk_const ctx (Symbol.mk_string ctx ("e"^(fst rd))) sint) in 
	let orwrts = (	if (List.length totwrts) > 1 
		     	then 	let thd = (List.hd totwrts) in 
				let ttl = (List.tl totwrts) in
				let andrval = (addAllRval ctx rval ieff 
							velse totwrts efftbl) in
				let vislist = addAllVis ctx vis rval rd ieff 
							totwrts efftbl in 
				let effs = allVisNot ctx vis rd thd ttl efftbl in 
				let feq = mk_eq ctx ieff velse in		
				let iff = mk_iff ctx feq effs in 
				let rdeq = makeRvals ctx rval ieff rd efftbl in
				(iff :: andrval :: rdeq :: vislist) 
			else 	if (List.length totwrts) > 0  
				then let thd = (List.hd totwrts) in
				     let viseq = makeVisImply ctx vis rval rd 
								thd ieff efftbl in
(* try mk_iplies on velse*)	     let eff = makeNotVis ctx vis rd thd efftbl in
				     let feq = mk_eq ctx ieff velse in		
				     let imply = mk_and ctx [eff; feq] in 
				     let rdeq = makeRvals ctx rval ieff rd efftbl in	
				     [imply;rdeq;viseq]

				else (mk_eq ctx ieff velse) :: [] ) in
	orwrts
	

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


