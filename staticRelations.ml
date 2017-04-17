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

(* Sets Not so relationship between the statements in the then and 
else branches. *)
let setNotSoOper ctx so top1 top2 efftbl = 
	match top1 with (s1,opr1) -> 
	match top2 with (s2,opr2) -> 
	if checkVar opr1 opr2 
	then	let eff1 = Hashtbl.find efftbl s1 in
		let eff2 = Hashtbl.find efftbl s2 in
		let fapp1 = mk_app ctx so [eff1;eff2] in 
		let fapp2 = mk_app ctx so [eff2;eff1] in
		let eq1 = mk_eq ctx fapp1 (mk_false ctx) in
		let eq2 = mk_eq ctx fapp2 (mk_false ctx) in
		[eq1;eq2]
	else []

let rec setNotSoAll ctx so top1 elist efftbl = 
	match elist with 
	| [] -> [] 
	| h::t -> List.append ( match h with 
		  | TagOper top2 -> setNotSoOper ctx so top1 top2 efftbl
		  | IfElse ifst -> 
			let scond = setNotSoOper ctx so top1 ifst.ifrd efftbl in
			let tstm = setNotSoAll ctx so top1 ifst.thenwr efftbl in
			let estm = setNotSoAll ctx so top1 ifst.elsewr efftbl in
			scond @ tstm @ estm )
		  (setNotSoAll ctx so top1 t efftbl)

let rec setNotSo ctx so tlist elist efftbl = 
	match tlist with 
	| [] -> []
	| h::t -> List.append ( match h with 
		  | TagOper top -> setNotSoAll ctx so top elist efftbl
		  | IfElse ifst -> 
			let scond = setNotSoAll ctx so ifst.ifrd elist efftbl in
			let tstm = setNotSo ctx so ifst.thenwr elist efftbl in
			let estm = setNotSo ctx so ifst.elsewr elist efftbl in
			scond @ tstm @ estm )
		  (setNotSo ctx so t elist efftbl)


(* Asserts forall effect2, (so effect1 effect2) = true (if possible) 
op1	- instruction for effect1 *)
let setSoTagOper ctx so top1 top2 efftbl = 
	match top1 with (s1,opr1) -> 
	match top2 with (s2,opr2) -> 
	if checkVar opr1 opr2 
	then	let eff1 = Hashtbl.find efftbl s1 in
		let eff2 = Hashtbl.find efftbl s2 in
		let fapp = mk_app ctx so [eff1;eff2] in 
		[ mk_eq ctx fapp (mk_true ctx) ]
	else []

(* Extra but correct bindings being generated. 
No use of trasitivity property then. *)
let rec relateSo ctx so op1 stlist efftbl =
	match stlist with
	| [] -> []
	| h::t -> List.append ( match h with 
		  | TagOper top -> setSoTagOper ctx so op1 top efftbl
		  | IfElse ifst -> 
			let scond = setSoTagOper ctx so op1 ifst.ifrd efftbl in
			let tstm = relateSo ctx so op1 ifst.thenwr efftbl in
			let estm = relateSo ctx so op1 ifst.elsewr efftbl in
			scond @ tstm @ estm )
		  (relateSo ctx so op1 t efftbl)

let rec setSoOutBlock ctx so ownstm othstm efftbl = 
	match ownstm with 
	| [] -> [] 
	| h::t -> List.append (setSoOutBlock ctx so t othstm efftbl) (
		  match h with 
		  | TagOper top -> relateSo ctx so top othstm efftbl
		  | IfElse ifst ->
			let ilist = relateSo ctx so ifst.ifrd othstm efftbl in 
			let tlist = setSoOutBlock ctx so ifst.thenwr 
							othstm efftbl in
			let elist = setSoOutBlock ctx so ifst.elsewr 
							othstm efftbl in
			List.append (List.append ilist tlist) elist )
			

let rec setSoBinding ctx so oplist efftbl =
	match oplist with 
	| [] -> []
	| h::t -> List.append (setSoBinding ctx so t efftbl) (
		  match h with 
		  | TagOper top -> relateSo ctx so top t efftbl
		  | IfElse ifst -> 
			let alist = List.append 
					(List.append ifst.thenwr ifst.elsewr) t in
			let icond = relateSo ctx so ifst.ifrd alist efftbl in 
			let tostm = setSoBinding ctx so ifst.thenwr efftbl in 
			let tdstm = setSoOutBlock ctx so ifst.thenwr t efftbl in
			let eostm = setSoBinding ctx so ifst.elsewr efftbl in 
			let edstm = setSoOutBlock ctx so ifst.elsewr t efftbl in
			let ntstm = setNotSo ctx so ifst.thenwr 
						ifst.elsewr efftbl in
			icond @ tostm @ tdstm @ eostm @ edstm @ ntstm)


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
	| h::t -> match h with 
		  | TagOper top -> if (checkVar (snd rd) (snd top))
		 	 	   then top :: (getVisWrites rd t)
		  		   else (getVisWrites rd t)
		  | IfElse st -> (getVisWrites rd t) (* Should not come here. *)

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
				     let andrval = (addAllRval ctx rval ieff 
							velse [thd] efftbl) in
				     let viseq = makeVisImply ctx vis rval rd 
								thd ieff efftbl in
(* try mk_iplies on velse*)	     let eff = makeNotVis ctx vis rd thd efftbl in
				     let feq = mk_eq ctx ieff velse in		
				     let iff = mk_iff ctx feq eff in 
				     let rdeq = makeRvals ctx rval ieff rd efftbl in	
				     [iff;andrval;rdeq;viseq]

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


(* No Vis relationships. *)
let rec makeAndRval ctx rhd rtl = 
	match rtl with 
	| [] -> rhd
	| h::t -> mk_and ctx [h;(makeAndRval ctx rhd t)]


let rec setNoRvalSess ctx rval top1 sess efftbl flag = 
	match sess with
	| [] -> []
	| h::t -> match top1 with (s1,op1) ->
		  let eff1 = Hashtbl.find efftbl s1 in
		  let fval1 = mk_app ctx rval [eff1] in
		  match h with 
		  | TagOper top2 -> if flag == 1 
				    then match top2 with (s2,op2) ->
					 match op2 with 
					 | Read n -> (setNoRvalSess ctx rval top1 t efftbl flag)
					 | Write v -> let eff2 = Hashtbl.find efftbl s2 in
						      let fval2 = mk_app ctx rval [eff2] in 
						      let eq = mk_eq ctx fval1 fval2 in 
						      let neq = mk_not ctx eq in
						      [neq] @ (setNoRvalSess ctx rval top1 t efftbl flag)
				    else setNoRvalSess ctx rval top1 t efftbl flag 
		  | IfElse ifst ->
			if sameTagOper ifst.ifrd top1
			then	(setNoRvalSess ctx rval top1 t efftbl 0)
			else  	let eqth = setNoRvalSess ctx rval top1 ifst.thenwr efftbl 1 in
				let eqel = setNoRvalSess ctx rval top1 ifst.elsewr efftbl 1 in
				let thlen = List.length eqth in
				let ellen = List.length eqel in

				match ifst.ifrd with (s3,op3) ->
				let effif = Hashtbl.find efftbl s3 in 
				let fval = mk_app ctx rval [effif] in
				let eq = mk_eq ctx fval (Integer.mk_numeral_i ctx ifst.ifval) in 
				
				let thlist = ( 
					if thlen > 1 
					then makeAndRval ctx (List.hd eqth) (List.tl eqth)
					else 	if thlen > 0 
						then List.hd eqth
						else mk_eq ctx fval1 fval1 ) in
				let ellist = ( 
					if ellen > 1 
					then makeAndRval ctx (List.hd eqel) (List.tl eqel)
					else 	if ellen > 0 
						then List.hd eqel
						else mk_eq ctx fval1 fval1 ) in
	
				let ifcond = mk_ite ctx eq ellist thlist in 
				ifcond :: (setNoRvalSess ctx rval top1 t efftbl 0)
			

let rec setNoRval ctx rval top1 prog efftbl = 
	match prog with 
	| [] -> []
	| h::t -> (setNoRvalSess ctx rval top1 h.oper efftbl 0) @ 
			(setNoRval ctx rval top1 t efftbl)
 

let rec assertNotRval ctx rval totops prog efftbl = 
	match totops with 
	| [] -> []
	| h::t -> match h with (s,op) -> 
		  match op with 
		  | Read n -> (setNoRval ctx rval h prog efftbl) @ 
				(assertNotRval ctx rval t prog efftbl)
		  | Write v -> assertNotRval ctx rval t prog efftbl

