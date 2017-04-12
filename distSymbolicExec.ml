open Printf
open RwOperations
(*open Distz3Code*)


let findVarInOper top = 
	match top with (s,rw) ->
	match rw with 
	| Read x -> x
	| Write (s,v) -> s

(* Get the list of program variables used in a session. *)
let rec findVarInSess stmts =
	match stmts with 
	| [] -> []
	| h::t -> List.append ( match h with 
		  | TagOper top -> [findVarInOper top]
		  | IfElse ifst -> 
			let ivar = findVarInOper ifst.ifrd in
			let tvar = findVarInSess ifst.thenwr in 
			let evar = findVarInSess ifst.elsewr in 
			(List.append (ivar::tvar) evar) ) 
		  (findVarInSess t)

(* List of program variables in the Litmus test. *)
let rec findProgVar prog = 
	match prog with 
	| [] -> []
	| h::t -> List.append (findProgVar t) 
			(findVarInSess h.oper)


(* Adding initial constraints as Write instruction to the deftb. *)
let rec addInit init deftb = 
	match init with 
	| [] -> deftb
	| h::t -> match h with (s,v) -> 
		  (Hashtbl.add deftb s ("0"^s, Write h);
		  addInit t deftb)

(* For each read constructs a list of writes which precede it in SO. 
sesslst	- list of all sessions.
(deftb,usetb) - hashtables for storing use chains (preceding writes). *)
let rec getSameSessWrites sesslst (deftb,usetb) init prgvar = 
	match sesslst with 
	| [] -> (deftb,usetb)
	| h::t -> (Hashtbl.reset deftb; 
		  let ndtbl = addInit init deftb in 
		  let htbs = useChains h.oper (ndtbl,usetb) prgvar in 
		  getSameSessWrites t (fst htbs, snd htbs) init prgvar)


let getOperWrites top stm =
	match top with (s,op) ->
	match op with 
	| Read s -> []
	| Write v -> [stm]


(* Get a list of session wise writes. *)
let rec getWrites stlist = 
	match stlist with 
	| [] -> []
	| h::t -> List.append (
		  match h with
		  | TagOper top -> (getOperWrites top h) 
		  | IfElse ifst -> List.append (getWrites ifst.thenwr) 
						(getWrites ifst.elsewr) )
		  (getWrites t)

let getSession sess = 
	{sid=sess.sid; oper=getWrites sess.oper}

(* Constructs a list of all writes in a session. 
sesslst	- list of all sessions. *)
let rec getWritesInSess sesslst = 
	match sesslst with 
	| [] -> []
	| h::t -> getSession h :: getWritesInSess t


let symbExecution test contrct = 
	let totops = getAllOperators test.pg in (* Get total effects. *)
	let totins = List.length totops in	(* Count of total effects. *)
	let allvar = findProgVar test.pg in 	
	let prgvar = List.sort_uniq compare allvar in
	let usehtb = Hashtbl.create totins in
	let defhtb = Hashtbl.create totins in
	(* Latest write comes last in the list. *)
	let ownwrt = getSameSessWrites test.pg (defhtb,usehtb) test.init prgvar in
	let wrlist = getWritesInSess test.pg in (* Get writes in each session. *)
	pp_program wrlist
(*	distZ3Code test wrlist (snd ownwrt) prgvar totops totins contrct
*)	
