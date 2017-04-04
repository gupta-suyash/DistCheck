open Printf
open RwOperations
open Distz3Code

(* Get the list of program variables used in a session. *)
let rec findVarInSess oplist =
	match oplist with 
	| [] -> []
	| h::t -> 
		(match h with (s,rw) -> 
			match rw with 
			| Read x -> x
			| Write (s,v) -> s) :: findVarInSess t	

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
		  (Hashtbl.add deftb s ("i"^s, Write h);
		  addInit t deftb)

(* For each read constructs a list of writes which precede it in SO. 
sesslst	- list of all sessions.
(deftb,usetb) - hashtables for storing use chains (preceding writes). *)
let rec getSameSessWrites sesslst (deftb,usetb) init = 
	match sesslst with 
	| [] -> (deftb,usetb)
	| h::t -> (Hashtbl.reset deftb; 
		  let ndtbl = addInit init deftb in
		  let htbs = useChains h.oper (ndtbl,usetb) in 
		  getSameSessWrites t (fst htbs, snd htbs) init)

(* Get a list of session wise writes. *)
let rec getWrites oplist = 
	match oplist with 
	| [] -> []
	| h::t -> match h with (s,op) ->
		  match op with 
		  | Read s -> getWrites t
		  | Write v -> h :: getWrites t

let rec getSession sess = 
	{sid=sess.sid; oper=getWrites sess.oper}

(* Constructs a list of all writes in a session. 
sesslst	- list of all sessions. *)
let rec getWritesInSess sesslst = 
	match sesslst with 
	| [] -> []
	| h::t -> getSession h :: getWritesInSess t


let symbExecution test = 
	let totops = getAllOperators test.pg in (* Get total effects. *)
	let totins = List.length totops in	(* Count of total effects. *)
	let wrlist = getWritesInSess test.pg in (* Get writes in each session. *)
	let usehtb = Hashtbl.create totins in
	let defhtb = Hashtbl.create totins in
	(* Latest write comes last in the list. *)
	let ownwrt = getSameSessWrites test.pg (defhtb,usehtb) test.init in  
	let allvar = findProgVar test.pg in 	
	let prgvar = List.sort_uniq compare allvar in
	distZ3Code test wrlist (snd ownwrt) prgvar totops totins
	
