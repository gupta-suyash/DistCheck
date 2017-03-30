open RwOperations
open Seqz3code
open Printf


(* For handling reads we need to make def-use chains, which tell last write 
for the read. *)
let rec defuseChains oplist (deftb,usetb) = 
	match oplist with 
	| [] -> (deftb,usetb)
	| h::t -> defuseChains t (
		  match h with (s,op) ->
		  match op with 
		  | Read s -> (Hashtbl.add usetb h (Hashtbl.find deftb s);
				(deftb,usetb))
		  | Write v -> (Hashtbl.add deftb (fst v) h; 
				(deftb,usetb)))

(* Generate unique temproaries for each instruction 
to be used in Z3. *)
let rec genTemporary oplist hashtb = 
	match oplist with
	| [] -> hashtb
	| h::t -> match h with (s,op) -> 
		genTemporary t ((Hashtbl.add hashtb h ("tmp" ^ s)); hashtb)

(* Get the list of instruction tags used in constraints. *)
let rec readProperty p = 
	match p with 
	| Atom (s,v) -> s :: [] 
	| Not v -> readProperty v 
	| And v -> readAndProp v 
	| Or v -> readOrProp v
	| Implies (v1,v2) -> 
		List.append (readProperty v1) (readProperty v2)
and readAndProp p = 
	match p with 
	| [] -> []
	| h::t -> List.append (readAndProp t) (readProperty h)
and readOrProp p = 
	match p with 
	| [] -> []
	| h::t -> List.append (readOrProp t) (readProperty h) 

let readConstraint cns = 
	match cns with 
	| ForallStates p
	| ExistsStates p
	| NotExistsState p -> readProperty p

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

(* Print methods. *)
let rec pp_temporary oplist hashtb = 
	match oplist with
	| [] -> printf ""
	| h::t -> (pp_taggedOper h; printf " --> %s\n" (Hashtbl.find hashtb h);
			pp_temporary t hashtb) 

let rec pp_use_chains oplist usehtb = 
	match oplist with 
	| [] -> printf ""
	| h::t -> match h with (s,op) ->
		  match op with 
		  | Read s -> (pp_taggedOper h; printf " --> "; 
				pp_taggedOper (Hashtbl.find usehtb h); 
				printf "\n"; pp_use_chains t usehtb)
		  | Write v -> pp_use_chains t usehtb

(* Start. *)
let exploreProg test = 
	let allops = getAllOperators test.pg in
	let totops = addInitialCond test.init allops 0 in 
	let allvar = findProgVar test.pg in 	
	let unqvar = List.sort_uniq compare allvar in 
	(*let tmpins = readConstraint test.cns in 
	let cnsins = List.sort_uniq compare tmpins in *)
	let totins = List.length totops in 
	let inittb = Hashtbl.create totins in
	let allhtb = genTemporary totops inittb in 	
	let usehtb = Hashtbl.create totins in
	let defhtb = Hashtbl.create totins in
	let udeftb = defuseChains totops (defhtb,usehtb) in
	(pp_session_opers totops; printf "\n";
	pp_use_chains totops (snd udeftb); printf "\n";
	pp_temporary totops allhtb; printf "\n";
	seqZ3code allhtb unqvar totops (fst udeftb) (snd udeftb) test)



