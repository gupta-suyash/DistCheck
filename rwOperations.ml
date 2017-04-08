open Printf

(* Variable to value mapping. *)
type valmap = string * int

(* Type of Read or Write operation *)
type rwop = 
| Read of string
| Write of valmap

(* taggedOper = a Rx *)
type taggedOper = string * rwop

(* Session, a collection of operations *)
type session = {
	sid : int;
	oper: taggedOper list;
}

(* Program is a list of operations. *)
type program = session list

(* Initial Condition *)
type initial = valmap list

(* Constraint Info *)
type prop =
| Atom of string * valmap 
| Not of prop
| And of prop list
| Or of prop list
| Implies of prop * prop

type constr =
| ForallStates of prop
| ExistsStates of prop
| NotExistsState of prop

(* Distributed testcase *)
type code = {
	init: initial;
	pg: program;
	cns: constr;
}


(* Methods on taggedOper. *)
let compareSt x y = if (String.compare x y) == 0 
			then true else false

let checkVar op1 op2 = 
	match op1,op2 with
	| Read x, Read y  	| Read x, Write (y,_) 
	| Write (x,_), Read y 
	| Write (x,_), Write (y,_) -> compareSt x y 
	
let sameTagOper op1 op2 = 
	if (compare (fst op1) (fst op2)) == 0 
		then true else false

let rec getIndex allOps op index = 
	match allOps with 
	| [] -> 0
	| h::t -> if (sameTagOper h op) 
			then index else (getIndex t op (index+1))

(* Generating Hash index table for all operations. *)
let rec addToHashTable allOps hashtb count = 
	match allOps with 
	| [] -> hashtb
	| h::t -> (Hashtbl.add hashtb h count; 
			addToHashTable t hashtb (count+1))

(* Single list of all operations. *)
let rec getAllOperators prog = 
	match prog with
	| [] -> []
	| h::t -> List.append (getAllOperators t) h.oper

(* Add initial condition as Write operations, named as "i0,i1...". *)
let rec addInitialCond init oplist count = 
	match init with 
	| [] -> oplist
	| h::t -> (("i" ^ (string_of_int count)), (Write h)) :: 
			(addInitialCond t oplist (count+1))

(* Make use chains, which tell all writes in same session. 
oplist 	- list of all the defs for a read, that is set of writes.
op	- the specific read
usetb	- hashtable for storing reads. *)
let rec addAllToTbl oplist op usetb = 
	match oplist with 
	| [] -> usetb
	| h::t -> (Hashtbl.add usetb op h;
			addAllToTbl t op usetb) 

(* Constructs def/use chains. 
oplist - set of effects.
(deftb,usetb) - hashtables for storing def/use chains. *) 	 
let rec useChains oplist (deftb,usetb) = 
	match oplist with 
	| [] -> (deftb,usetb)
	| h::t -> useChains t (
		  match h with (s,op) ->
		  match op with 
		  | Read s -> (deftb, addAllToTbl 
				(List.rev (Hashtbl.find_all deftb s)) h usetb)
		  | Write v -> (Hashtbl.add deftb (fst v) h; (deftb,usetb)))

(* Creating a effect to session-id hashtable for quicker acces. *)
let rec addEffToSess sid oplist hashtb = 
	match oplist with 
	| [] -> hashtb
	| h::t -> (Hashtbl.add hashtb h sid; addEffToSess sid t hashtb)

let rec createEfftSessMap prog hashtb =  
	match prog with 
	| [] -> hashtb
	| h::t -> createEfftSessMap t (addEffToSess h.sid h.oper hashtb)


(* Print methods *)

let pp_valmap vmap =  
	match vmap with (var,value) -> printf "%s=%d" var value

let pp_rwop oper = 
	match oper with 
	| Read var -> printf "Read %s" var
	| Write vmap -> printf "Write "; pp_valmap vmap

let pp_taggedOper toper =
	match toper with (s,oper) -> (printf "%s:" s; pp_rwop oper)

let pp_session_id sid = printf "Session %d\n" sid

let rec pp_session_opers oplist = 
	match oplist with 
	| [] -> printf ""
	| h :: t -> (pp_taggedOper h; printf "\n"; 
			pp_session_opers t) 

let pp_session sess = 
	pp_session_id sess.sid;
	pp_session_opers sess.oper	

let rec pp_program prog = 
	match prog with 
	| [] -> printf "";
	| h::t -> (pp_session h; printf "---\n"; pp_program t)

let rec pp_initial initmap = 
	match initmap with 
	| [] -> printf ""
	| h :: t -> (pp_valmap h; pp_initial t)

let rec pp_prop p = 
	match p with 
	| Atom (i,v) -> printf "%s:" i; pp_valmap v
	| Not v -> pp_not v
	| And v -> pp_and v
	| Or v -> pp_or v
	| Implies (v1,v2) -> pp_implies (v1,v2)
and pp_not p = 
	(printf "~"; pp_prop p)
and pp_and p = 
	match p with 
	| [] -> printf ""
	| h::t -> (pp_prop h; printf "&"; pp_and t)
and pp_or p = 
	match p with 
	| [] -> printf ""
	| h::t -> (pp_prop h; printf "|"; pp_or t)
and pp_implies p = 
	match p with (p1,p2) -> (pp_prop p1; printf "->"; pp_prop p2)

let pp_constr cns = 
	match cns with 
	| ForallStates p -> (printf "forall: "; pp_prop p) 
	| ExistsStates p -> (printf "exists: "; pp_prop p)
	| NotExistsState p -> (printf "~ exists: "; pp_prop p)

let pp_code ast = 
	printf "Testcase:\n";
	pp_initial ast.init; 
	pp_program ast.pg;
	pp_constr ast.cns

(* Prints all the strings in a list. *)
let rec pp_listOfString allvar = 
	match allvar with
	| [] -> printf ""
	| h::t -> (printf "%s " h; pp_listOfString t)

(* Prints use chains for the reads in the oplist. *)
let rec pp_use_chains oplist usehtb = 
	match oplist with 
	| [] -> printf ""
	| h::t -> match h with (s,op) ->
		  match op with 
		  | Read s -> (pp_taggedOper h; printf " --> "; 
				pp_taggedOper (Hashtbl.find usehtb h); 
				printf "\n"; pp_use_chains t usehtb)
		  | Write v -> pp_use_chains t usehtb

