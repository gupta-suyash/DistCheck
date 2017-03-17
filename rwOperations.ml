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
| Atom of int * valmap 
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

(* Add operations. *)
let createValmap var value = (var,value)

let setInitial vmap init = vmap :: init 

let createRead var = Read var

let createWrite vmap = Write vmap 

let add_rwop optype vmap = 
	match optype with 
	| "R" -> createRead (fst vmap)
	| "W" -> createWrite vmap
	| _ -> createRead (fst vmap)  (* This case should not occur, throw error *)

let add_taggedOper tag optype vmap = 
	(tag,(add_rwop optype vmap))

let rec sessionExists sid prog = 
	match prog with 
	| [] -> false
	| h::t -> if (compare sid h.sid) == 0 
							then true else sessionExists sid t

let addOperToSession sid tag optype vmap oplist = 
	{sid=sid; oper=((add_taggedOper tag optype vmap) :: oplist)}

let rec modifySession sid tag optype vmap prog = 
	match prog with 
	| [] -> (addOperToSession sid tag optype vmap []) :: []
	| h::t -> if (compare sid h.sid) == 0 
							then (addOperToSession  h.sid tag optype vmap h.oper) :: t
							else h :: (modifySession sid tag optype vmap t)

let createAtom vmap = Atom vmap


(* Print methods *)

let pp_valmap vmap =  
	match vmap with (var,value) -> printf "%s=%d\n" var value

let pp_rwop oper = 
	match oper with 
	| Read var -> printf "%s\n" var
	| Write vmap -> pp_valmap vmap

let pp_taggedOper toper =
	match toper with (s,oper) -> (printf "%s:" s; pp_rwop oper)

let pp_session_id s = printf "%d\n" s.sid

let rec pp_session_opers oplist = 
	match oplist with 
  | [] -> printf "Empty\n"
  | h :: t -> (pp_taggedOper h; pp_session_opers t) 

let rec pp_initial initmap = 
	match initmap with 
  | [] -> printf "Empty\n"
  | h :: t -> (pp_valmap h; pp_initial t)

let rec pp_prop p = 
	match p with 
	| Atom v -> pp_valmap v
	| Not v -> printf ""
	| And v -> pp_and v
	| Or v -> pp_or v
  | Implies (v1,v2) -> (printf "")
and pp_not p = 
	(printf "~"; pp_prop p)
and pp_and p = 
	match p with 
	| [] -> printf ""
	| h::t -> (pp_prop h; printf "/\\"; pp_and t)
and pp_or p = 
	match p with 
	| [] -> printf ""
	| h::t -> (pp_prop h; printf "\\/"; pp_or t)
and pp_implies p = 
	match p with (p1,p2) -> (pp_prop p1; printf "->"; pp_prop p2)

let pp_constr cns = 
	match cns with 
	| ForallStates p -> (printf "forall: "; pp_prop p) 
	| ExistsStates p -> (printf "exists: "; pp_prop p)
	| NotExistsState p -> (printf "~ exists: "; pp_prop p)


