open Printf

(* Variable to value mapping. *)
type valmap = string * int


(* Type of Read or Write operation *)
type rwop = 
| Read of string
| Write of valmap (* string * int *)

(* taggedOper = a Rx *)
type taggedOper = string * rwop

(* Session, a collection of operations *)
type session = {
	sid : int;
	oper: taggedOper list;
}

(* Program is a list of sessions. *)
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

let pp_valmap vmap =  
	match vmap with (var,value) -> printf "%s=%d\n" var value

let rec pp_initial initmap = 
	match initmap with 
	| [] -> printf ""
	| h :: t -> (pp_valmap h; pp_initial t)

let pp_code ast = 
	printf "Code is:\n";
	pp_initial ast.init
