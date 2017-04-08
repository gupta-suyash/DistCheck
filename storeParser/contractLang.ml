open Printf
open RwOperations

type idpair = string *  string

type relation = 
| Vis
| So 
| Sameobj
| Union of relation * relation
| Inter of relation * relation
| Rplus of relation

type property = 
| Patom of relation * idpair
| Pand of property * property
| Por of property * property
| Pimply of property * property


type opType = 
| R | W | RW

type parameter = string * opType

type contract = {
	param: parameter list;
	prp: property;
}


type stsem = contract list

(* Print methods *)

let pp_idpair ip = printf "(%s,%s)" (fst ip) (snd ip)


let pp_optype otyp = 
	match otyp with
	| R -> "R"
	| W -> "W"
	| RW -> "A"

let pp_parameter param = 
	printf "%s:%s" (fst param) (pp_optype (snd param))


let rec pp_relation rel = 
	match rel with
	| Vis -> printf "vis"
	| So ->  printf "so"
	| Sameobj -> printf "sameobj"
	| Union (rel1,rel2) -> pp_relation rel1; printf " v "; 
				pp_relation rel2
	| Inter (rel1,rel2) -> pp_relation rel1; printf " ^ "; 
				pp_relation rel2
	| Rplus rel -> pp_relation rel; printf "+"

let rec pp_plist plist = 
	match plist with 
	| [] -> printf ""
	| h::t -> pp_parameter h; printf ","; pp_plist t

let rec pp_prop prop = 
	match prop with
	| Patom (rel,ipair) -> pp_relation rel; printf " "; pp_idpair ipair
	| Pand (p1,p2) -> pp_prop p1; printf "&&"; pp_prop p2 
	| Por (p1,p2) -> pp_prop p1; printf "||"; pp_prop p2
	| Pimply (p1,p2) -> pp_prop p1; printf "->"; pp_prop p2


let pp_contract ctr = 
	printf "forall("; pp_plist ctr.param; printf ")."; 
	pp_prop ctr.prp

let rec pp_st ast = 
	match ast with
	| [] -> printf ""
	| h::t -> pp_contract h; printf "\n"; pp_st t
