open Printf
open RwOperations

type pairOps = taggedOper * taggedOper
type pairOpList = pairOps list

(* Single list of all operations. *)
let rec getAllOperators prog = 
	match prog with
	| [] -> []
	| h::t -> List.append (getAllOperators t) h.oper

(* Adding same session pairs. *)
let rec add_allSame op oplist = 
	match oplist with 
	| [] -> []
	| h::t -> (op,h) :: (add_allSame op t)

let rec add_same oplist = 
	match oplist with
	| [] -> []
	| h::t -> List.append (add_same t) 
			(add_allSame h t) 

let rec same_sess_pair prog = 
	match prog with
	| [] -> []
	| h::t -> List.append (same_sess_pair t) 
			(add_same h.oper)

(* Sets the SO relationship for each pair of operators in the 
list "samepair" in the matrix "somat". *)
let rec setSo somat allOps samepair = 
	match samepair with 
	| [] -> somat
	| h::t -> 
		let i = getIndex allOps (fst h) 0 in
		let j = getIndex allOps (snd h) 0 in
		(somat.(i).(j) <- 1; setSo somat allOps t)	

(* Sets SameObj relationships for all the operations which 
share the common variable, across sessions, in the matrix "samemat". *)
let rec setSameRel samemat op oplist allOps = 
	match oplist with 
	| [] -> samemat
	| h::t -> if (checkVar (snd op) (snd h))
		  then	let i = getIndex allOps op 0 in
			let j = getIndex allOps h 0 in
			(samemat.(i).(j) <- 1; 
			 samemat.(j).(i) <- 1;
			setSameRel samemat op t allOps)
		  else setSameRel samemat op t allOps 

let rec setSameobj samemat oplist allOps = 
	match oplist with
	| [] -> samemat
	| h::t -> setSameobj (setSameRel samemat h t allOps) 
			t allOps

(* Printing the matrix. *)
let rec pp_row mat allOps count i = 
	match allOps with 
	| [] -> printf "\n"
	| h::t -> (printf "%d " mat.(count).(i);
			pp_row mat t count (i+1))

let rec pp_relmat mat allOps opset count = 
	match allOps with 
	| [] -> printf ""
	| h::t -> (pp_taggedOper h; printf ": "; 
			pp_row mat opset count 0;
			pp_relmat mat t opset (count+1))

(* Print same session pairs. *)
let rec pp_same_sess_pair spair = 
	match spair with
	| [] -> printf ""
	| h::t -> (pp_taggedOper (fst h); printf ",";
			pp_taggedOper (snd h); printf "\n"; 
			pp_same_sess_pair t)		

(* Initial Method for SO. *)
let initialfunction prog =
	let allOps = getAllOperators prog in	(* list of operations *)
	let totalOps = List.length allOps in 
	let samePair = same_sess_pair prog in 	(* list of same session pairs *)
	let imat = Array.make_matrix totalOps totalOps 0 in
	let somat = setSo imat allOps samePair in (* SO matrix. *)
	let jmat = Array.make_matrix totalOps totalOps 0 in
	let samemat = setSameobj jmat allOps allOps in (* SameObj matrix. *)
	pp_relmat samemat allOps allOps 0

let generate_so test =
	initialfunction test.pg 

