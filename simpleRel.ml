open Printf
open RwOperations

type relations = {
	op1: taggedOper;
	op2: taggedOper;
	relt: string list;
}

type relationSet = relations list

(* Operation comparison on basis of tags. *)
let sameOper op1 op2 = 
	match op1 with (sid1,oper1) -> 
		match op2 with (sid2,oper2) -> 
			if (compare sid1 sid2) == 0 
				then true
				else false

(* Relation checking methods. *)
let equalRel rel1 rel2 = 
	if (compare rel1 rel2) == 0 
		then true else false

let checkRel rel relList = 
	List.exists (fun x -> equalRel rel x) relList
		  
let rec isRel rel op1 op2 relts = 
	match relts with
	| [] -> false
	| h::t -> if (sameOper h.op1 op1) 
							then if (sameOper h.op2 op2) 
										then if (checkRel rel h.relt) 
													then true else false
										else isRel rel op1 op2 t 
							else isRel rel op1 op2 t 

(* Specific methods for checking relations. *)
let isSo op1 op2 relts = isRel "so" op1 op2 relts

let isSameobj op1 op2 relts = isRel "sameobj" op1 op2 relts
 
(* Adding relations to the common data-structure *)
let setRel rel relt = List.cons rel relt

let appendRelts op1 op2 rel relList relts = 
		List.cons {op1=op1; op2=op2; relt=(setRel rel relList)} relts

(* Takes a data-structure of relations type and returns 
an updated version. *)		
let rec addRel rel op1 op2 relts = 
	match relts with
	| [] -> appendRelts op1 op2 rel [] []
	| h::t -> if (sameOper h.op1 op1) 
							then if (sameOper h.op2 op2) 
										then appendRelts op1 op2 rel h.relt t 
										else h :: (addRel rel op1 op2 t)
							else h :: (addRel rel op1 op2 t)

(* Pretty Printing methods. *)
let rec pp_allRels relList = 
	match relList with 
	| [] -> printf ""
	| h::t -> (printf "%s ," h; pp_allRels t) 

let rec ppRel op1 op2 relts = 
	match relts with
	| [] -> printf "No relation found\n" 
	| h::t -> if (sameOper h.op1 op1) 
							then if (sameOper h.op2 op2) 
										then pp_allRels h.relt
										else ppRel op1 op2 t 
							else ppRel op1 op2 t

