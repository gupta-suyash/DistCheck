open Printf
open RwOperations
open ContractLang

type conInfo = {
	op1name: String;
	op1type: opType;
	op2name: String;
	op2type: opType;
}

let isVis 

let isRel ops rel = 
	match rel with 
	| Vis ip -> isVis ops ip
	| So ip -> isSo ops ip
	| Sameobj ip -> isSame ops ip
	| _ -> true (* TODO *)

let getops param = 
	match param with (x1::x2::t) ->
		{op1name=(fst x1); op1type=(snd x1); 
		 op2name=(fst x2); op2type=(snd x2);}

let restParam param = 
	match param with (x1::t) -> t

let rec relationCheck param rel 
	match rel with 
	| [] -> true
	| h::t ->
		let ops = getOps param in 
		let rem = restParam param in 
		(isRel ops h) && (relationCheck rem t)

let handleProperty vismat param rel ip = 
	if relationCheck param rel 
		then setVis vismat param ip

let setVisMat vismat param prop = 
	match prop with 
	| Patom (rel,ip) -> handleProperty vismat param rel ip 
	| Pand (p1,p2) -> (* TODO *)

let handleContract vismat cntr = 
	setVisMat vismat cntr.param cntr.prp

let parseContracts cntlist vismat = 
	match cntlist with 
	| [] -> vismat
	| h::t -> parseContracts t (handleContract vismat h)

(*
type relDiffSession = {
	op1: taggedOper;
	op2: taggedOper;
	sameobj: bool;
	vis: bool;
	so: int;
}

type relsset = relSameSession list
type reldset = relDiffSession list

type opRelations = {
	relss: relsset;
	relds: reldset;
}


let compareSt x y = if (compare x y) == 0 
			then true else false
let checkVar op1 op2 = 
	match op1,op2 with
	| Read x, Read y  
	| Read x, Write (y,_) 
	| Write (x,_), Read y 
	| Write (x,_), Write (y,_) -> compareSt x y

let rec allPairSame op1 oplist sid = 
	match oplist with
	| [] -> []
	| h::t -> ({op1=op1; op2=h; 
			sameobj=(checkVar (snd op1) (snd h)); vis=false; sid=sid;})
			:: (allPairSame op1 t sid)


let rec addSRelation sid oplist = 
	match oplist with
	| [] -> []
	| h::t -> List.append (addSRelation sid t) 
			(allPairSame h t sid) 


let rec setSameSessionRel (prog: program) : relsset = 
	match prog with
	| [] -> []
	| h::t -> List.append (setSameSessionRel t) 
			(addSRelation h.sid h.oper) 

let rec allPairDiff op1 oplist sid = 
	match oplist with
	| [] -> []
	| h::t -> ({op1=op1; op2=h; 
			sameobj=(checkVar (snd op1) (snd h)); vis=false; so=0;})
			:: (allPairDiff op1 t sid)

let rec addDRelation sid oplist = 
	match oplist with
	| [] -> []
	| h::t -> List.append (addDRelation sid t) 
			(allPairDiff h t sid)


let rec setDiffSessionRel (prog : program) : reldset = 
	match prog with
	| [] -> []
	| h::t -> List.append (setDiffSessionRel t) 
			(addDRelation h.sid h.oper)

let createRelations prog = 
	{relss = (setSameSessionRel prog); relds = (setDiffSessionRel prog);}



(* The testcase is passed at this point. *)
let extractStuff test = 
	createRelations test.pg
*)
