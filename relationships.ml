open Printf
open RwOperations
open ContractLang

type relSameSession = {
	op1: taggedOper;
	op2: taggedOper;
	sameobj: bool;
	vis: bool;
	sid: int;
}

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

let extractStuff test = 
	createRelations test.pg

