open Printf

type relation = 
| Vis
| So
| Sameobj
| Union of relation * relation
| Inter of relation * relation
| Rplus of relation

type idpair = string *  string

type property = 
| Patom of relation * idpair 
| Por of property * property
| Pand of property * property
| Pimplies of property * property 

type opType = 
| Read | Write | Any

type parameter = string * opType

type contract = {
	param: parameter list;
	prp: property;
}

type stsem = contract list


let pp_st ast = 
	printf "Hello\n" 
