open Z3
open Z3.Symbol
open Z3.Sort
open Z3.Expr
open Z3.Boolean
open Z3.Goal
open Z3.Probe
open Z3.Solver
open Z3.Model
open Z3.FuncDecl
open Z3.Enumeration
open Z3.Arithmetic
open Z3.Arithmetic.Integer

open RwOperations
open StaticRelations
open DefinedLemmas
open EncodeConstraint
open EncodeContracts
open TestMethods
open Printf

(* Asserts (ssid effect) == int  --> sid 
ctx 	- context
ssid	- z3 function declaration for ssid
sid	- session id
oplist	- list of operations in a session.
efftbl	- hashtable of all effects.
itble	- stores are session id assertions. *)
let rec setSsid ctx ssid sid oplist efftbl itbl = 
	match oplist with 
	| [] -> itbl
	| h::t -> match h with (s,op) -> 
		  let eff = Hashtbl.find efftbl s in
		  let fapp = mk_app ctx ssid [eff] in 
		  let eq = mk_eq ctx fapp (Integer.mk_numeral_i ctx sid) in 
			   (Hashtbl.add itbl s eq; setSsid ctx ssid sid t efftbl itbl)

(* Calls for creating assertions (ssid effect) == int  --> sid 
ctx 	- context
ssid	- z3 function declaration for ssid
prog	- list of all sessions.
efftbl	- hashtable of all effects.
itble	- stores are session id assertions. *)
let rec assertSsid ctx ssid prog efftbl itbl = 
	match prog with 
	| [] -> itbl
	| h::t -> assertSsid ctx ssid t efftbl 
			(setSsid ctx ssid h.sid h.oper efftbl itbl)

(* Asserts (rval effect) == int --> value 
ctx 	- context
rval	- z3 function declaration for rval
oplist	- list of operations in a session.
efftbl	- hashtable of all effects.
rtbl	- stores are session id assertions. *)
let rec assertRval ctx rval oplist efftbl rtbl = 
	match oplist with 
	| [] -> rtbl
	| h::t -> match h with (s,op) -> 
		  let eff = Hashtbl.find efftbl s in
		  let fapp = mk_app ctx rval [eff] in 
		  match op with 
		  | Read n -> assertRval ctx rval t efftbl rtbl
		  | Write v -> let eq = mk_eq ctx fapp 
				(Integer.mk_numeral_i ctx (snd v)) in 
			(Hashtbl.add rtbl s eq; assertRval ctx rval t efftbl rtbl)  

(* Asserts (sval effect) == symbol -> x,y 
opid	- effect (Read x or Write v)
vlist	- List of all the variable symbols.*)
let rec getEffSymbol opid vlist count = 
	match vlist with 
	| [] -> -1
	| h::t -> if (checkVar (Read (Symbol.get_string h)) opid) 
		  then count else (getEffSymbol opid t (count+1))

(* Calls for creating assertions (sval effect) == symbol -> x,y
ctx 	- context
sval	- z3 function declaration for sval
oplist	- list of operations in a session.
efftbl	- hashtable of all effects.
stbl	- stores all sval equality assertions. 
var	- Enumeration for the program variables.
vsymlst	- symbol list. *)
let rec assertSval ctx sval oplist efftbl stbl var vsymlst = 
	match oplist with 
	| [] -> stbl
	| h::t -> match h with (s,op) ->
		  let eff = Hashtbl.find efftbl s in
		  let fapp = mk_app ctx sval [eff] in
		  let eq = mk_eq ctx fapp 
			   (get_const var (getEffSymbol (snd h) vsymlst 0)) in
		  (Hashtbl.add stbl s eq;   
		  assertSval ctx sval t efftbl stbl var vsymlst)

(* Asserts (oper effect) ==  symbol -> read/write. 
ctx 	- context
oper	- z3 function declaration for oper
oplist	- list of operations in a session.
efftbl	- hashtable of all effects.
otbl	- stores all kind (R/W) assertions. 
kind	- Enumeration for the effect kind (Read/Write). *)
let rec assertOper ctx oper oplist efftbl otbl kind = 
	match oplist with 
	| [] -> otbl
	| h::t -> ((match h with (s,op) ->
		  let eff = Hashtbl.find efftbl s in
		  let fapp = mk_app ctx oper [eff] in
		  match op with 
		  | Read n -> let eq = mk_eq ctx fapp (get_const kind 0) in 
				Hashtbl.add otbl s eq 
		  | Write v -> let eq = mk_eq ctx fapp (get_const kind 1) in 
				Hashtbl.add otbl s eq);
		  assertOper ctx oper t efftbl otbl kind)

(* Declares each instruction as an effect. *)
let rec declareEffects ctx effect oplist tbl =
	match oplist with 
	| [] -> tbl
	| h::t -> match h with (s,op) ->
		  let eff = (Expr.mk_const ctx (Symbol.mk_string ctx s) effect) in 
		  (Hashtbl.add tbl s eff; declareEffects ctx effect t tbl)

(* Returns list consisting a symbol for each program variable. *)
let rec addVarSymbols ctx prgvar = 
	match prgvar with 
	| [] -> []
	| h::t -> Symbol.mk_string ctx h ::
		  addVarSymbols ctx t 


(* Solver. *)
let constSolver ctx gset = 
	(printf "Entered\n"; 
	let g = (mk_goal ctx true false false) in
	printf "Goal made";
 	(Goal.add g gset);
	printf "Goal added";
  	Printf.printf "%s\n" ("Goal: " ^ (Goal.to_string g));
  	(
    	let solver = (mk_solver ctx None) in
    	(List.iter (fun a -> (Solver.add solver [ a ])) (get_formulas g)) ;
    	if (check solver []) != SATISFIABLE then
      		Printf.printf "Failure\n"
    	else
      	(
		Printf.printf "Test passed.\n";
		let gtmod = Solver.get_model solver in 
		match gtmod with
		| None -> Printf.printf "Exception occurred"
		| Some (m) -> Printf.printf "%s\n" (Model.to_string m)
	)))


(* Basic Definitions:
ctx 	- context
prgvar	- unique program variables (x,y,...)
test	- litmus testcase
totops	- all the instructions.
totins	- count of all instructions. *)
let addBasicDecl ctx prgvar test totops totins ownwrt wrlist contrct = 
	(* Enumeration "kind" of effect. *)
	let rsym = Symbol.mk_string ctx "R" in  
	let wsym = Symbol.mk_string ctx "W" in
	let syms = [rsym;wsym] in
	let kind = Enumeration.mk_sort ctx (Symbol.mk_string ctx "kind") syms in 
	(* "Effect" *)
	let effect = Sort.mk_uninterpreted ctx (Symbol.mk_string ctx "effect") in 
	(* oper function. *)
	let domain = [ effect ] in 
	let foper = (mk_string ctx "oper") in 	
	let oper = FuncDecl.mk_func_decl ctx foper domain kind in
	(* rval function. *)
	let sint = Integer.mk_sort ctx in 
	let frval = (mk_string ctx "rval") in	
	let rval = FuncDecl.mk_func_decl ctx frval domain sint in
	(* symbols for each program variable. *)	
	let vsymlst = addVarSymbols ctx prgvar in
	let var = Enumeration.mk_sort ctx (Symbol.mk_string ctx "var") vsymlst in
	(* sval function. *)
	let fsval = (mk_string ctx "sval") in	
	let sval = FuncDecl.mk_func_decl ctx fsval domain var in 	
	(* ssid function. *)
	let fssid = (mk_string ctx "ssid") in	
	let ssid = FuncDecl.mk_func_decl ctx fssid domain sint in
	(* vis function. *)
	let sbool = Boolean.mk_sort ctx in
	let rdomain = [ effect; effect ] in
	let fvis = (mk_string ctx "vis") in 	
	let vis = FuncDecl.mk_func_decl ctx fvis rdomain sbool in
	(* so function. *)
	let fso = (mk_string ctx "so") in 	
	let so = FuncDecl.mk_func_decl ctx fso rdomain sbool in
	(* same function. *)
	let fsame = (mk_string ctx "same") in 	
	let same = FuncDecl.mk_func_decl ctx fsame rdomain sbool in
	(* hb function. *)
	let fhb = (mk_string ctx "hb") in 	
	let hb = FuncDecl.mk_func_decl ctx fhb rdomain sbool in
	(* Effect declarations. *)
	let tbl = Hashtbl.create totins in
	let efftbl = declareEffects ctx effect totops tbl in 
	(* Assert oper effect *)
	let otbl = Hashtbl.create totins in
	let aoper = assertOper ctx oper totops efftbl otbl kind in 
	(* Assert sval effect *)
	let stbl = Hashtbl.create totins in
	let asval = assertSval ctx sval totops efftbl stbl var vsymlst in
	(* Assert rval effect *)
	let rtbl = Hashtbl.create totins in
	let arval = assertRval ctx rval totops efftbl rtbl in 
	(* Assert ssid effect *)
	let itbl = Hashtbl.create totins in
	let assid = assertSsid ctx ssid test.pg efftbl itbl in
	(* Assert static so bindings. *)
	let sobind = assertSoBinding ctx so test.pg efftbl in 
	(* Assert static same bindings. *)
	let samebind = assertSameBinding ctx same totops prgvar efftbl in 
	(* Instruction to session mapping. *)
	let intbl = Hashtbl.create totins in
	let sidtbl = createEfftSessMap test.pg intbl in
	(* Assert static vis bindings. *)
	let visbind = assertVisRel ctx vis rval test.init totops 
			ownwrt wrlist efftbl sidtbl in

let hlist1 = Hashtbl.fold (fun x y z -> y :: z) aoper [] in 
let hlist2 = Hashtbl.fold (fun x y z -> y :: z) asval [] in
let hlist3 = Hashtbl.fold (fun x y z -> y :: z) arval [] in
let hlist4 = Hashtbl.fold (fun x y z -> y :: z) assid [] in
let tlist = List.append hlist1 hlist2 in 
let tlist1 = List.append tlist hlist3 in
let ulist = List.append tlist1 hlist4 in
let ulist2 = List.append ulist sobind in
let ulist3 = List.append ulist2 samebind in
let vlist = List.append ulist3 visbind in

let so_q1 = so_irreflexive ctx effect so in 
let so_q2 = so_same_session ctx effect so ssid in
let so_q3 = so_transitivity ctx effect so in

let same_q1 = same_equal_var ctx effect same sval in 
let same_q2 = same_symmetric ctx effect same in
let same_q3 = same_transitivity ctx effect same in

let vis_q1 = vis_irreflexive ctx effect vis in
let vis_q2 = vis_anti_symmetric ctx effect vis in
let vis_q3 = vis_same ctx effect vis same in

let hb_q1 = hb_irreflexive ctx effect hb in
let hb_q2 = hb_define ctx effect vis so hb in
let hb_q3 = hb_transitivity ctx effect hb in
let hb_q4 = hb_anti_symmetric ctx effect hb in
let hb_all = hb_acyclic ctx effect hb oper vis same rval kind in 


let rels  = [so_q1;so_q2;so_q3;same_q1;same_q2;same_q3;
		vis_q1;vis_q2;vis_q3;hb_q1;hb_q2;hb_q3;hb_q4;hb_all] in
let nvlist = List.append vlist rels in
		 
let cnstr = assertConstraints ctx rval test.cns efftbl in
let clist = List.append nvlist [cnstr] in  (* Valid till here. *)

let cntlist = assertContracts ctx vis so same effect oper kind contrct in

let pgencode = List.append clist cntlist in

(printf "Starting solver: \n"; constSolver ctx pgencode)



let distZ3Code test wrlist ownwrt prgvar totops totins contrct = 
	try (
		if not (Log.open_ "z3.log") then
			printf "Failure with log.\n"
		else (
			printf "Running Z3\n";
			let cfg = [("model", "true"); ("proof", "false")] in
			let ctx = (mk_context cfg) in 
	(*		let eff = (Expr.mk_const ctx (Symbol.mk_string ctx "A") (Integer.mk_sort ctx)) in
			let eq = Boolean.mk_eq ctx (Integer.mk_numeral_i ctx 0) eff in
*)			let bdecl = addBasicDecl ctx prgvar test totops totins ownwrt 
					wrlist contrct in 	
			printf "end\n"
		
		)
	) with Error(msg) -> (
		printf "Z3 EXCEPTION: %s\n" msg ;
		exit 1
	)
