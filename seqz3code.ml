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
open Z3.Arithmetic
open Z3.Arithmetic.Integer

open RwOperations

(* TODO - Need to add the constraint assertions to the goal. *)

(* Creates a list of assert statements that need to be added to the Goal. 
decl	- temporary fro each instruction
oplist	- list of the instructions.
usetb	- the use table (def/use chains)
wrtb	- stores the write assert statements. *)
let rec addInstToGoal ctx oplist decl usetb wrtb = 
	match oplist with 
	| [] -> []
	| h::t -> match h with (s,op) ->
		  match op with 
		  | Read s -> 
		    (let wr = Hashtbl.find usetb h in
		     let ex = Hashtbl.find wrtb wr in
		     let eq = Boolean.mk_eq ctx (List.hd decl) ex in 
		     eq :: addInstToGoal ctx t (List.tl decl) usetb wrtb)
		  | Write v -> 
		    (let cs = (Integer.mk_numeral_i ctx (snd v)) in 
	   	    (Hashtbl.add wrtb h cs; 
		     let eq = Boolean.mk_eq ctx (List.hd decl) cs in
		     eq :: addInstToGoal ctx t (List.tl decl) usetb wrtb))

(* Adding all the variables to context. *)
let rec addVarsToCtx ctx hashtb oplist = 
	match oplist with 
	| [] -> []
	| h::t -> (let vr = (Integer.mk_sort ctx) in 
		  (Expr.mk_const ctx (Symbol.mk_string ctx 
			(Hashtbl.find hashtb h)) vr)) :: 
			(addVarsToCtx ctx hashtb t)

(* Solver. *)
let constSolver ctx gset = 
	let g = (mk_goal ctx true false false) in
 	(Goal.add g gset);
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
	))

(* Starts the z3 encoding -- Parameters: 
hashtb 	- hash table consisting of temporaries for each instruction.
vars	- all the different shared variables.
deftb	- def hash table
usetb	- use hash table
test	- the litmus test case. *)
let seqZ3code hashtb vars oplist deftb usetb test = 
	try (
		if not (Log.open_ "z3.log") then
			Printf.printf "Failure with log.\n"
		else (
			Printf.printf "Running Z3\n";
			let cfg = [("model", "true"); ("proof", "false")] in
			let ctx = (mk_context cfg) in 
			let decl = addVarsToCtx ctx hashtb oplist in
			let wrtb = Hashtbl.create (Hashtbl.length deftb) in 
		(pp_session_opers oplist; Printf.printf "\n";
		Printf.printf "%d:%d" (List.length decl) (List.length oplist);
			let gset = addInstToGoal ctx oplist decl usetb wrtb in
		(Printf.printf "%d: " (Hashtbl.length wrtb);
			constSolver ctx gset))
		);
		exit 0
	) with Error(msg) -> (
		Printf.printf "Z3 EXCEPTION: %s\n" msg ;
		exit 1
	)

