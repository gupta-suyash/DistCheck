open Z3
open Z3.Symbol
open Z3.Set
open Z3.Sort
open Z3.Expr
open Z3.Boolean
open Z3.FuncDecl
open Z3.Enumeration
open Z3.Quantifier

open ContractLang
open Printf

let rec getParameter ctx oper kind effect plist ptbls = 
	match plist with 
	| [] -> ptbls
	| h::t -> match h with (s,typ) ->
		  let eff = (Expr.mk_const ctx (Symbol.mk_string ctx s) effect) in
		  (Hashtbl.add (fst ptbls) s eff;  
		  (match typ with 
		  | R -> let fapp = mk_app ctx oper [eff] in
		  	 let eq = mk_eq ctx fapp (get_const kind 0) in 
			 Hashtbl.add (snd ptbls) s eq
		  | W -> let fapp = mk_app ctx oper [eff] in
		  	 let eq = mk_eq ctx fapp (get_const kind 1) in 
			 Hashtbl.add (snd ptbls) s eq
		  | RW -> let fapp = mk_app ctx oper [eff] in
		  	  let tr = mk_true ctx in 
			  Hashtbl.add (snd ptbls) s tr);
		  getParameter ctx oper kind effect t ptbls)

let rec setRelation ctx vis so same rel ip ptables = 
	match rel with 
	| Vis -> let eff1 = Hashtbl.find ptables (fst ip) in
		 let eff2 = Hashtbl.find ptables (snd ip) in
		 mk_app ctx vis [eff1;eff2]
	| So ->  let eff1 = Hashtbl.find ptables (fst ip) in
		 let eff2 = Hashtbl.find ptables (snd ip) in
		 mk_app ctx so [eff1;eff2]
	| Sameobj -> let eff1 = Hashtbl.find ptables (fst ip) in
		     let eff2 = Hashtbl.find ptables (snd ip) in
		     mk_app ctx same [eff1;eff2]
	| Union (r1,r2) -> let exp1 = setRelation ctx vis so same r1 ip ptables in 
			   let exp2 = setRelation ctx vis so same r2 ip ptables in
			   mk_or ctx [exp1;exp2] (* TODO -- How to handle union. *)
	| Inter (r1,r2) -> let exp1 = setRelation ctx vis so same r1 ip ptables in 
			   let exp2 = setRelation ctx vis so same r2 ip ptables in
			   mk_and ctx [exp1;exp2] (* TODO -- how to handle this. *)
	| Rplus r -> let exp = setRelation ctx vis so same r ip ptables in 
		     mk_complement ctx exp (* TODO -- wrong interpretation. *)


let rec getProperty ctx vis so same aexp prop ptables count = 
	match prop with 
	| Patom (r,ip) -> let rel = setRelation ctx vis so same r ip ptables in
			  if count == 0 
			  then (mk_and ctx [aexp;rel])
			  else rel
	| Pand (p1,p2) -> let exp1 = getProperty ctx vis so same 
						aexp p1 ptables (count+1) in
			  let expa = (if count == 0 
			  then mk_and ctx [aexp;exp1] else exp1) in
			  let exp2 = getProperty ctx vis so same 
						aexp p2 ptables (count+1) in
			  mk_and ctx [expa;exp2]
	| Por (p1,p2) ->  let exp1 = getProperty ctx vis so same 
						aexp p1 ptables (count+1) in
			  let expa = (if count == 0 
			  then mk_and ctx [aexp;exp1] else exp1) in
			  let exp2 = getProperty ctx vis so same 
						aexp p2 ptables (count+1) in
			  mk_or ctx [expa;exp2]
	| Pimply (p1,p2) -> let exp1 = getProperty ctx vis so same 
						aexp p1 ptables (count+1) in
			  let expa = (if count == 0 
			  then mk_and ctx [aexp;exp1] else exp1) in
			  let exp2 = getProperty ctx vis so same 
						aexp p2 ptables (count+1) in
			  mk_implies ctx expa exp2

let rec andAllPredicates ctx phd ptl =
	match ptl with 
	| [] -> phd
	| h::t -> mk_and ctx [h;(andAllPredicates ctx phd t)]

let setContract ctx vis so same effect oper kind contct =
	let pcount = List.length contct.param in
	let poptbl = Hashtbl.create pcount in 
	let ptytbl = Hashtbl.create pcount in 
	let ptables = getParameter ctx oper kind effect 
				contct.param (poptbl,ptytbl) in
	let varlst = Hashtbl.fold (fun x y z -> y :: z) (snd ptables) [] in
	let aexp = (if List.length varlst == 1 
		   then List.hd varlst 
		   else andAllPredicates ctx (List.hd varlst) (List.tl varlst)) in
	let propty = getProperty ctx vis so same aexp contct.prp (fst ptables) 0 in
	let vars = Hashtbl.fold (fun x y z -> y :: z) (fst ptables) [] in
	let qan = (Quantifier.mk_forall_const ctx vars propty 
						None [] [] None None) in
	(printf "Quantifier X: %s\n" (Quantifier.to_string qan);
	let qexp = Quantifier.expr_of_quantifier qan in qexp)
	


let rec assertContracts ctx vis so same effect oper kind contcts =
	match contcts with 
	| [] -> []
	| h::t -> (setContract ctx vis so same effect oper kind h) ::
		(assertContracts ctx vis so same effect oper kind t)

