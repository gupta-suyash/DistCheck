open Z3
open Z3.Symbol
open Z3.Sort
open Z3.Expr
open Z3.Boolean
open Z3.FuncDecl
open Z3.Enumeration
open Z3.Quantifier

open RwOperations
open Printf

(* SO Properties. *)

(* (assert (forall ((x effect)) (not (so x x)))) *)
let so_irreflexive ctx effect so =
	let vars = [ (Expr.mk_const ctx (Symbol.mk_string ctx "x") effect) ] in
	let fapp = mk_app ctx so [ (List.nth vars 0); (List.nth vars 0) ] in 
	let fnot = mk_not ctx fapp in
	let qan = (Quantifier.mk_forall_const ctx vars fnot None [] [] None None) in
	let qexp = Quantifier.expr_of_quantifier qan in
	(Printf.printf "Quantifier X: %s\n" (Quantifier.to_string qan) ; qexp)

(* (assert (forall ((x effect) (y effect))
        ( =>    (so x y) (= (ssid x) (ssid y))))) *)
let so_same_session ctx effect so ssid =
	let x = (Expr.mk_const ctx (Symbol.mk_string ctx "x") effect) in 
	let y = (Expr.mk_const ctx (Symbol.mk_string ctx "y") effect) in 
	let vars = [x;y] in
	let f1 = mk_app ctx so [x;y] in 
	let f2 = mk_app ctx ssid [x] in
	let f3 = mk_app ctx ssid [y] in
	let eq = mk_eq ctx f2 f3 in
	let imply = mk_implies ctx f1 eq in
	let qan = (Quantifier.mk_forall_const ctx vars imply None [] [] None None) in
	let qexp = Quantifier.expr_of_quantifier qan in
	(Printf.printf "Quantifier X: %s\n" (Quantifier.to_string qan) ; qexp)

(* (assert (forall ((x effect) (y effect) (z effect))
        ( =>    (and (so x y) (so y z)) (so x z)))) *)
let so_transitivity ctx effect so =
	let x = (Expr.mk_const ctx (Symbol.mk_string ctx "x") effect) in 
	let y = (Expr.mk_const ctx (Symbol.mk_string ctx "y") effect) in 
	let z = (Expr.mk_const ctx (Symbol.mk_string ctx "z") effect) in
	let vars = [x;y;z] in
	let f1 = mk_app ctx so [x;y] in 
	let f2 = mk_app ctx so [y;z] in
	let f3 = mk_app ctx so [x;z] in
	let sand = mk_and ctx [f1;f2] in
	let imply = mk_implies ctx sand f3 in
	let qan = (Quantifier.mk_forall_const ctx vars imply None [] [] None None) in
	let qexp = Quantifier.expr_of_quantifier qan in
	(Printf.printf "Quantifier X: %s\n" (Quantifier.to_string qan) ; qexp)


(* SameObj Properties. *)

(* (assert (forall ((x effect) (y effect))
        ( =>    (same x y) (= (sval x) (sval y))))) *)
let same_equal_var ctx effect same sval =
	let x = (Expr.mk_const ctx (Symbol.mk_string ctx "x") effect) in 
	let y = (Expr.mk_const ctx (Symbol.mk_string ctx "y") effect) in 
	let vars = [x;y] in
	let f1 = mk_app ctx same [x;y] in 
	let f2 = mk_app ctx sval [x] in
	let f3 = mk_app ctx sval [y] in
	let eq = mk_eq ctx f2 f3 in
	let imply = mk_implies ctx f1 eq in
	let qan = (Quantifier.mk_forall_const ctx vars imply None [] [] None None) in
	let qexp = Quantifier.expr_of_quantifier qan in
	(Printf.printf "Quantifier X: %s\n" (Quantifier.to_string qan) ; qexp)

(* (assert (forall ((x effect) (y effect))
        ( =>    (same x y) (same y x)))) *)
let same_symmetric ctx effect same =
	let x = (Expr.mk_const ctx (Symbol.mk_string ctx "x") effect) in 
	let y = (Expr.mk_const ctx (Symbol.mk_string ctx "y") effect) in 
	let vars = [x;y] in
	let f1 = mk_app ctx same [x;y] in 
	let f2 = mk_app ctx same [y;x] in
	let imply = mk_implies ctx f1 f2 in
	let qan = (Quantifier.mk_forall_const ctx vars imply None [] [] None None) in
	let qexp = Quantifier.expr_of_quantifier qan in
	(Printf.printf "Quantifier X: %s\n" (Quantifier.to_string qan) ; qexp)

(* (assert (forall ((x effect) (y effect) (z effect))
        ( =>    (and (same x y) (same y z)) (same x z)))) *) 
let same_transitivity ctx effect same =
	let x = (Expr.mk_const ctx (Symbol.mk_string ctx "x") effect) in 
	let y = (Expr.mk_const ctx (Symbol.mk_string ctx "y") effect) in 
	let z = (Expr.mk_const ctx (Symbol.mk_string ctx "z") effect) in
	let vars = [x;y;z] in
	let f1 = mk_app ctx same [x;y] in 
	let f2 = mk_app ctx same [y;z] in
	let f3 = mk_app ctx same [x;z] in
	let sand = mk_and ctx [f1;f2] in
	let imply = mk_implies ctx sand f3 in
	let qan = (Quantifier.mk_forall_const ctx vars imply None [] [] None None) in
	let qexp = Quantifier.expr_of_quantifier qan in
	(Printf.printf "Quantifier X: %s\n" (Quantifier.to_string qan) ; qexp)


(* Vis Properties. *)
(* (assert (forall ((x effect)) (not (vis x x)))) *)
let vis_irreflexive ctx effect vis =
	let vars = [ (Expr.mk_const ctx (Symbol.mk_string ctx "x") effect) ] in
	let fapp = mk_app ctx vis [ (List.nth vars 0); (List.nth vars 0) ] in 
	let fnot = mk_not ctx fapp in
	let qan = (Quantifier.mk_forall_const ctx vars fnot None [] [] None None) in
	let qexp = Quantifier.expr_of_quantifier qan in
	(Printf.printf "Quantifier X: %s\n" (Quantifier.to_string qan) ; qexp)


(* (assert (forall ((x effect) (y effect))
        ( =>    (vis x y) (not (vis y x))))) *)
let vis_anti_symmetric ctx effect vis =
	let x = (Expr.mk_const ctx (Symbol.mk_string ctx "x") effect) in 
	let y = (Expr.mk_const ctx (Symbol.mk_string ctx "y") effect) in 
	let vars = [x;y] in
	let f1 = mk_app ctx vis [x;y] in 
	let f2 = mk_app ctx vis [y;x] in
	let fnot = mk_not ctx f2 in
	let imply = mk_implies ctx f1 fnot in
	let qan = (Quantifier.mk_forall_const ctx vars imply None [] [] None None) in
	let qexp = Quantifier.expr_of_quantifier qan in
	(Printf.printf "Quantifier X: %s\n" (Quantifier.to_string qan) ; qexp)


(* HB Properties. *)

(* (assert (forall ((x effect) (y effect))
    (=> (or (vis x y) (so x y)) (hb x y)))) *)
let hb_define ctx effect vis so hb =
	let x = (Expr.mk_const ctx (Symbol.mk_string ctx "x") effect) in 
	let y = (Expr.mk_const ctx (Symbol.mk_string ctx "y") effect) in 
	let z = (Expr.mk_const ctx (Symbol.mk_string ctx "z") effect) in
	let vars = [x;y;z] in
	let f1 = mk_app ctx vis [x;y] in 
	let f2 = mk_app ctx so [x;y] in
	let f3 = mk_app ctx hb [x;y] in
	let hor = mk_or ctx [f1;f2] in
	let imply = mk_implies ctx hor f3 in
	let qan = (Quantifier.mk_forall_const ctx vars imply None [] [] None None) in
	let qexp = Quantifier.expr_of_quantifier qan in
	(Printf.printf "Quantifier X: %s\n" (Quantifier.to_string qan) ; qexp)

(* (assert (forall ((x effect)) (not (hb x x)))) *)
let hb_irreflexive ctx effect hb =
	let vars = [ (Expr.mk_const ctx (Symbol.mk_string ctx "x") effect) ] in
	let fapp = mk_app ctx hb [ (List.nth vars 0); (List.nth vars 0) ] in 
	let fnot = mk_not ctx fapp in
	let qan = (Quantifier.mk_forall_const ctx vars fnot None [] [] None None) in
	let qexp = Quantifier.expr_of_quantifier qan in
	(Printf.printf "Quantifier X: %s\n" (Quantifier.to_string qan) ; qexp)

(* (assert (forall ((x effect) (y effect) (z effect))
    (=> (and (hb x y) (hb y z)) (hb x z)))) *)
let hb_transitivity ctx effect hb =
	let x = (Expr.mk_const ctx (Symbol.mk_string ctx "x") effect) in 
	let y = (Expr.mk_const ctx (Symbol.mk_string ctx "y") effect) in 
	let z = (Expr.mk_const ctx (Symbol.mk_string ctx "z") effect) in
	let vars = [x;y;z] in
	let f1 = mk_app ctx hb [x;y] in 
	let f2 = mk_app ctx hb [y;z] in
	let f3 = mk_app ctx hb [x;z] in
	let sand = mk_and ctx [f1;f2] in
	let imply = mk_implies ctx sand f3 in
	let qan = (Quantifier.mk_forall_const ctx vars imply None [] [] None None) in
	let qexp = Quantifier.expr_of_quantifier qan in
	(Printf.printf "Quantifier X: %s\n" (Quantifier.to_string qan) ; qexp)

(* 
(assert (forall ((x effect) (y effect) (z effect))
        ( =>    (and
                        (and
                                (and
                                        (= (oper x) R)
                                        (and  (= (oper y) W) (= (oper z) W)))
                                (and (same x y) (same y z)))
                        (and
                                (vis y x)
                                (and (vis z x) (hb y z)))))
                (= (rval x) (rval z)))))
*)
let hb_acyclic ctx effect hb oper vis same rval kind =
	let x = (Expr.mk_const ctx (Symbol.mk_string ctx "x") effect) in 
	let y = (Expr.mk_const ctx (Symbol.mk_string ctx "y") effect) in 
	let z = (Expr.mk_const ctx (Symbol.mk_string ctx "z") effect) in
	let vars = [x;y;z] in
	let f1 = mk_app ctx oper [x] in
	let xread = mk_eq ctx f1 (get_const kind 0) in
	let f2 = mk_app ctx oper [y] in
	let yread = mk_eq ctx f2 (get_const kind 1) in
	let f3 = mk_app ctx oper [z] in
	let zread = mk_eq ctx f3 (get_const kind 1) in
	let oand1 = mk_and ctx [yread;zread] in
	let oand2 = mk_and ctx [xread;oand1] in

	let f4 = mk_app ctx same [x;y] in
	let f5 = mk_app ctx same [y;z] in 
	let sand = mk_and ctx [f4;f5] in
	let aand = mk_and ctx [oand2;sand] in
 
	let f6 = mk_app ctx vis [y;x] in
	let f7 = mk_app ctx vis [z;x] in
	let f8 = mk_app ctx hb [y;z] in
	let vand1 = mk_and ctx [f7;f8] in
	let vand2 = mk_and ctx [f6;vand1] in
	let cand = mk_and ctx [aand;vand2] in

	let f9 = mk_app ctx rval [x] in
	let f10 = mk_app ctx rval [z] in
	let veq = mk_eq ctx f9 f10 in

	let imply = mk_implies ctx cand veq in
	let qan = (Quantifier.mk_forall_const ctx vars imply None [] [] None None) in
	let qexp = Quantifier.expr_of_quantifier qan in
	(Printf.printf "Quantifier X: %s\n" (Quantifier.to_string qan) ; qexp)

