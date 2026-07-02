(* Title:
 Author:
 *)

theory Exercise0211
imports Main
begin

(*
Exercise 2.11. Define arithmetic expressions in one variable over integers
(type int) as a data type:
datatype exp = Var | Const int | Add exp exp | Mult exp exp
*)

datatype exp = Var | Const int | Add exp exp | Mult exp exp 

(*
Define a function eval :: exp \<Rightarrow> int \<Rightarrow> int such that eval e x evaluates e at
the value x.
A polynomial can be represented as a list of coefficients, starting with the
constant. For example, [4, 2, − 1, 3] represents the polynomial 4+2x−x^2+3*x^3
*)

fun eval :: "exp \<Rightarrow> int \<Rightarrow> int" where
"eval Var x = x" |
"eval (Const i) x = i" |
"eval (Add e1 e2) x = (eval e1 x) + (eval e2 x)" |
"eval (Mult e1 e2) x = (eval e1 x) * (eval e2 x)" 

(* combines powers - think basic addition instead units 10s 100s 1000s its  powers of x 
constant power_of_1 powers_of_2 powers_of_3 
*)
fun comb :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"comb [] ys = ys" |
"comb xs [] = xs" |
"comb (x # xt) (y # yt) = (x + y) # (comb xt yt)" 

(* represents addition of 3x and 2 expect 2+3x as result - in list form [2,3]*)
value "comb [0,3] [2]" 

(*
fun fan3 :: "int \<Rightarrow> int list \<Rightarrow> int list \<Rightarrow> int list" where
"fan3 x ys aa = aa @ (map (%v . v * x) ys)"

fun fan2 :: "int list \<Rightarrow> int list \<Rightarrow> int list \<Rightarrow> int list \<Rightarrow> int list" where
"fan2 [] ys zs aa = zs " |
"fan2 xs [] zs aa = []"  |
"fan2 (x # xt) ys zs aa = fan2 xt ys (comb (fan3 x ys aa) zs) (0 # aa)" 


fun fan :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"fan [] ys = []" |
"fan xs [] = []" |
"fan xs ys = fan2 xs ys [] []"
*)


(* Scales a polynomial list by a single scalar coefficient: c * P(x) *)
fun poly_scale :: "int \<Rightarrow> int list \<Rightarrow> int list" where
"poly_scale c [] = []" |
"poly_scale c (y # ys) = (c * y) # poly_scale c ys"

(* Multiplies two polynomials structurally: P(x) * Q(x) *)
fun fan :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"fan [] ys = []" |
"fan (x # xt) ys = comb (poly_scale x ys) (0 # fan xt ys)"


fun coeffs :: "exp \<Rightarrow> int list" where
"coeffs Var = [0,1]" |
"coeffs (Const i) = [i]" |
"coeffs (Add e1 e2) = (let s1 = coeffs e1 in 
                       let s2 = coeffs e2 in 
                          comb s1 s2)" |
"coeffs (Mult e1 e2) = (let s1 = coeffs e1 in 
                        let s2 = coeffs e2 in 
                           fan s1 s2)" 

(* [4,2,-1,3] *)
value "(Add (Const 4) (Add (Mult (Const 2) Var) (Add (Mult (Const (-1)) (Mult Var Var)) 
  (Mult (Const 3) (Mult Var (Mult Var Var))))))"

value "eval (Add (Const 4) (Add (Mult (Const 2) Var) (Add (Mult (Const (-1)) (Mult Var Var)) 
  (Mult (Const 3) (Mult Var (Mult Var Var)))))) 3"

value "coeffs (Add (Const 4) (Add (Mult (Const 2) Var) (Add (Mult (Const (-1)) (Mult Var Var)) 
  (Mult (Const 3) (Mult Var (Mult Var Var))))))"

value "(Add (Const 4) (Add (Mult (Const 2) Var) (Add (Mult (Const (-1)) (Mult Var Var)) 
  (Mult (Const 3) (Mult Var (Mult Var Var))))))"


fun evalp3 :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
"evalp3 x n z = (if n = 0 then x else  x * (z ^ (nat n)))" 

fun evalp2 :: "int list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
"evalp2 [] n z = 0" |
"evalp2 (x # xt) n z = (evalp3 x n z) + (evalp2 xt (n + 1) z)" 

fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
"evalp xs z = evalp2 xs 0 z" 

(* expected 82 for the polynomial 3x^3 - x^2 + 2x + 4 evaluated at x = 3 *)
value "evalp [4,2,-1,3] 3" 


lemma evalp2_comb: "evalp2 (comb xs ys) n x = evalp2 xs n x + evalp2 ys n x"
  apply(induction xs ys arbitrary: n rule: comb.induct)
  apply(auto simp: algebra_simps)
  done


lemma evalp_comb: "evalp (comb xs ys) x = evalp xs x + evalp ys x"
  apply(induction xs ys arbitrary: n rule: comb.induct)
  apply(auto simp: algebra_simps evalp2_comb)
  done

lemma evalp2_poly_scale: "evalp2 (poly_scale c ys) n x = c * evalp2 ys n x" 
  apply(induction ys arbitrary: n)
  apply(auto simp: algebra_simps)
  done

lemma evalp2_shift: "evalp2 (0 # xs) n x = evalp2 xs (n + 1) x"
  apply(induction xs arbitrary: n x)
  apply (simp add: evalp3.simps)
  apply(auto)
  done

(* we stall here ? *)

lemma evalp2_factor_out: "0 \<le> n \<Longrightarrow> evalp2 ys n x = evalp2 ys 0 x * (x ^ nat n)"
  apply(induction ys arbitrary: n)
   apply(simp)
  apply(case_tac n)
   apply(simp add: evalp3.simps)
  apply(simp add: evalp3.simps algebra_simps power_add nat_add_distrib)
  oops


lemma evalp2_factor_out: "0 \<le> n \<Longrightarrow> evalp2 ys n x = evalp2 ys 0 x * (x ^ nat n)"
  apply(induction ys arbitrary: n)
  apply(auto simp: evalp2_shift evalp2_poly_scale)
  oops

(*
lemma evalp2_factor_out: "0 \<le> n \<Longrightarrow> evalp2 ys n x = evalp2 ys 0 x * (x ^ nat n)"
  apply(induction ys arbitrary: n)
   apply(simp)
apply(auto simp: algebra_simps power_add)
 oops

lemma evalp2_fan: "n \<ge> 0 \<Longrightarrow> evalp2 (fan xs ys) n x = evalp2 xs n x * evalp2 ys 0 x" 
  apply(induction xs arbitrary: n)
  apply(auto) 
  apply(auto simp add: evalp2_comb evalp2_poly_scale evalp2_shift algebra_simps)
  oops

lemma eval_coeff : "evalp (coeffs e) x = eval e x" 
  apply(induction e arbitrary: x)
  apply(auto simp: algebra_simps evalp_comb evalp2_comb)

*)

(* --- anything below this line is to be ignored --- *)
