(*  Title:      Concrete-Semantics/Chapter2.thy
    Author:     Terry
*)

section \<open>Chapter2\<close>

theory Chapter2
  imports Main
begin

(*
Exercises

Exercise 2.1. Use the value command to evaluate the following expressions:
"1 + (2::nat)", "1 + (2::int)", "1 − (2::nat)" and "1 − (2::int)".

clipboard 1 - (2::nat) the minus sign is copied wrong
*)

value "1 + (2::nat)"
value "1 + (2::int)"
value "1 - (2::nat)"
value "1 - (2::int)"

(*
Exercise 2.2. Start from the definition of add given above. Prove that add
is associative and commutative. 
Define a recursive function double :: nat \<Rightarrow> nat and prove double m = add m m.
*)

(* ok here is the definition of add , the natural numbers*)
fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc(add m n)"

(*lets check its 3 as expected*)
value "add 1 2"

lemma add_m_0: "add m 0 = m" 
   apply(induction m)
   apply(auto)
  done
(* proved our first theorem : theorem add_m_0: add ?m 0 = ?m *)

lemma add_assoc3: "add (add a b) c = add a (add b c)"
  apply(induction a)
   apply(subst add.simps)
   apply(subst add.simps)
   apply(rule refl) 
(*    apply(simp only: add.simps)  simp too powerful*)
  apply(subst add.simps)
  apply(subst add.simps)
  apply(subst add.simps)
  apply (rule arg_cong[where f=Suc])  (* *)
  apply assumption
  done


lemma add_assoc2: "add (add a b) c = add a (add b c)"
  apply(induction a)
  apply(simp)
  apply(simp)
  done

(* prove add is associative  (a + b) + c = a + (b + c) *)
lemma add_assoc: "add (add a b) c = add a (add b c)"
(*   apply(induction a arbitrary: b) *)
  apply(induction a)
   apply(auto)
  done

(* prove add is commutative  -- a + b = b + a 
*)
lemma add_m_suc: "add a (Suc b) = Suc (add a b)"
  apply(induction a)
  apply(subst add.simps)
  apply(subst add.simps)
  apply(rule refl) 
  apply(subst add.simps)
  apply(subst add.simps)
  apply (rule arg_cong[where f=Suc])  (* *)
  apply assumption 
  done


lemma add_comm: "add a b = add b a"
  apply(induction a)
   apply(subst add.simps)
   apply(simp add: add_m_0)
  apply(subst add.simps)
  apply(simp only: add_m_suc)
  done

(* exercise 2.2 cont/d 
Define a recursive function double :: nat \<Rightarrow> nat and prove double m = add m m.
*)

fun double :: "nat \<Rightarrow> nat " where
"double 0 = 0" |
"double (Suc m) = add (Suc m) (Suc m)" 

(***was double (Suc m) = Suc (Suc (double m))  *)

value "double 0" (*check*)
value "double 2"
value "double 3" 

lemma double_m_add_m_m: "double m = add m m"
  apply(induction m)
   apply(subst double.simps)
   apply(simp add: add_m_0)
  apply(subst double.simps)
  apply(rule refl) 
  done


fun double2 :: "nat \<Rightarrow> nat " where
"double2 0 = 0" |
"double2 (Suc m) = Suc (Suc (double2 m))" 

(*check doubles correctly*)
value "double2 0" 
value "double2 2"
value "double2 3" 

(*
lemma add_m_suc_m : "Suc (add m m) = add m (Suc m) "
  apply(induction m)
  apply(simp)
  apply(simp add: add_m_suc)
  done
 *)

lemma add_m_suc_n : "Suc (add m n) = add m (Suc n) "
  apply(induction m)
  apply(simp)
  apply(simp add: add_m_suc)
  done

lemma double2_m_add_m_m: "double2 m = add m m"
  apply(induction m)
  apply(simp)
  apply(simp add: add_m_suc)
  done



(* key point - advised to make functions like double2 that involve only themselves and Suc 
  then connect double m = add m m , this way building a genuine connection between functions 
  that know nothing about themselves apart from definition of natural numbers 
*)


(* 
  apply(simp add: add.simps)
  apply(simp add: double2.simps)
  apply(simp add: add.simps)
  apply(subst double2.simps)
   apply(simp add: add_m_0)
   apply(simp add: add.simps)
   apply(subst double2.simps)
  apply (erule subst)
  apply(subst double2.simps)
  apply (subst double2.simps)
  apply(rule refl) 
*)


(*
Exercise 2.3. Define a function count :: 'a \<Rightarrow> 'a list \<Rightarrow> nat that counts the
number of occurrences of an element in a list. 
Prove count x xs \<le> length xs.
*)

fun count :: " 'a \<Rightarrow> 'a list \<Rightarrow> nat " where
"count x [] = 0" |
"count x (h # t) = (if x = h 
                   then 1 + (count x t) 
                   else count x t)" 

value "count (2::int) []"
value "count (2::int) [1,2,3]"

lemma count_length : "count x xs \<le> length xs" 
  apply(induction xs)
  apply(auto)
  done 

 
lemma count_length2 : "count x xs \<le> length xs" 
  apply(induction xs)
  apply(auto)
  done 


(*
Exercise 2.4. Define a recursive function snoc :: 'a list \<Rightarrow> 'a \<Rightarrow> 'a list
that appends an element to the end of a list. 

With the help of snoc define a recursive function reverse
reverse :: 'a list \<Rightarrow> 'a list that reverses a list. 

Prove reverse (reverse xs) = xs.
*)

value "[] :: int list"

fun snoc :: " 'a list \<Rightarrow> 'a \<Rightarrow> 'a list " where
"snoc [] x = [x] " |
"snoc (h # t) x = h # (snoc t x)" 

fun reverse :: " 'a list \<Rightarrow> 'a list " where
"reverse [] = [] " |
"reverse (h # t) = snoc (reverse t) h" 

value "snoc [1,2,3] 4 :: int list"
value "reverse (snoc [1,2,3] 4) :: int list"

(*  
reverse (reverse (a # xs)) = a # xs 
*)

value "reverse (1 # []) :: int list"
value "reverse (1 # [2]) :: int list"
value "reverse (1 # [2,3]) :: int list"
value "reverse (1 # [2,3,4]) :: int list"
value "[1,2] @ [3,4] :: int list"

lemma snoc_append: "snoc xs a = append xs [a]"
  apply(induction xs)
   apply(auto)
  done

(* ok that surprised me it worked*)
lemma reverse_append2: "reverse (append x y) = append (reverse y) (reverse x) " 
  apply(induction x)
   apply(auto)
  apply(simp add:snoc_append)
  done

(**** this is the target to prove ****)
lemma reverse_reverse : "reverse (reverse xs) = xs" 
  apply(induction xs)
   apply(simp)
  apply(simp add:snoc_append)
  apply(simp add:reverse_append2)
  done 

(* that was quite tough even though its an identical classic rev rev xs = xs*)


(*
Exercise 2.5. Define a recursive function sum :: nat \<Rightarrow> nat such that sum n
= 0 + ... + n and prove sum n = n \<^emph> (n + 1) div 2.
*)

fun sum :: " nat \<Rightarrow> nat " where
"sum 0 = 0 " |
"sum (Suc n) = (Suc n) + sum n " 

value "sum 0"
value "sum 1"
value "sum 2"
value "sum 10"

lemma sum_n : "sum n = n * (n + 1) div 2"
  apply(induction n)
   apply(auto)
  done


(*
Exercise 2.6. Starting from the type 'a tree defined in the text, define a
function contents that collects all values in a tree in a list,
in any order, without removing duplicates. 

contents :: 'a tree \<Rightarrow> 'a list 

Then define a function treesum that sums up all values in a tree of natural 
numbers and

treesum :: nat tree \<Rightarrow> nat

prove treesum t = listsum (contents t).
*)


datatype 'a tree = Tip | Node " 'a tree" 'a " 'a tree"

fun contents :: " 'a tree \<Rightarrow> 'a list " where
"contents Tip = [] " |
"contents (Node left x right) = contents left @ [x] @ contents right" 

(* we can read contents of 1 - 2 - 3 tree *)
value "contents (Node (Node Tip 1 Tip) 2 (Node Tip 3 Tip)) :: int list"

fun treesum :: " nat tree \<Rightarrow> nat " where
"treesum Tip = 0 " |
"treesum (Node left x right) = treesum left + x + treesum right" 

fun listsum :: " nat list \<Rightarrow> nat " where
"listsum [] = 0 " |
"listsum (h # t) =  h + listsum t" 

lemma listsum_dist : "listsum (x @ y) = (listsum x) + (listsum y)"
  apply(induction x)
   apply(auto)
  done

lemma treesum_listsum : "treesum t = listsum (contents t)"
  apply(induction t)
   apply(auto)
  apply(simp add: listsum_dist)
  done


(*
Exercise 2.7. 
Define a new type 'a tree2 of binary trees where values are
also stored in the leaves of the tree. 

Also reformulate the mirror function accordingly. 

Define two functions 

pre_order  :: 'a tree2 \<Rightarrow> 'a list  
post_order :: 'a tree2 \<Rightarrow> 'a list 

that traverse a tree and collect all stored values in the respective
order in a list. 

Prove pre_order (mirror t) = rev (post_order t).
*)

datatype 'a tree2 = Tip2 'a | Node2 " 'a tree2" 'a " 'a tree2"

fun mirror :: "'a tree2 \<Rightarrow> 'a tree2" where
"mirror (Tip2 x) = (Tip2 x)" |
"mirror (Node2 l a r ) = Node2 (mirror r ) a (mirror l)"

fun pre_order :: "'a tree2 \<Rightarrow> 'a list" where
"pre_order (Tip2 x) = [x]" |
"pre_order (Node2 l a r ) = [a] @ (pre_order l ) @ (pre_order r)"

fun post_order :: "'a tree2 \<Rightarrow> 'a list" where
"post_order (Tip2 x) = [x]" |
"post_order (Node2 l a r ) = (post_order l ) @ (post_order r) @ [a]"

lemma pre_post_order : "pre_order (mirror t) = rev (post_order t)"
  apply(induction t)
  apply(auto)
  done


(*
Exercise 2.8. Define a function 

intersperse :: 'a \<Rightarrow> 'a list \<Rightarrow> 'a list 

such that intersperse a [x 1, ..., x n] = [x 1, a, x 2, a, ..., a, x n]. 

Now prove 

map f (intersperse a xs) = intersperse (f a) (map f xs).
*)

fun intersperse :: "'a  \<Rightarrow> 'a list  \<Rightarrow> 'a list " where
"intersperse a [] = []" |
"intersperse a [e] = [e]" |
"intersperse a (h # t) = h # (a # (intersperse a t))"

value "intersperse 9 [1,2,3,4,5] :: int list"

lemma intersperse_map : "map f (intersperse a xs) = intersperse (f a) (map f xs)"
  apply(induction xs rule: intersperse.induct)
  apply(auto) 
  done


(*
Exercise 2.9. Write a tail-recursive variant of the add function on nat:

itadd :: nat \<Rightarrow> nat \<Rightarrow> nat 

Tail-recursive means that in the recursive case, itadd needs to call
itself directly: 

itadd (Suc m) n = itadd . . ..

Prove itadd m n = add m n.
*)

fun itadd :: " nat  \<Rightarrow> nat  \<Rightarrow> nat " where
"itadd 0 n = n" |
"itadd (Suc m) n = itadd m (Suc n)" 

(** this is the target to prove **)
lemma itadd_add : "itadd m n = add m n"
  apply(induction m arbitrary: n)
  apply(simp add: add_m_suc_n)
  apply(simp add: add_m_suc_n)
  done

(** we use arbitrary:n because n is used as the accumulator in a tail recursive 
function , if itadd was not tail recursive its not needed - i think
**)

(*
Exercise 2.10. Define a 
datatype tree0 of binary tree skeletons which do not
store any information, neither in the inner nodes nor in the leaves. 
-- binary skeleton no 
*)

datatype tree0 = Tip0 | Node0 "tree0" "tree0"

(*
Define a function 
nodes :: tree0 \<Rightarrow> nat that counts the number of all nodes (inner
nodes and leaves) in such a tree. 
*)
fun nodes :: " tree0 \<Rightarrow> nat " where
"nodes Tip0 = 1 " |
"nodes (Node0 left right) = 1 + (nodes left) + (nodes right)" 


(*
Consider the following recursive function:

fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
"explode 0 t = t" |
"explode (Suc n) t = explode n (Node t t)"

Find an equation expressing the size of a tree after exploding it (nodes
(explode n t)) as a function of nodes t and n. 
Prove your equation. 

You
may use the usual arithmetic operators, including the exponentiation operator “^”.
 For example, 2 ^ 2 = 4.
Hint: simplifying with the list of theorems algebra_simps takes care of
common algebraic properties of the arithmetic operators.
*)

fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
"explode 0 t = t" |
"explode (Suc n) t = explode n (Node0 t t)"

value "nodes (explode 1 Tip0)"  (* = 3*)
value "nodes (explode 2 Tip0)"  (* = 2n+1 where n is (explode (2-1) Tip) == 7*)
value "nodes (explode 3 Tip0)"  (* = 2n+1 where n is 7 (explode (3-1) Tip) == 15*)
value "nodes (explode 4 Tip0)"  (* = 2n+1 where n is 15 (explode (4-1) Tip) == 31*)

fun nodex :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"nodex nt 0 = nt" |
"nodex nt (Suc n) = 2*(nodex nt n) + 1"

value "nodex (nodes Tip0) 1 = nodes (explode 1 Tip0)" 
value "nodex (nodes Tip0) 2 = nodes (explode 2 Tip0)"
value "nodex (nodes Tip0) 3 = nodes (explode 3 Tip0)"
value "nodex (nodes Tip0) 4 = nodes (explode 4 Tip0)"

lemma nodex_step: "nodex (2 * nt + 1) n = 2 * (nodex nt n) + 1"
  apply(induction n arbitrary: t)
   apply(auto)
  done

lemma nodex_step2: "nodex (Suc (m + m)) n = Suc (2 * nodex m n)"
  apply(induction n)
   apply(auto)
  done

lemma nodex_rel : "nodes (explode n t) = nodex (nodes t) n"
  apply(induction n arbitrary: t)
  apply(auto)
  apply(auto simp add:nodex_step2 algebra_simps)
  done

(*** we proved it
after auto we were left with 

 \<And>n t. (\<And>t. nodes (explode n t) = nodex (nodes t) n) 
\<Longrightarrow> nodex (Suc (nodes t + nodes t)) n = Suc (2 * nodex (nodes t) n)

so we made whole right hand side another lemma  

nodex (Suc (nodes t + nodes t)) n = Suc (2 * nodex (nodes t) n)

if substitute m for nodes t

nodex (Suc (m + m)) n = Suc (2 * nodex m n)

this is the lemma we needed to prove
***)



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

lemma evalp2_factor_out: "0 \<le> n \<Longrightarrow> evalp2 ys n x = evalp2 ys 0 x * (x ^ nat n)"
  apply(induction ys arbitrary: n)
  apply(simp)
  oops

(*  apply(auto simp: algebra_simps power_add nat_add_distrib)
  done
*)


lemma evalp2_factor_out: "0 \<le> n \<Longrightarrow> evalp2 ys n x = evalp2 ys 0 x * (x ^ nat n)"
  apply(induction ys arbitrary: n)
   apply(simp)
apply(auto simp: algebra_simps power_add)



lemma evalp2_fan: "n \<ge> 0 \<Longrightarrow> evalp2 (fan xs ys) n x = evalp2 xs n x * evalp2 ys 0 x" 
  apply(induction xs arbitrary: n)
  apply(auto) 
  apply(auto simp add: evalp2_comb evalp2_poly_scale evalp2_shift algebra_simps)
  oops

 (* proof (prove)
goal (1 subgoal):
 1. evalp2 (fan xs ys) n x = evalp2 xs n x * evalp2 ys 0 x 
Auto Quickcheck found a counterexample:
  xs = [- 2]
  ys = [- 2, - 1]
  n = - 3
  x = - 3
Evaluated terms:
  evalp2 (fan xs ys) n x = 6
  evalp2 xs n x * evalp2 ys 0 x = - 2

 oops
*)

(*
  apply(induction ys arbitrary: n)
  apply(auto) 
  apply(simp add: evalp2_comb evalp2_poly_scale evalp2_shift algebra_simps)
  done
*)


(*
lemma evalp2_fan3: 
  "\<lbrakk> ys \<noteq> []; \<forall>y \<in> set aa. y = 0 \<rbrakk> \<Longrightarrow> evalp2 (fan3 c ys aa) 0 x = c * (x ^ length aa) * evalp2 ys 0 x" 
  apply(induction ys arbitrary: x c aa rule: fan.induct)
  apply(auto simp: algebra_simps)

lemma evalp2_fan3: "ys \<noteq> [] \<Longrightarrow> evalp2 (fan3 c ys aa) 0 x = c * (x ^ length aa) * evalp2 ys 0 x"

lemma evalp2_fan3: "evalp2 (fan3 c ys aa) 0 x = c * (x ^ length aa) * evalp2 ys 0 x" 
  oops
*)

lemma eval_coeff : "evalp (coeffs e) x = eval e x" 
  apply(induction e arbitrary: x)
  apply(auto simp: algebra_simps evalp_comb evalp2_comb)



(*
proof (prove)
goal (2 subgoals):
 1. \<And>e1 e2 x. (\<And>x. evalp2 (coeffs e1) 0 x = eval e1 x) \<Longrightarrow> (\<And>x. evalp2 (coeffs e2) 0 x = eval e2 x) \<Longrightarrow> 
evalp2 (comb (coeffs e1) (coeffs e2)) 0 x = eval e1 x + eval e2 x

 2. \<And>e1 e2 x. (\<And>x. evalp2 (coeffs e1) 0 x = eval e1 x) \<Longrightarrow> (\<And>x. evalp2 (coeffs e2) 0 x = eval e2 x) \<Longrightarrow> 
evalp2 (fan2 (coeffs e1) (coeffs e2) [] []) 0 x = eval e1 x * eval e2 x
*)





(* --- anything below this line is to be ignored --- *)

(*
(define (seval expr)
  (cond
    ((equal? expr 'var) '(0 1))
    ((and (pair? expr) (equal? (car expr) 'const))
     (let ((e1 (car (cdr expr))))
       `(,e1)))
    ((and (pair? expr) (equal? (car expr) 'add))
     (let ((e1 (seval (car (cdr expr))))
	   (e2 (seval (car (cdr (cdr expr))))))
       (comb e1 e2)))
    ((and (pair? expr) (equal? (car expr) 'mult))
     (let ((e1 (seval (car (cdr expr))))
	   (e2 (seval (car (cdr (cdr expr))))))
       (fan-mult e1 e2)))))

;; a rename
(define coeffs seval)

*)


(*

(define (fan-mult xs ys) 
  (fan2-mult xs ys '() '()))

(fan3-mult 2 '(0 1 0 2) '(0 0))

*)

(*

"eval (VarPow i) x = x ^ (nat i)" 

value "eval Var 3" 
value "eval (Const 5) 3"
value "eval (Add Var Var) 3"
(* 2 raised to 3rd power 2^3 should be 2 * 2 * 2 or 8 *)
value "eval (VarPow 3) 2" 

fun mlist3 :: "int \<Rightarrow> int \<Rightarrow> exp" where 
"mlist3 x pow = (if pow < 1 then Mult (Const x) (VarPow 0)
                else Mult (Const x) (VarPow pow))" 

fun mlist2 :: "int list \<Rightarrow> int \<Rightarrow> exp" where 
"mlist2 [] pow = Mult (Const 0) (VarPow 0)" |
"mlist2 [x] pow = mlist3 x pow" |
"mlist2 (x # t) pow = (let v = mlist3 x pow in 
                       let v2 = mlist2 t (pow + 1) in 
                       Add v v2)" 

(* poly takes an int list and produces an equivalent expression*)
fun poly :: "int list \<Rightarrow> exp" where 
"poly xs = mlist2 xs 0" 

fun coeffs :: "exp \<Rightarrow> int list" where
"coeffs Var = []" |
"coeffs (Const i)  = [i]" |
"coeffs (Add e1 e2)  = (coeffs e1) @ (coeffs e2)" |
"coeffs (Mult e1 e2) = (coeffs e1) @ (coeffs e2)" |
"coeffs (VarPow n) = []"

fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
"evalp xs n = eval (poly xs) n"

lemma evalp_coeff : " evalp (coeffs e) x = eval e x " 
  apply(induction e arbitrary: x)
      apply(auto)
  sledgehammer
  


(*
lemma mlist2_coeff : "mlist2 (coeffs (mlist2 (a # xs) 0)) 0 = mlist2 (a # xs) 0"
  nitpick

  apply(induction xs arbitrary: a)
  apply(auto)
  oops

lemma poly_coeff : "e = poly(y) \<Longrightarrow> poly (coeffs e) = e" 
  apply(induction e arbitrary: y)
  apply(simp)
      apply(auto)
  sledgehammer
      apply (metis exp.distinct(3) mlist2.elims exp.distinct(5) mlist3.elims)
  sledgehammer
  apply (metis mlist3.elims exp.distinct(9) mlist2.elims exp.distinct(11))
*)

*)