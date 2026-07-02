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

value "eval Var 3" 
value "eval (Const 5) 3"
value "eval (Add Var Var) 3"

(* an expression simplifier *)

fun simp :: "exp \<Rightarrow> exp" where 
"simp Var = Var" |
"simp (Const i) = Const i" |
"simp (Add e1 e2) = ( 
  let s1 = simp e1 ;    s2 = simp e2 in
 if s1 = Const 0 then s2 
 else if s2 = Const 0 then s1 
 else case (s1,s2) of 
  (Const a, Const b) \<Rightarrow> Const (a + b)
  | _ \<Rightarrow> Add s1 s2 )" |
"simp (Mult e1 e2) = ( 
  let s1 = simp e1 ;  s2 = simp e2 in
 if s1 = Const 0 then Const 0
 else if s2 = Const 0 then Const 0 
 else case (s1,s2) of 
  (Const a, Const b) \<Rightarrow> Const (a * b)
  | _ \<Rightarrow> Mult s1 s2 )" 


(*
let rec keep_simp (e:expr) =
  let e1 = simp e in
  let e2 = simp e1 in
  if e1 = e2 then e2 else keep_simp e2
  *)


(*
Define a function evalp :: int list \<Rightarrow> int \<Rightarrow> int that evaluates a polynomial at
the given value. 
*)

fun evalph2 :: "int list \<Rightarrow> exp \<Rightarrow> exp \<Rightarrow> exp" where
"evalph2 [] e acc = acc"  |
"evalph2 (h # t) e acc = evalph2 t (Mult e Var) (Add (Mult (Const h) e) acc)"

fun evalph :: "int list \<Rightarrow> exp " where
"evalph e = evalph2 e (Const 1) (Const 0)" 

fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
"evalp xs x = eval (evalph xs) x" 

value "evalph [4,2,-1,3] " (* 3x^3 -x^2 + 2x + 4 *)
value "evalp [4,2,-1,3] 3" (* 82 *)

(*
Define a function 

coeffs :: exp \<Rightarrow> int list 

that transforms an expression into a polynomial. 
This may require auxiliary functions. Prove that coeffs preserves the value of the expression: 

evalp (coeffs e) x = eval e x.

Hint: consider the hint in Exercise 2.10.
*)

fun coeffsh :: "exp \<Rightarrow> int " where
"coeffsh (Const a) = a" | 
"coeffsh (Mult e1 e2) = (coeffsh e1) * (coeffsh e2)" |
"coeffsh _ = 1 "

(* this is going to be painful *)
fun coeffs2 :: "exp \<Rightarrow> int list" where 
"coeffs2 (Add e1 e2) = (coeffsh e1) # (coeffs2 e2)" | 
"coeffs2 (Const a) = [a]" | 
"coeffs2 _ = [] "

fun coeffs :: "exp \<Rightarrow> int list " where  
"coeffs e = List.rev (coeffs2 e)" 

(* coeffs fails on constant 1 ?*)
value "coeffs (Const 1)"


(** 
whilst true - we only interested in expressions generated by evalph
e = Mult (Const 1) (Const 1)
x = 2
**)
value "evalp (coeffs (Mult (Const 1) (Const 1))) 2" (* 0 *)
value "eval (Mult (Const 1) (Const 1)) 2" (* 1 *)

(*
Auto Quickcheck found a counterexample:
  xs = [- 1]
  x = - 2
Evaluated terms:
  evalp (coeffs (evalph xs)) x = 2
  eval (evalph xs) x = - 1
*)
value "evalph [ -1 ]"
value "coeffs (evalph [ -1 ])" 

(*power operator defined*)
value "2 ^ 3 :: int" 


(** target 
replace e by evalph xs 
**)
lemma eval_coeffs : "evalp (coeffs (evalph xs)) x = eval (evalph xs) x"
  nitpick
  oops

(*
  apply(induction e arbitrary: x)
     apply(auto)
  apply(simp add: arith_simps)
*)

