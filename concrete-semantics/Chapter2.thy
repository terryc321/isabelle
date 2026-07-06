(*  Title:      Concrete-Semantics/Chapter2.thy
    Author:     Terry Cadd
    Date:       05/07/2026  5th july 2026
*)

section \<open>Chapter2\<close>

theory Chapter2
  imports Main
begin

(* Exercise 2.1. Use the value command to evaluate the following expressions:
"1 + (2::nat)", "1 + 
(2::int)", "1 − (2::nat)" and "1 − (2::int)".
*)

value "1 + (2::nat)"
value "1 + (2::int)"
value "1 - (2::nat)"
value "1 - (2::int)"

(* Exercise 2.2. Start from the definition of add given above. Prove that add
is associative and commutative. 
Define a recursive function double :: nat \<Rightarrow> nat and prove double m = add m m.
*)

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc(add m n)"

(* associativity goes through easy *)
lemma add_assoc: "add (add a b) c = add a (add b c)"
proof(induction a b arbitrary: c rule: add.induct)
  case (1 n)
  then show ?case by auto
next
  case (2 m n)
  then show ?case by auto
qed

(* simple fact from add definition extends to *)
lemma add_0 : "add a 0 = add 0 a"
proof (induction a)
  case 0
  then show ?case 
    by simp
next
  case (Suc a)
  then show ?case 
     by simp
qed

lemma add_suc : "add a (Suc b) = Suc (add a b)"
proof (induction a b rule: add.induct)
  case (1 n)
  then show ?case by simp
next
  case (2 m n)
  then show ?case by simp
qed

lemma add_suc2 : "add (Suc a) b = Suc (add a b)"
proof (induction a b rule: add.induct)
  case (1 n)
  then show ?case by simp
next
  case (2 m n)
  then show ?case by simp
qed

lemma add_suc3 : "add (Suc a) b = add a (Suc b)"
  by (simp add: add_suc)
  
lemma add_com : "add a b = add b a"
proof (induction a b rule: add.induct)
  case (1 n)
  then show ?case 
    by (simp add: add_0)
next
  case (2 m n)
  then show ?case 
    by (simp add: add_suc)
qed

(* proving a random addition puzzle *)
lemma add_suc9 : "add (Suc a) b = add b (Suc a)"
  by (simp add: add_com)

(*exercise 2.2 cont/d *)
fun double :: "nat \<Rightarrow> nat " where
"double 0 = 0" |
"double (Suc m) = add (Suc m) (Suc m)" 

lemma "double m = add m m"
proof (induction m)
  case 0
  then show ?case by simp
next
  case (Suc m)
  then show ?case by simp
qed

(* exercise 2.3 *)

fun count :: " 'a \<Rightarrow> 'a list \<Rightarrow> nat " where
"count x [] = 0" |
"count x (h # t) = (if x = h 
                   then 1 + (count x t) 
                   else count x t)" 

lemma count_length : "count x xs \<le> length xs" 
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

fun snoc :: " 'a list \<Rightarrow> 'a \<Rightarrow> 'a list " where
"snoc [] x = [x] " |
"snoc (h # t) x = h # (snoc t x)" 

fun reverse :: " 'a list \<Rightarrow> 'a list " where
"reverse [] = [] " |
"reverse (h # t) = snoc (reverse t) h" 

value "snoc [1,2,3] 4 :: int list"
value "reverse (snoc [1,2,3] 4) :: int list"

lemma snoc_append: "snoc xs a = append xs [a]"
  by (induction xs , auto)

(* ok that surprised me it worked*)
lemma reverse_append2: "reverse (append x y) = append (reverse y) (reverse x) " 
  by (induction x , auto , simp add: snoc_append)

(**** this is the target to prove ****)
lemma reverse_reverse : "reverse (reverse xs) = xs" 
  by (induction xs , simp_all add: snoc_append reverse_append2)

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
  by (induction n , auto)


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
  by (induction x, simp_all)

lemma "treesum t = listsum (contents t)"
  by (induction t, simp_all add: listsum_dist)

(* isar structured proof will be much longer than a one line solution 
  also much harder to understand whats allowed or not
*)



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
  by (induction t , auto)


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
  by (induction xs rule: intersperse.induct , auto)


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
  by (induction m arbitrary: n , simp_all add: add_suc)

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
  by (induction n , auto)

lemma nodex_step2: "nodex (Suc (m + m)) n = Suc (2 * nodex m n)"
  by (induction n , auto)


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


(** only exercise 2.11 outstanding 
some starter notes in Chapter2.txt 
**)



(* this is the end of Chapter2 *)
end