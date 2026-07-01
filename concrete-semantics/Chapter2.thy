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

lemma add_m_suc_m : "Suc (add m m) = add m (Suc m) "
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