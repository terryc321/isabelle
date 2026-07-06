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


(* this is the end of Chapter2 *)
end