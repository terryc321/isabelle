
theory Exercise0302
  imports Main
begin

type_synonym vname = "string"
datatype aexp = N int | V vname | Plus aexp aexp

type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (N n) s = n" |
"aval (V x ) s = s x" |
"aval (Plus a1 a2 ) s = (aval a1 s) + (aval a2 s)"

(*
Exercise 3.2. In this exercise we verify constant folding for aexp where we
sum up all constants, even if they are not next to each other. 
For example, 

Plus (N 1) (Plus (V x) (N 2)) becomes Plus (V x ) (N 3)

This goes beyond asimp.
Define a function full_asimp :: aexp \<Rightarrow> aexp that sums up all constants and
prove its correctness: aval (full_asimp a) s = aval a s.
*)

(* here is asimp as reference *)

(* an optimized version of plus - well , 
it recognises something plus zero is something*)
fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"plus (N i1 ) (N i2 ) = N (i1 + i2 )" |
"plus (N i) a = (if i = 0 then a else Plus (N i) a)" |
"plus a (N i) = (if i = 0 then a else Plus a (N i))" |
"plus a1 a2 = Plus a1 a2 "

fun asimp :: "aexp \<Rightarrow> aexp" where
"asimp (N n) = N n" |
"asimp (V x ) = V x" |
"asimp (Plus a1 a2 ) = plus (asimp a1) (asimp a2 )"

(* count number of N expressions in 
either 0 none exist 
either 1 (N i) itself
or 1 and expression is of the form Plus _ (N i)

inside object language True False \<and> \<or> 
*)

fun hasN :: "aexp \<Rightarrow> bool " where
"hasN (N n) = True" |
"hasN (V x) = False" |
"hasN (Plus a1 a2) = ((hasN a1) \<or> (hasN a2))"

fun aleafs :: "aexp \<Rightarrow> aexp list " where
"aleafs (N n) = [N n]" |
"aleafs (V x) = []" |
"aleafs (Plus a1 a2) = ((aleafs a1) @ (aleafs a2))"

fun hasN2 :: "aexp \<Rightarrow> bool " where
"hasN2 e = (case (aleafs e) of 
   [] \<Rightarrow> False |
   _ \<Rightarrow> True)"

(* has equivalence - two different ways to determine if expression has 
   any number constants 
*)
lemma hasEqv : "(hasN e) = (hasN2 e)"
proof (induction e)
  case (N x)
  then show ?case by simp
next
  case (V x)
  then show ?case by simp
next
  case (Plus e1 e2)
  then show ?case by simp
qed

value "hasN (V x)"
value "hasN (N 2)" 
value "hasN (Plus (V x) (V y))" 
value "hasN (Plus (V x) (Plus (N 1) (V y)))" 

value "aleafs (V x)"
value "aleafs (N 2)" 
value "aleafs (Plus (V x) (V y))" 
value "aleafs (Plus (V x) (Plus (N 1) (V y)))" 


(** target full_asimp 
 try move any N n to right hand of a Plus expression
*)

(* flatEn filters (N n) expression *)
fun flatEn :: "aexp \<Rightarrow> aexp list" where 
"flatEn (N n) = [N n]" |
"flatEn (V x) = []" |
"flatEn (Plus a1 a2) = (flatEn a1 @ flatEn a2)"

(* flatEv filters (V x) expressions *)
fun flatEv :: "aexp \<Rightarrow> aexp list" where 
"flatEv (N n) = []" |
"flatEv (V x) = [V x]" |
"flatEv (Plus a1 a2) = (flatEv a1 @ flatEv a2)"

(* \noteq  \<noteq> formula  *)
lemma flat_env : " flatEn e = []  \<Longrightarrow> flatEv e \<noteq> []"
proof (induction e)
  case (N x)
  then show ?case by simp
next
  case (V x)
  then show ?case by simp
next
  case (Plus e1 e2)
  then show ?case by simp
qed

thm flat_env


(* 
case analysis for full_simp 
let e be an aexp 
e can be some number n (N n)
e can be some variable x (V x)
e can be an addition (Plus a1 a2) where a1 ,a2 can be aexp themselves arbitrarily large? 
*)

(*rebuild_nums just sums up all nums *)
fun rebuild_nums :: "aexp list \<Rightarrow> aexp \<Rightarrow> aexp" where
"rebuild_nums [] acc = acc"|
"rebuild_nums (h # t) acc = 
 (case (h,acc) of 
  (N n , N i) \<Rightarrow> rebuild_nums t (N (n+i)) |
  (_ , acc) \<Rightarrow> rebuild_nums t acc
 )"

(* are we cheating rebuild_vars - we use a default value to avoid pollutions of option everywhere*)
fun rebuild_vars2 :: "aexp list \<Rightarrow> aexp \<Rightarrow> aexp" where
"rebuild_vars2 [] e = e"|
"rebuild_vars2 (h # t) e = rebuild_vars2 t (Plus e h)" 

fun rebuild_vars :: "aexp list \<Rightarrow> aexp \<Rightarrow> aexp" where
"rebuild_vars [] def = def"|
"rebuild_vars (h # t) _ = rebuild_vars2 t h" 
 
fun full_asimp :: "aexp \<Rightarrow> aexp " where
"full_asimp (N n) = N n" |
"full_asimp (V x ) = V x" |
"full_asimp (Plus a1 a2) = (
 let ns = flatEn (Plus a1 a2) ; 
 vs = flatEv (Plus a1 a2) in  
 let rns = rebuild_nums ns (N 0) in 
 let rvs = rebuild_vars vs (V ''x'') in
 case ns of 
 [] \<Rightarrow> rvs |
 xs \<Rightarrow> (case vs of 
       [] \<Rightarrow> rns |
       ys \<Rightarrow> Plus rvs rns ))" 

lemma "aval (full_asimp a) s = aval a s" 
proof (induction a arbitrary: s)
  case (N x)
  then show ?case by simp
next
  case (V x)
  then show ?case by simp
next
  case (Plus a1 a2)
  then show ?case by simp
qed

value "flatEn (V ''z'')" 
value "full_asimp (Plus (V ''x'')(V ''y''))" 


(* 
norm form 
if Plus a1 a2 contains no numbers then a1 a2 contain only vars
otherwise a1 contains no numbers and a2 is (N i)
*)

fun is_norm :: "aexp \<Rightarrow> bool" where
"is_norm (N _) = True" |
"is_norm (V _) = True" | 
"is_norm (Plus a1 a2) = ( 
   if hasN a1 then False 
   else (if hasN a2 then 
     (case a2 of 
       N i \<Rightarrow> True
      | _ \<Rightarrow> False )
   else True ))"

lemma norm : "is_norm (full_asimp a)"
proof (induction a)
  case (N x)
  then show ?case by simp
next
  case (V x)
  then show ?case by simp
next
  case (Plus a1 a2)
  then show ?case by simp
qed

thm norm
(* is_norm (full_asimp ?a) *)

(* completed exercise 3.2 *)




