
(* Chapter3.thy *)

theory Chapter3
  imports Main
begin

type_synonym vname = "string"
datatype aexp = N int | V vname | Plus aexp aexp

(* multiple expressions like vname \<Rightarrow> val , we put quotes around it 
we will see if it causes problems later on *)
type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (N n) s = n" |
"aval (V x ) s = s x" |
"aval (Plus a1 a2 ) s = (aval a1 s) + (aval a2 s)"

(* one comment on use pdf pretty-printed code is that copy paste does not work into isabelle
there is artifacts left over and will not parse *)
value "aval (Plus (N 3) (V ''x'')) (\<lambda>x . 0)" (* returns 3 *)

fun asimp_const :: "aexp \<Rightarrow> aexp" where
"asimp_const (N n)  = N n" |
"asimp_const (V x ) = V x" |
"asimp_const (Plus a1 a2 ) =
(case (asimp_const a1, asimp_const a2 ) of
      (N n1 , N n2 ) \<Rightarrow> N (n1 + n2) |
      (b1,b2 )       \<Rightarrow> Plus b1 b2 )"

lemma asimp_const1 : "aval (asimp_const v) s = aval v s"
  by (induction v rule: asimp_const.induct , simp_all, auto split: aexp.split)

(* an optimized version of plus - well , it recognises something plus zero is something*)
fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"plus (N i1 ) (N i2 ) = N (i1 + i2 )" |
"plus (N i) a = (if i = 0 then a else Plus (N i) a)" |
"plus a (N i) = (if i = 0 then a else Plus a (N i))" |
"plus a1 a2 = Plus a1 a2 "

lemma aval_plus: "aval (plus a1 a2 ) s = aval a1  s + aval a2 s"
  by( induction a1 rule: plus.induct , simp_all)

fun asimp :: "aexp \<Rightarrow> aexp" where
"asimp (N n) = N n" |
"asimp (V x ) = V x" |
"asimp (Plus a1 a2 ) = plus (asimp a1) (asimp a2 )"

lemma asimp1 : "aval (asimp a) s = aval a s"
  by (induction a rule: asimp.induct , simp_all add: aval_plus)


(* 
Exercise 3.1. To show that asimp_const really folds all subexpressions of
the form Plus (N i ) (N j ), 
define a function optimal :: aexp \<Rightarrow> bool that
checks that its argument does not contain a subexpression 
of the form Plus (N i ) (N j ). 
Then prove optimal (asimp_const a).
*)

(* 
bothNumbers is a helper routine because cannot pattern match on 
right hand side of optimal (Plus a1 a2) = if a1 = (N i) & a2 = (N j) then False ...
so we wrote bothNumbers hopefully get us over this hurdle
*)
fun bothNumbers :: "aexp \<Rightarrow> aexp \<Rightarrow> bool" where 
"bothNumbers (N _)(N _) = True"
| "bothNumbers _ _ = False" 

fun optimal :: "aexp \<Rightarrow> bool" where
"optimal (N n)  = True" |
"optimal (V x ) = True" |
"optimal (Plus a1 a2) = (if bothNumbers a1 a2 then False 
                       else (optimal a1) & (optimal a2))"

(* & and \<and> seem to be logically equivalent *)
lemma and1 : " (P & Q) = (P \<and> Q) "
  by simp
  

lemma "optimal (asimp_const a)"
proof(induction a)
  case (N x)
  then show ?case by simp
next
  case (V x)
  then show ?case by simp
next
  case (Plus a1 a2)
  then show ?case by (auto split: aexp.splits) 
qed


(* 
Exercise 3.2. In this exercise we verify constant folding for aexp where we
sum up all constants, even if they are not next to each other. 
For example, Plus (N 1) (Plus (V x ) (N 2)) becomes Plus (V x ) (N 3). 
This goes beyond asimp.
Define a function full_asimp :: aexp \<Rightarrow> aexp that sums up all constants and
prove its correctness: aval (full_asimp a) s = aval a s.
*)

(* has constants (N i) *)
fun hasN :: "aexp \<Rightarrow> bool" where
"hasN (N _) = True"
| "hasN (V _) = False" 
| "hasN (Plus a b) = (hasN a \<or> hasN b)" 

fun totN :: "aexp \<Rightarrow> int" where 
"totN (N i) = i"
| "totN (V _) = 0"
| "totN (Plus a b) = (totN a) + (totN b)"

fun simpAdd :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"simpAdd (N i)(N j) = N (i+j)" 
| "simpAdd _ _ = N 0" (* dummy case ? *)

fun isNum :: "aexp \<Rightarrow> bool" where
"isNum (N _) = True"
| "isNum _ = False" 

(* *)
fun lowN :: "aexp \<Rightarrow> aexp" where
"lowN (N i) = N i"
| "lowN (V x) = V x"
| "lowN (Plus a b) = (if isNum a then b else 
                          (if isNum b then a
                           else (let sa = lowN a ;
                                     sb = lowN b in 
                               Plus sa sb)))"

value "lowN (N 3)"
value "lowN (Plus (N 3)(N 4))"


fun full_asimp :: "aexp \<Rightarrow> aexp" where
"full_asimp (N n)  = N n" |
"full_asimp (V x ) = V x" |
"full_asimp (Plus a1 a2 ) = (let s1 = full_asimp a1 ; 
                                 s2 = full_asimp a2 in
                           if bothNumbers s1 s2 then simpAdd s1 s2
                           else Plus s1 s2)"




(* end of Chapter3 *)
end
