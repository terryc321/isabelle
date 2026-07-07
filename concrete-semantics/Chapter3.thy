
(* Chapter3.thy *)

theory Chapter3
  imports Main
begin

value "( \<lambda> z .  (if z = ''x'' then 7 else if z = ''y'' then 3 else 0 :: int)) " 
value "( \<lambda> z .  (if z = ''x'' then 7 else if z = ''y'' then 3 else 0 :: int)) ''x'' "
value "( \<lambda> z .  (if z = ''x'' then 7 else if z = ''y'' then 3 else 0 :: int)) ''y'' "
value "( \<lambda> z .  (if z = ''x'' then 7 else if z = ''y'' then 3 else 0 :: int)) ''z'' "

(* value " < ''x'':= 7 , ''y'' := 3 > ''x''" *)

value "(\<lambda> x . 0 :: int) ''z''"
value "(\<lambda> x . 0 :: int) 4"
value "((\<lambda> x . 0) (''x'' := 4 )) ''x'' :: int"
value "((\<lambda> x . 0) (''x'' := 1 , ''y'' := 2)) ''x'' :: int" (* \<Longrightarrow> 1 :: int *)
value "((\<lambda> x . 0) (''x'' := 1 , ''y'' := 2)) ''y'' :: int" (* \<Longrightarrow> 2 :: int *)
value "((\<lambda> x . 0) (''x'' := 1 , ''y'' := 2)) ''z'' :: int" (* \<Longrightarrow> 0 :: int *)

lemma "(((\<lambda> x . 0) (''x'' := 1 , ''y'' := 2)) ''x'') = 1" 
  by simp
lemma "(((\<lambda> x . 0) (''x'' := 1 , ''y'' := 2)) ''y'') = 2" 
  by simp
lemma "(((\<lambda> x . 0) (''x'' := 1 , ''y'' := 2)) ''z'') = 0" 
  by simp

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

(* level one - pure machine code tactics *)
lemma asimp_const1 : "aval (asimp_const v) s = aval v s"
  by (induction v rule: asimp_const.induct , simp_all, auto split: aexp.split)

(* level one - isar flavour machine proof *)
lemma asimp_const2 : "aval (asimp_const v) s = aval v s"
proof (induction v)
  case (N x)
  then show ?case by simp
next
  case (V x)
  then show ?case by simp
next
  case (Plus v1 v2)
  then show ?case by (auto split: aexp.splits)
qed

thm TrueI
(* thm HOL.Ex  *)

lemma abs_nonneg:
  fixes x :: int
  shows "(if x < 0 then -x else x) >= 0"
proof -
  consider (Neg) "x < 0" | (NonNeg) "\<not> x < 0"
    by blast
  then show ?thesis
  proof cases
    case Neg
    then show ?thesis
      by simp
  next
    case NonNeg
    then show ?thesis
      by simp
  qed
qed



(* thm arith.simps ? *)
(* thm algebra.simps ? *)

(* goal : aval (asimp_const (N x)) s = aval (N x) s *)
(* goal : aval (N x) s = aval (N x) s *)

(*
-- from concrete-semantics page 30 -- 
= aval ai s for i =1,2. 
If asimp_const a i = N n i for i =1,2, then
aval (asimp_const (Plus a1 a2 )) s
= aval (N (n1 + n2)) s = n1 + n2
= aval (asimp_const a 1 ) s + aval (asimp_const a 2 ) s
= aval (Plus a 1 a 2 ) s
*)


lemma asimp_const3 : "aval (asimp_const v) s = aval v s"
proof (induction v)
  case (N x)  
  then show ?case 
  proof -     (* checked *)
    have "aval (asimp_const (N x)) s = aval (N x) s" 
      unfolding asimp_const.simps 
      by (rule refl)     
     then show ?case .    
    qed        (*ok*)
next
  case (V x)   (* ok *)
  then show ?case 
  proof -     (* checked - note dash after proof >>> - <<< *)
  have "aval (asimp_const (V x)) s = aval (V x) s" 
      unfolding asimp_const.simps 
      by (rule refl)     
    then show ?case .  
  qed         (* checked - note dot after ?case >>> . << *)
next
  case (Plus v1 v2)
  then show ?case 
  proof - 

  consider (BothN) n1 n2 where "asimp_const v1 = N n1" "asimp_const v2 = N n2"
  | (NotBothN) "\<not> (\<exists> n1 n2. asimp_const v1 = N n1 \<and> asimp_const v2 = N n2)"
   by blast

    then show ?case
    proof cases
      case BothN
      then show ?thesis 
      proof - 
        show ?thesis using BothN Plus.IH by simp
      qed  
    next
      case NotBothN
      then show ?thesis    
      proof - 
        show ?thesis using NotBothN Plus.IH by (auto split:aexp.split)
      qed
    qed  
  qed
qed




(* level two - human readable proof 


aval (asimp_const v) s = aval v s

induction on v 
case (N x) so v will be some number (N x) 

aval (asimp_const (N x)) s = aval (N x) s
ok - goal matches 
by asimp_const definition asimp_const (N n) = N n
so 
aval (N x) s = aval (N x) s
by asimp_const.simps 


*)



(*
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


*)

(* end of Chapter3 *)
end
