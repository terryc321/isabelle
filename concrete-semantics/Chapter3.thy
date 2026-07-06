
theory Chapter3
  imports Main
begin

type_synonym vname = "string"
datatype aexp = N int | V vname | Plus aexp aexp

value "N 5" (* represent number 5 *)
value "V ''x''" (* this is the variable x *)
value "''x''" (* this is how to write the string x *)
value "''x'' :: string" (* this is how to write a string x *)
value "(''x'' :: string) = (''x'' :: char list)" (* string is synonym for char list *)

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

fun optimal :: "aexp \<Rightarrow> bool" where
"optimal (N n)  = True" |
"optimal (V x ) = True" |
"optimal (Plus a1 a2) = (case (a1,a2) of 
    (N i, N j) \<Rightarrow> False 
    | _ \<Rightarrow> (optimal a1) \<and> (optimal a2))"

value "N x"
value "true" (* true is unknown *)
value "True" (* True has type bool *)
(* 
 cant do this has wrong type ?
 assume 0: "(N x)" 

    

    print_facts
    from 1 show ?case by (rule ssubst)

    (* Now replace in the goal *)
    from this have 2: "optimal (N x)" by (rule ssubst)
    from this have 3: "True" by (rule optimal.simps)
    
         
    
     

    show "optimal (asimp_const (N x))" using 1 by (rule 1)

      using cong
      apply (rule ssubst)
      apply (rule optimal.simps)

    assume 0: "optimal (asimp_const (N x))"
    from 0 have 1: "asimp_const (N x) = (N x) " by (simp add: asimp_const.simps(1))
    from 1 have 2: "optimal (asimp_const (N x)) = optimal (N x)" by (simp add: 1)
    from 2 have 3: "optimal (N x) = True" by (simp add: 2)
    print_facts

(* proof (state)
goal (1 subgoal):
 1. optimal (asimp_const (N x)) 
*)
    thm asimp_const.simps(1)
   (* asimp_const (N ?n) = N ?n *)

*)


lemma "\<not> surj (f :: 'a \<Rightarrow> 'a set )"
proof
assume 0: "surj f"
from 0 have 1: "\<forall> A. \<exists> a. A = f a" by(simp add: surj_def )
from 1 have 2: "\<exists> a. {x . x \<notin> f x } = f a" by blast
from 2 show "False" by blast
qed

(* 
fun optimal :: "aexp \<Rightarrow> bool" where
"optimal (N n)  = True" |
"optimal (V x ) = True" |
"optimal (Plus a1 a2) = (case (a1,a2) of 
    (N i, N j) \<Rightarrow> False 
    | _ \<Rightarrow> (optimal a1) \<and> (optimal a2))"

fun asimp_const :: "aexp \<Rightarrow> aexp" where
"asimp_const (N n)  = N n" |
"asimp_const (V x ) = V x" |
"asimp_const (Plus a1 a2 ) =
(case (asimp_const a1, asimp_const a2 ) of
      (N n1 , N n2 ) \<Rightarrow> N (n1 + n2) |
      (b1,b2 )       \<Rightarrow> Plus b1 b2 )"

lemma optimal_2 : "optimal (asimp_const v)"
is a proposition - does simplifying constants asimp_const result in an 
optimal expression ?

lemma optimal_2 : "optimal (asimp_const v)"
induction on v 
v is (N n) then 
    Prove : optimal (asimp_const (N n))
    optimal (N n) by asimp_const def
    True by optimal def
v is (V x) 
    Prove : optimal (asimp_const (V x))
    optimal (V x) by asimp_const def
    True by optimal def
v is (Plus a1 a2)
    Prove : optimal (asimp_const (Plus a1 a2))
*)


(*
lemma "\<lbrakk> optimal (asimp_const v1) ; optimal (asimp_const v2) \<rbrakk> 
       \<Longrightarrow> optimal (asimp_const (Plus v1 v2))"
proof (cases (Pair a b))
  *)

lemma optimal_3 : "optimal (asimp_const (Plus (N i) (N j)))"
  unfolding asimp_const.simps
  apply (simp)

 

lemma optimal_2 : "optimal (asimp_const v)"
proof (induction v)
  case (N x)
  then show ?case by simp
next
  case (V x)
  then show ?case by simp
next
  case (Plus a1 a2)
  then show ?case
  proof cases
    case both_nums
    (* Under this branch, asimp_const unfolds to N (n1 + n2) *)
    then show ?thesis 
      by (simp add: asimp_const.simps optimal.simps Plus.IH split: aexp.splits)
  next
    case not_both_nums
    (* Under this branch, it evaluates to Plus b1 b2 where b1,b2 are not both N *)
    then show ?thesis using Plus.IH
      by (auto simp add: asimp_const.simps optimal.simps)
  qed
qed

 

  

proof (induction v)
  case (N x)
  then show ?case 
    unfolding asimp_const.simps(1) optimal.simps
    by (rule TrueI)
next
  case (V x)
  then show ?case 
    unfolding asimp_const.simps(2) optimal.simps
    by (rule TrueI)
next
  case (Plus v1 v2)
  then show ?case 
    apply (simp add: t.splits )
    
  qed
  


(*

lemma optimal_2 :" optimal (asimp_const v) "
proof (induction v)
  case (N x)
  then show ?case
    unfolding asimp_const.simps(1) 
    unfolding optimal.simps   (* line 122 *)
    by (rule TrueI)
next 
  case (V x)
  then show ?case
    unfolding asimp_const.simps
    unfolding optimal.simps
    by (rule TrueI)
next
  case (Plus v1 v2)
  then show ?case using Plus.IH by (auto split: aexp.split)
qed
*)
(* it is not good news , isabelle build says line 122 
  Running concrete-semantics ...
concrete-semantics: theory concrete-semantics.Chapter3
concrete-semantics FAILED (see also "isabelle build_log -H Error concrete-semantics")
*** Illegal application of proof command in "state" mode
*** At command "unfolding" (line 122 of "~/code/isabelle/concrete-semantics/Chapter3.thy")
Unfinished session(s): concrete-semantics
*)

(* end of Chapter3 *)
end
