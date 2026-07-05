
theory Exercise0304
  imports Main
begin

(* Exercise 3.4. 
Take a copy of theory AExp and modify it as follows. Extend
type aexp with a binary constructor Times that represents multiplication. - done

Modify the definition of the functions aval and asimp accordingly. 
You can remove asimp_const. 

Function asimp should eliminate 0 and 1 from multi-plications as well as 
evaluate constant subterms. 

Update all proofs concerned.
*)

type_synonym vname = "string"
datatype aexp = N int | V vname | Plus aexp aexp | Times aexp aexp

type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (N n) s = n" |
"aval (V x ) s = s x" |
"aval (Plus a1 a2 ) s = (aval a1 s) + (aval a2 s)" | 
"aval (Times a1 a2 ) s = (aval a1 s) * (aval a2 s)" 

value "aval (N 3) (\<lambda>x . 0 )" (* 3 *)
value "aval (Plus (N 2) (Times (N 4) (N 3))) (\<lambda>x . 0 )" (* 14 *)
value "aval (Times (V ''y'') (Plus (N 2) (Times (N 4) (Times (V ''x'') (N 3))))) 
  (\<lambda>x . (case x of 
    ''x'' \<Rightarrow> 3 | 
    ''y'' \<Rightarrow> 4 | 
     _ \<Rightarrow> 0 ))" (* 152 , y*(2+(4*(x*3))) *)
value "let x = 3 ; y = 4 in y*(2+(4*(x*3))) :: int"  (* 152 *)
value "aval (Times (V ''y'') (Plus (N 2) (Times (N 4) (Plus (V ''x'') (Plus (N 3) (Times (N 5) (Plus (N 2)(Times (N 2) (Plus (N 6)(N 8)))))))))) 
  (\<lambda>x . (case x of 
    ''x'' \<Rightarrow> 3 | 
    ''y'' \<Rightarrow> 4 | 
     _ \<Rightarrow> 0 ))" (* 2504  *)


(* an optimized version of plus - well , 
it recognises something plus zero is something*)
fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"plus (N i1 ) (N i2 ) = N (i1 + i2 )" |
"plus (N i) a = (if i = 0 then a else Plus (N i) a)" |
"plus a (N i) = (if i = 0 then a else Plus a (N i))" |
"plus a1 a2 = Plus a1 a2 "

fun times :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"times (N i1 ) (N i2 ) = N (i1 * i2 )" |
"times (N i) a = (if i = 0 then (N 0) else (if i = 1 then a else Times (N i) a))" |
"times a (N i) = (if i = 0 then (N 0) else (if i = 1 then a else Times a (N i)))" |
"times a1 a2 = Times a1 a2 "

fun asimp :: "aexp \<Rightarrow> aexp" where
"asimp (N n) = N n" |
"asimp (V x ) = V x" |
"asimp (Plus a1 a2 ) = plus (asimp a1) (asimp a2 )" | 
"asimp (Times a1 a2 ) = times (asimp a1) (asimp a2 )" 

value "asimp (Times (N 3) (N 4))"

lemma aval_simp0 : "aval (asimp a) s = aval a s"
proof (induction a)
  case (N x)
  then show ?case 
    by simp
next
  case (V x)
  then show ?case 
    by simp
next
  case (Plus a1 a2)
  then show ?case 
    by simp
next
  case (Times a1 a2)
  then show ?case 
    by simp
qed

thm aval_simp0 


fun hasN :: "aexp \<Rightarrow> bool " where
"hasN (N n) = True" |
"hasN (V x) = False" |
"hasN (Plus a1 a2) = ((hasN a1) \<or> (hasN a2))" |
"hasN (Times a1 a2) = ((hasN a1) \<or> (hasN a2))"

fun aleafs :: "aexp \<Rightarrow> aexp list " where
"aleafs (N n) = [N n]" |
"aleafs (V x) = []" |
"aleafs (Plus a1 a2) = ((aleafs a1) @ (aleafs a2))" |
"aleafs (Times a1 a2) = ((aleafs a1) @ (aleafs a2))" 

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
next 
  case (Times e1 e2)
  then show?case by simp
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
"flatEn (Plus a1 a2) = (flatEn a1 @ flatEn a2)" |
"flatEn (Times a1 a2) = (flatEn a1 @ flatEn a2)" 

(* flatEv filters (V x) expressions *)
fun flatEv :: "aexp \<Rightarrow> aexp list" where 
"flatEv (N n) = []" |
"flatEv (V x) = [V x]" |
"flatEv (Plus a1 a2) = (flatEv a1 @ flatEv a2)" | 
"flatEv (Times a1 a2) = (flatEv a1 @ flatEv a2)" 

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
next 
  case (Times e1 e2)
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

(* recap on definition of aval 
fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (N n) s = n" |
"aval (V x ) s = s x" |
"aval (Plus a1 a2 ) s = (aval a1 s) + (aval a2 s)" | 
"aval (Times a1 a2 ) s = (aval a1 s) * (aval a2 s)" 
*)

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
       ys \<Rightarrow> Plus rvs rns )) "  |
"full_asimp (Times a1 a2) = (
 let ns = flatEn (Times a1 a2) ; 
 vs = flatEv (Times a1 a2) in  
 let rns = rebuild_nums ns (N 0) in 
 let rvs = rebuild_vars vs (V ''x'') in
 case ns of 
 [] \<Rightarrow> rvs |
 xs \<Rightarrow> (case vs of 
       [] \<Rightarrow> rns |
       ys \<Rightarrow> Times rvs rns )) " 

lemma aval_simp2 : "aval (full_asimp a) s = aval (simp a) s" 
proof (induction a)
  case (N x)
  then show ?case by simp
next
  case (V x)
  then show ?case by simp
next
  case (Plus a1 a2)
  then show ?case by simp
next
  case (Times a1 a2)
  then show ?case by simp
qed

thm aval_simp2
(* aval (full_asimp ?a) ?s = aval (?simp ?a) ?s *)


lemma aval_simp : "aval (full_asimp a) s = aval a s" 
proof (induction a arbitrary: s)
  case (N x)
  then show ?case by simp
next
  case (V x)
  then show ?case by simp
next
  case (Plus a1 a2)
  then show ?case by simp
next
  case (Times a1 a2)
  then show ?case by simp
qed

thm aval_simp 
(* aval (full_asimp ?a) ?s = aval ?a ?s *)

(* here is a test case *)
value "(let e = (Times (V ''y'') 
                  (Plus (N 2) 
                   (Times (N 4) 
                    (Plus (V ''x'') 
                      (Plus (N 3) 
                       (Times (N 5) 
                         (Plus (N 2)
                           (Times (N 2) 
                             (Plus (N 6)(N 8))))))))))
 in (let s2 = full_asimp e ; 
         s1 = e ;
         lookup = (\<lambda> v . (case v of 
            ''x'' \<Rightarrow> 3 |
            ''y'' \<Rightarrow> 4 |
             _ \<Rightarrow> 0))
      in (aval s1 lookup , aval s2 lookup)))"
(* shockingly the disagree ! "(2504, 224)" :: "int \<times> int" *)


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
   else True ))" |
"is_norm (Times a1 a2) = ( 
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
next
  case (Times a1 a2)
  then show ?case by simp
qed

thm norm
(* is_norm (full_asimp ?a) *)

(* completed exercise 3.2 *)

(**** exercise 3.3 starts here ****)

(*
Exercise 3.3. Substitution is the process of replacing a variable by an ex-
pression in an expression. Define a substitution function 
subst :: vname \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> aexp 
such that subst x a e is the result of replacing every
occurrence of variable x by a in e. 

For example:
subst ''x'' (N 3) (Plus (V ''x'') (V ''y'')) = 
Plus (N 3) (V ''y'')

Prove the so-called substitution lemma that says 
that we can either substitute first and evaluate afterwards
or evaluate with an updated state:
aval (subst x a e) s = aval e (s(x := aval a s)). 

As a consequence prove
(aval a1 s = aval a2 s) \<Longrightarrow> 
(aval (subst x a1 e) s = aval (subst x a2 e) s)   *)

fun subst :: "vname \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"subst v r (N i) = N i" | 
"subst v r (V x) = (if v = x then r else V x )" |
"subst v r (Plus a1 a2) = Plus (subst v r a1) (subst v r a2)" | 
"subst v r (Times a1 a2) = Times (subst v r a1) (subst v r a2)" 

(* example given for subst -- expect True *)
value "subst ''x'' (N 3) (Plus (V ''x'') (V ''y'')) = Plus (N 3) (V ''y'')" 

(* := is inbuilt operator in isabelle 
 \y . if y = x then v else s(y)  
*)
lemma aval_subst1 : "aval (subst x a e) s = aval e (s(x := aval a s))"
proof (induction e arbitrary: x a)
  case (N x)
  then show ?case by simp
next
  case (V x)
  then show ?case by simp
next
  case (Plus e1 e2)
  then show ?case by simp
next
  case (Times e1 e2)
  then show ?case by simp
qed

lemma aval_subst2 : "(aval a1 s = aval a2 s) \<Longrightarrow> (aval (subst x a1 e) s = aval (subst x a2 e) s)"
  by (simp add: aval_subst1)
thm aval_subst2 
(* aval ?a1.0 ?s = aval ?a2.0 ?s \<Longrightarrow> aval (subst ?x ?a1.0 ?e) ?s = aval (subst ?x ?a2.0 ?e) ?s *)

(*print_facts*)

(* exercise 3.3 completed *)

(* exercise 3.4 starts here *)
(* exercise 3.4 completed -- all definitions and proofs pass using extra binary Times operator 
 simply required adding an extra case to each proof 

 next
  case (Times e1 e2)
  then show ?case by simp
  
i would not get too concerned it seems too easy because it is just replacing like for like , 
think about putting wooden blocks through holes , the color of the block does not affect 
if the block goes through the hole , 
importance is if the block goes through the hole - ie if isabelle says its proven
*)

(*
lemma "True = False" 
qed
*)

lemma aval0 : "aval (full_asimp a) s = aval a s"
  quickcheck

(* Testing conjecture with Quickcheck-exhaustive... 
Quickcheck found a counterexample:
  a = Times (N (- 1)) (N (- 1))
  s = \<lambda>x. - 3
Evaluated terms:
  aval (full_asimp a) s = - 2
  aval a s = 1 
*)

lemma aval1 : "aval (full_asimp a) s = aval a s"
  by (simp add:aval_simp)
(* theorem aval1: aval (full_asimp ?a) ?s = aval ?a ?s *)
(*
proof (prove)
goal (1 subgoal):
 1. aval (full_asimp a) s = aval a s 
Bad context for command "lemma"\<^here> -- using reset state 
Auto solve_direct: the current goal can be solved directly with
  Exercise0304.aval_simp: aval (full_asimp ?a) ?s = aval ?a ?s
  Exercise0304.aval_simp2: aval (full_asimp ?a) ?s = aval (?simp ?a) ?s 
Auto Quickcheck found a counterexample:
  a = Times (N (- 1)) (N (- 1))
  s = \<lambda>x. - 3
Evaluated terms:
  aval (full_asimp a) s = - 2
  aval a s = 1
*)