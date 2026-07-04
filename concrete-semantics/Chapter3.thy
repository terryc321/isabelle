
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


lemma aval_1 : " aval (asimp_const (N x)) s = aval (N x) s "
proof (induction x)
  case (nonneg n)
  then show ?case (* aval (asimp_const (N (int n))) s = 
                     aval (N (int n)) s *)
      unfolding asimp_const.simps (* aval (N (int n)) s = 
                                     aval (N (int n)) s *)
      by (rule refl)
next
  case (neg n)
  then show ?case (* aval (asimp_const (N (- int (Suc n)))) s = 
                     aval (N (- int (Suc n))) s *)
    unfolding asimp_const.simps (*aval (N (- int (Suc n))) s = 
                                  aval (N (- int (Suc n))) s*)
    by (rule refl)
qed


lemma aval_2 : " aval (asimp_const (N x)) s = aval (N x) s "
proof
  unfolding asimp_const.simps
  by (rule refl)
qed 

(* 
      unfolding asimp_const.simps aval.simps
      by (rule refl)
      then have "a2 = N x1" by simp  
*)
lemma aval_3 : "aval (asimp_const (Plus a1 a2)) s = aval (Plus a1 a2) s"
proof (induction a1)
  case (N x)  
  then show ?case 
  proof (cases a2)
    case (N x1)
    then show ?thesis
    by (rule refl)
  next
    case (V x2)
    then show ?thesis
      unfolding asimp_const.simps aval.simps  
      by simp       
  next
    case (Plus x31 x32)
    then show ?thesis 
      by simp
  qed    
next
  case (V x)
  then show ?case
  proof (cases a2)
    case (N x1)
    then show ?thesis
    by (rule refl)
  next
    case (V x2)
    then show ?thesis
      unfolding asimp_const.simps aval.simps  
      by simp       
  next
    case (Plus x31 x32)
    then show ?thesis 
      by simp
  qed
  case (Plus a11 a22 )
  then show ?case
  proof (cases a2)
    case (N x1)
    then show ?thesis 
      by simp
  next
    case (V x2)
    then show ?thesis 
      by simp
  next
    case (Plus x31 x32)
    then show ?thesis
      unfolding aval.simps  
      by simp
  qed  
  qed


(* this statement tries to show the simplification asimp_const 
does not alter its evaluation under aval *)
lemma "aval (asimp_const a) s = aval a s"
proof (induction a)
  case (N x)
  then show ?case (* aval (asimp_const (N x)) s = aval (N x) s *)
    by aval_2 
next
  case (V x)
  then show ?case 
    unfolding asimp_const.simps
    by (rule refl)
next
  case (Plus a1 a2)
  then show ?case (* aval (asimp_const (Plus a1 a2)) s = aval (Plus a1 a2) s *)
    by aval_3
qed


(* 
apply (induction a)
apply (auto split : aexp.split )
done
*)

(* an optimized version of plus - well , it recognises something plus zero is something*)
fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"plus (N i1 ) (N i2 ) = N (i1 + i2 )" |
"plus (N i) a = (if i = 0 then a else Plus (N i) a)" |
"plus a (N i) = (if i = 0 then a else Plus a (N i))" |
"plus a1 a2 = Plus a1 a2 "

lemma aval_plus: "aval (plus a1 a2 ) s = aval a1  s + aval a2 s"
proof (induction a1)
  case (N x)
  then show ?case 
    by simp
next
  case (V x)
  then show ?case 
    by simp
next
  case (Plus a11 a12)
  then show ?case 
    by simp
qed


fun asimp :: "aexp \<Rightarrow> aexp" where
"asimp (N n) = N n" |
"asimp (V x ) = V x" |
"asimp (Plus a1 a2 ) = plus (asimp a1) (asimp a2 )"

lemma "aval (asimp a) s = aval a s"
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
qed


(* 
Exercise 3.1. To show that asimp_const really folds all subexpressions of
the form Plus (N i ) (N j ), 
define a function optimal :: aexp \<Rightarrow> bool that
checks that its argument does not contain a subexpression of the form Plus
(N i ) (N j ). 
Then prove optimal (asimp_const a).
*)

value " false :: bool " 
value " true :: bool "

(*
fun optimal :: "aexp \<Rightarrow> bool" where
"optimal (N n) = false" |
"optimal (V x ) = false" |
"optimal (Plus a1 a2 ) = (case (optimal a1,optimal a2) of
 (true,_) \<Rightarrow> true 
 | (_ , true) \<Rightarrow> true 
 | _ \<Rightarrow> (case (a1,a2) of 
        (N i, N j) \<Rightarrow> true 
        | _ \<Rightarrow> false ))" 
*)

(*
fun optimal :: "aexp \<Rightarrow> bool" where
"optimal (N n)  = True" |
"optimal (V x ) = True" |
"optimal (Plus a1 a2 ) = (case (a1,a2) of 
   (N i, N j) \<Rightarrow> False 
        | _ \<Rightarrow> (optimal a1) \<and> (optimal a2))" 
*)

fun optimal :: "aexp \<Rightarrow> bool" where
"optimal (N n)  = True" |
"optimal (V x ) = True" |
"optimal (Plus a1 a2) = (case (a1,a2) of 
    (N i, N j) \<Rightarrow> False 
    | _ \<Rightarrow> (optimal a1) \<and> (optimal a2))"


lemma optimal_1 :" optimal (asimp_const a) "
proof (induction a)
  case (N x)
  then show ?case 
    unfolding asimp_const.simps
    unfolding optimal.simps
    by (rule trueI) (* True is True by the axiom true introduction trueI*)  
next
  case (V x)
  then show ?case 
    unfolding asimp_const.simps
    unfolding optimal.simps
    by (rule trueI) (* True is True by the axiom true introduction trueI*)
next
  case (Plus a1 a2)
  then show ?case 
  proof (cases "(asimp_const a1 , asimp_const a2)")
    case (Pair a b)
    then show ?thesis 
      by simp
  qed
qed


lemma f3 :
  assumes H : "x = 3"  
  shows "f x = f 3" 
proof -
  from H show ?thesis 
    apply (subst (1) H)
    by (rule refl)
qed

lemma f3b :
  assumes H : "x = 3"  
  shows "f x = f 3"  
proof
  by (simp add: HOL.arg_cong)


lemma f3c :
  assumes H : "x = 3"  
  shows "f x = f 3"   
  by (simp add: HOL.arg_cong)




(*
 (subst (1) H)
  by (rule refl)
qed

*)


(* 
lemma f3 :
  assumes H : "x = 3"  
  shows "f x = f 3" 
proof 
  shows "f 3 = f 3 " 
proof
    by apply (subst (1) H) 
  by (rule refl)
qed
qed
*)


value "3 :: int "

(*
  from H show?thesis
    apply (subst (1) H)   (* substitute 1st occurrence of x in f x = f 3 theres only one here *)
    by (rule refl)
    using H have "f 3 = f 3" 
*)
    


(*
lemma
  assumes H : "x = 3"  
  shows "f x = f 3"
proof -
  from H show?thesis
    apply (subst (1) H)   (* substitute 1st occurrence of x in f x = f 3 theres only one here *)
    using H 
    
    using this 
   (* using H by simp only *)
    (* print_facts *)
*)
 
    
    
  
  
   

  
  
  


lemma optimal_2 : " optimal (asimp_const a) "
proof (induction a)
  case (N x)
  then show ?case 
    unfolding asimp_const.simps
    unfolding optimal.simps
    by (rule trueI) (* True is True by the axiom true introduction trueI*)  
next
  case (V x)
  then show ?case 
    unfolding asimp_const.simps
    unfolding optimal.simps
    by (rule trueI) (* True is True by the axiom true introduction trueI*)
next
  case (Plus a1 a2)  
  then show ?case 
    by simp
qed


(*      simp add: "asimp_const a1 = N x1" 

  proof (cases "asimp_const a1")
    case (N x1)
    note eq = this
    then show ?thesis 
      unfolding asimp_const.simps
      (*apply simp*)
      apply (subst eq)
      apply simp


*)

(*      have ass "asimp_const a1 = N x1" 
        using that subst ass 
        using that by subst
  using that by simp

      from this have ... 

      subst (asm) "asimp_const a1 = N x1"
*)

(*
      by simp
  next
    case (V x2)
    then show ?thesis 
      unfolding asimp_const.simps
      by simp
  next
    case (Plus x31 x32)
    then show ?thesis 
      unfolding asimp_const.simps
      by simp
  qed  
qed
*)



 






