
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

  (* this is really a new one - consider *)
  consider (BothN) n1 n2 where "asimp_const v1 = N n1" "asimp_const v2 = N n2"
  | (NotBothN) "\<not> (\<exists> n1 n2. asimp_const v1 = N n1 \<and> asimp_const v2 = N n2)"
   by blast

    then show ?case
    proof cases
      case BothN
      then show ?thesis 
      proof - 
        have h3: "asimp_const (Plus v1 v2) = N (n1 + n2)"  using BothN  by simp
        then show ?thesis using BothN h3 Plus.IH by simp
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

thm ccontr

(* assumes "X"
   shows  "Y" 
rather than "X \<Rightarrow> Y" 
*)
(*
lemma asimp_const_Plus_not_both_N: 
  assumes "\<not> (\<exists>n1 n2. asimp_const v1 = N n1 \<and> asimp_const v2 = N n2)"
  shows "asimp_const (Plus v1 v2) =  Plus (asimp_const v1) (asimp_const v2)"
  print_facts
 *)



lemma asimp_const_Plus_not_both_N:
  assumes H:
    "\<not> (\<exists>n1 n2.
        asimp_const v1 = N n1 \<and>
        asimp_const v2 = N n2)"
  shows
    "asimp_const (Plus v1 v2) =
     Plus (asimp_const v1) (asimp_const v2)"
proof (cases "asimp_const v1")
  case (N x1)
  then show ?thesis 
   proof (cases "asimp_const v2")
     case (N x1)
     then show ?thesis by simp
   next
     case (V x2)
     then show ?thesis by simp
   next
     case (Plus x31 x32)
     then show ?thesis by simp
   qed
next
  case (V x2)
  then show ?thesis 
   proof (cases "asimp_const v2")
     case (N x1)
     then show ?thesis by simp
   next
     case (V x2)
     then show ?thesis by simp
   next
     case (Plus x31 x32)
     then show ?thesis by simp
   qed
next
  case (Plus x31 x32)
  then show ?thesis 
   proof (cases "asimp_const v2")
     case (N x2)
     then show ?thesis by simp
   next
     case (V x2)
     then show ?thesis by simp
   next
     case (Plus x33 x34)
     then show ?thesis by simp
   qed
qed


  case (N n1)
  then show ?thesis
  proof (cases "asimp_const v2")
    case (N n2)
    have False
      using H
      using \<open>asimp_const v1 = N n1\<close>
      using \<open>asimp_const v2 = N n2\<close>
      by blast
    then show ?thesis
      by blast
  next
    case V
    then show ?thesis
    proof (cases "asimp_const v2")
      case (N x1)
      then show ?thesis sorry
    next
      case (V x2)
      then show ?thesis sorry
    next
      case (Plus x31 x32)
      then show ?thesis sorry
    qed      
  next
    case Plus
    then show ?thesis 
    proof (cases "asimp_const v2")
      case (N x1)
      then show ?thesis sorry
    next
      case (V x2)
      then show ?thesis sorry
    next
      case (Plus x31 x32)
      then show ?thesis sorry
    qed
  qed
qed


(*
proof - 
  assume H : "\<not> (\<exists>n1 n2. asimp_const v1 = N n1 \<and> asimp_const v2 = N n2)"  
  sorry
qed
*)

(*
    "asimp_const (Plus v1 v2) =  Plus (asimp_const v1) (asimp_const v2)"
  sorry
*)



lemma asimp_const4 : "aval (asimp_const v) s = aval v s"
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

  (* this is really a new one - consider *)
  consider (BothN) n1 n2 where "asimp_const v1 = N n1" "asimp_const v2 = N n2"
  | (NotBothN) "\<not> (\<exists> n1 n2. asimp_const v1 = N n1 \<and> asimp_const v2 = N n2)"
   by blast

    then show ?case
    proof cases
      case BothN
      then show ?thesis 
      proof - 
        have h1: "asimp_const v1 = N n1" by (rule BothN)
        have h2: "asimp_const v2 = N n2" by (rule BothN)
        have h3: "asimp_const (Plus v1 v2) = N (n1 + n2)"  using h1 h2  by simp
        then show ?thesis using h1 h2 h3 Plus.IH by simp
      qed
    next
      case NotBothN
      then show ?thesis    
        using NotBothN asimp_const_Plus_not_both_N by simp
    qed
  qed
qed


(* end of Chapter3 *)
end
