
theory Ex304Step
  imports Main
begin

type_synonym vname = "string"
datatype aexp = N int | V vname | Plus aexp aexp | Times aexp aexp

type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (N n) s = n" |
"aval (V x ) s = s x" |
"aval (Plus a1 a2 ) s = (aval a1 s) + (aval a2 s)" | 
"aval (Times a1 a2 ) s = (aval a1 s) * (aval a2 s)" 

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

lemma aval_plus : (*[simp]:*)
  "aval (plus a1 a2) s = aval a1 s + aval a2 s"
proof (induction a1 a2 rule: plus.induct)
  case (1 i1 i2)
  then show ?case  
  proof - 
    show "aval (plus (N i1) (N i2)) s = aval (N i1) s + aval (N i2) s"
    (* "aval (N (i1 + i2)) s = aval (N i1) s + aval (N i2) s" *) 
    unfolding plus.simps
    (* "i1 + i2 = i1 + i2" *) 
    unfolding aval.simps
    by (rule refl)
  qed

next
  case ("2_1" i v)
  then show ?case
  proof (cases "i = 0")   
    case True
    then show ?thesis      
    proof - 

      unfolding plus.simps 
      aval.simps if_P True add_0_left)
      show "s v = s v" by (rule refl)
    qed
  next
    case False
    then show ?thesis      
    proof (unfold plus.simps aval.simps if_not_P) 
      show "i + s v = i + s v" by (rule refl)
    qed


(*
next
  case ("2_1" i v)
  then show ?case
  proof (cases "i = 0")   
    case True
    then show ?thesis      
    proof (unfold plus.simps aval.simps if_P True add_0_left)
      show "s v = s v" by (rule refl)
    qed
  next
    case False
    then show ?thesis      
    proof (unfold plus.simps aval.simps if_not_P) 
      show "i + s v = i + s v" by (rule refl)
    qed
  *)  

(*
        (unfold plus.simps aval.simps if_P True add_0_left)
      (* 0 = 0 \<Longrightarrow> s v = s v 
       isnt this just reflexivity ?
      *)

      (* Step 1: Unfold the definition of 'plus' mechanically *)
      

      have "aval (plus (N i) (V v)) s = aval (if i = 0 then V v else Plus (N i) (V v)) s"
        by (unfold plus.simps)


      show "aval (plus (N i) (V v)) s = aval (N i) s + aval (V v) s"
      unfolding plus.simps 
      unfolding aval.simps 
      (*  aval (if i = 0 then V v else Plus (N i) (V v)) s = i + s v  *)
      have "aval (if i = 0 then V v else Plus (N i) (V v)) s = aval (V v) s"
        using True by (simp only: if_True)
      have "aval (if i = 0 then V v else Plus (N i) (V v)) s = aval (V v) s" using True by (simp only: if_P)
      (* i = 0 \<Longrightarrow> aval (V v) s = i + s v *)

      have "if i = 0 then V v else Plus (N i) (V v) = V v"  using this by (rule if_P)

      (* aval (V v) s = i + s v *)
      (* have "aval (if i = 0 then V v else Plus (N i) (V v)) s = i + s v " *)
      
      thm refl
      thm if_P 
      show "aval (plus (N i) (V v)) s = aval (N i) s + aval (V v) s"
      unfolding plus.simps 
      unfolding aval.simps 

 
      then have "..." by (simp only: if_True)
      
      have "aval (V v) s = i + s v"
        using `i = 0`
        by (simp only: if_True)

      have "aval (V v) s = i + s v" 
        using A

      by simp

      then have "aval (V v) s = i + s v"
        using `i = 0` by (simp only: ifTrue)

      by simp
      using `i=0` by (simp only: add_0_left)
      unfolding if_bool_eq_conj
      by simp
  next
    case False
    then show ?thesis
      unfolding plus.simps 
      unfolding aval.simps 
      by simp
  qed 
*)
next
  case ("2_2" i v va)
  then show ?case sorry
next
  case ("2_3" i v va)
  then show ?case sorry
next
  case ("3_1" v i)
  then show ?case sorry
next
  case ("3_2" v va i)
  then show ?case sorry
next
  case ("3_3" v va i)
  then show ?case sorry
next
  case ("4_1" v va)
  then show ?case sorry
next
  case ("4_2" v va vb)
  then show ?case sorry
next
  case ("4_3" v va vb)
  then show ?case sorry
next
  case ("4_4" v va vb)
  then show ?case sorry
next
  case ("4_5" v va vb vc)
  then show ?case sorry
next
  case ("4_6" v va vb vc)
  then show ?case sorry
next
  case ("4_7" v va vb)
  then show ?case sorry
next
  case ("4_8" v va vb vc)
  then show ?case sorry
next
  case ("4_9" v va vb vc)
  then show ?case sorry
next
  case ("4_10" va v)
  then show ?case sorry
next
  case ("4_11" va vb v)
  then show ?case sorry
next
  case ("4_12" va vb v)
  then show ?case sorry
next
  case ("4_13" vb v va)
  then show ?case sorry
next
  case ("4_14" vb vc v va)
  then show ?case sorry
next
  case ("4_15" vb vc v va)
  then show ?case sorry
next
  case ("4_16" vb v va)
  then show ?case sorry
next
  case ("4_17" vb vc v va)
  then show ?case sorry
next
  case ("4_18" vb vc v va)
  then show ?case sorry
qed

lemma aval_times [simp]:
  "aval (times a1 a2) s = aval a1 s * aval a2 s"
  sorry

lemma aval_simp0 : "aval (asimp a) s = aval a s"
  sorry
*)


(** this is the end of the theory file **)
end