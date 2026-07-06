
theory Ex304
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

lemma aval_plus [simp]:
  "aval (plus a1 a2) s = aval a1 s + aval a2 s"
  apply (induction a1 a2 rule: plus.induct)
  apply simp_all
  done 

lemma aval_times [simp]:
  "aval (times a1 a2) s = aval a1 s * aval a2 s"
  apply (induction a1 a2 rule: times.induct)
  apply simp_all 
  done

lemma aval_simp0 : "aval (asimp a) s = aval a s"
proof (induction a)
  (* Case 1: a is a number N x *)
  case (N x)
  show ?case 
    apply simp          (* both sides are just the number x *)
    done
next
  (* Case 2: a is a variable V x *)
  case (V x)
  show ?case 
    apply simp          (* both sides are just s x *)
    done
next
  (* Case 3: a is Plus a1 a2  — this is the hard one *)
  case (Plus a1 a2)  
  show ?case 
proof -
    have "aval (plus (asimp a1) (asimp a2)) s = aval (asimp a1) s + aval (asimp a2) s"  by (rule aval_plus)
    also have "... = aval a1 s + aval a2 s"  using Plus.IH by simp
    also have "... = aval (Plus a1 a2) s"  by simp
    finally show ?case  by simp_all
  qed
next
  (* Case 4: a is Times a1 a2 *)
  case (Times a1 a2)
  have "aval (times (asimp a1) (asimp a2)) s = aval (asimp a1) s * aval (asimp a2) s"   by (rule aval_times)
    also have "... = aval a1 s * aval a2 s" using Times.IH by simp
    also have "... = aval (Times a1 a2) s"  by simp
    finally show ?case by simp_all
qed


(** this is the end of the theory file **)
end