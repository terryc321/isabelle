
theory Chapter4
  imports Main
begin

(* 4.4 Single step proofs 

P \<and> Q \<Longrightarrow> P

*)

(*
$$A \Longrightarrow B \Longrightarrow C \Longrightarrow D$$This means: 
"Given $A$, $B$, and $C$, you can conclude $D$."Because writing a long chain of \<Longrightarrow> arrows 
can get ugly and hard to track, 
Isabelle allows you to group all the premises inside \<lbrakk> ... \<rbrakk>, separated by semicolons:

"\<lbrakk> A; B; C \<rbrakk> \<Longrightarrow> D"
 \<Longrightarrow>  \Longrightarrow    means implies  

we can interchange elim with rule , ok 
we can just use simp 
*)

lemma "\<lbrakk> P \<and> Q \<rbrakk> \<Longrightarrow> P" 
proof -
  assume "P \<and> Q"
  then show "P" 
    by (elim conjE)     
qed


lemma "\<lbrakk> P \<and> Q \<rbrakk> \<Longrightarrow> P" 
proof -
  assume "P \<and> Q"
  then show "P" 
    by (rule conjE)     
qed


lemma "\<lbrakk> P \<and> Q \<rbrakk> \<Longrightarrow> P"
  by simp

lemma "\<lbrakk> P \<and> Q \<rbrakk> \<Longrightarrow> Q"
  by simp

(* we can see the conjunction elimination theorem by saying thm conjE *)
thm conjE 

lemma "Explicit_Style": "\<lbrakk> P \<and> Q \<rbrakk> \<Longrightarrow> P"
proof -
  assume h: "P \<and> Q"
  print_facts
  show "P" using h by (rule conjE)
qed

lemma "Explicit_Style2": "\<lbrakk> P \<and> Q \<rbrakk> \<Longrightarrow> P"
proof -
  assume h: "P \<and> Q"
  show "P" using this by (rule conjE)
qed

lemma "Explicit_Style3": "\<lbrakk> P \<and> Q \<rbrakk> \<Longrightarrow> P"
proof -  
  show "P" by (rule conjE)
qed



