
theory Chapter5
  imports Main
begin

(* chapter five of concrete semantics 
 \<lbrakk> \<rbrakk> brackets are [ |    | ] 
 \<lbrakk> P ; Q \<rbrakk>  is shorthand for P \<Longrightarrow> Q \<Longrightarrow> 
 \<lbrakk> P ; Q \<rbrakk> \<Longrightarrow> P \<and> Q  shorthand for P \<Longrightarrow> Q \<Longrightarrow> P \<and> Q
i think , not sure about \<Longrightarrow> and \<longrightarrow> difference 
 \<Longrightarrow> may be meta level 
 \<longrightarrow> may be a logic level , who knows
*)

thm HOL.conjI  
thm HOL.conjunct1
thm HOL.conjunct2

(* ?P \<Longrightarrow> ?Q \<Longrightarrow> ?P \<and> ?Q *)
(* 
conjunction introduction conjI 

   P   Q
  ------- 
   P \<and> Q 

 in proving this below 

 P \<Longrightarrow> Q \<Longrightarrow>   P \<and> Q \<and> P
 ^^^^^^^^^^^   ^^^^^^^^^
  assumptions  conclusion
  
so when we use conjI we end up working backward up the derivation tree and not
using forward reasoning , working backwards is called goal directed reasoning

given a goal , derive the assumptions or something that is obviously true like x = x 

   P \<and> Q \<Longrightarrow> P   from HOL.conjunct1 
  
   P \<and> Q \<Longrightarrow> Q   from HOL.conjunct2

*)

lemma trivial0 : " \<lbrakk> P  \<rbrakk> \<Longrightarrow> P " 
proof -
  assume P: "P"
  then show "P" by assumption
qed

(* so we have to assume "P" otherwise we have an empty set of assumptions*)

(* here we have something that has no assumptions , something 
that is forever true 
something is always equal to itself 

*)
lemma trivial_eq : " P = P " 
proof -  
  show "P = P" by (rule refl)
qed

(* this is reflexivity *)
thm refl  (* ?t = ?t *)

thm conjI (* ?P \<Longrightarrow> ?Q \<Longrightarrow> ?P \<and> ?Q *)
thm conjE (* ?P \<and> ?Q \<Longrightarrow> (?P \<Longrightarrow> ?Q \<Longrightarrow> ?R) \<Longrightarrow> ?R *)
(* conjunct1 conjunct2 only for assumptions ? *)
thm HOL.conjunct1 (* ?P \<and> ?Q \<Longrightarrow> ?P *)
thm HOL.conjunct2 (* ?P \<and> ?Q \<Longrightarrow> ?Q *)


lemma trivial_and1 : " \<lbrakk> P ; Q \<rbrakk> \<Longrightarrow> P \<and> Q "
proof -
  assume P: "P" and Q:"Q" 
  show "P \<and> Q" using \<open>P\<close> \<open>Q\<close> by (rule conjI)
qed

(* disjunction introduction *)
thm disjI1 (*?P \<Longrightarrow> ?P \<or> ?Q *)
thm disjI2 (*?Q \<Longrightarrow> ?P \<or> ?Q *)

(* given P then claim P \<or> anything! *)
lemma trivial_or1 : " \<lbrakk> P \<rbrakk> \<Longrightarrow> P \<or> False "
proof -
  assume P: "P" 
  show "P \<or> False" using \<open>P\<close> by (rule disjI1)
qed

(* given Q claim anything! \<or> Q*)
lemma trivial_or2 : " \<lbrakk> Q \<rbrakk> \<Longrightarrow> False \<or> Q "
proof -
  assume Q: "Q" 
  show "False \<or> Q" using \<open>Q\<close> by (rule disjI2)
qed


(* forward proof seems more difficult as its expecting user to put components together . 
like building lego without manual but expecting the final result
*)
lemma trivial_task1 : " \<lbrakk> P ; Q \<rbrakk> \<Longrightarrow> P \<and> (Q \<and> P) "
proof -
  assume P:"P" and Q:"Q"
  show "P \<and> (Q \<and> P)"               (* \<leftarrow> This is the important line *)
  proof -
    have QP : "Q \<and> P" using Q P by (rule conjI)
    have PQP: "P \<and> Q \<and> P" using P QP by (rule conjI) 
    then show ?thesis by assumption
  qed
qed



lemma foo : " \<lbrakk> P ; Q \<rbrakk> \<Longrightarrow> P \<and> (Q \<and> P) "
  apply(rule conjI)
  apply(assumption)
  apply(rule conjI)
  apply(assumption)
  apply(assumption)
  done

(*
lemma trivial_task2 : " \<lbrakk> P ; Q \<rbrakk> \<Longrightarrow> P \<and> (Q \<and> P) "
proof -
  assume P:"P" and Q:"Q" 
  show "P \<and> (Q \<and> P)"               (* \<leftarrow> This is the important line *)
  proof -
*)
 

(*
lemma trivial_task2 : " \<lbrakk> P ; Q \<rbrakk> \<Longrightarrow> P \<and> (Q \<and> P) "
proof -
  assume P:"P" and Q:"Q" 
  then show "P \<and> (Q \<and> P)"               (* \<leftarrow> This is the important line *)
  proof -

    have QP : "Q" by (rule conjI)
    have PQP: "P \<and> Q \<and> P" using P QP by (rule conjI) 
    then show ?thesis by assumption
  qed
qed
*)


(* increedibly detailed every step has to be meticulously clean 
  rule conjI  the arguments must come in order left to right 
   using A B by (rule conjI)  to give 

also the file has to be completely tidy at all times or cannot hope to get isabelle to accept it

*)


(* the end of the Chapter5.thy 
without the word end , isabelle build will say there
is an error
*)
end

