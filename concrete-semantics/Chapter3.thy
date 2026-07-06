
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

lemma "aval (asimp_const v) s = aval v s"
  by (induction v rule: asimp_const.induct , simp_all, auto split: aexp.split)

(* an optimized version of plus - well , it recognises something plus zero is something*)
fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"plus (N i1 ) (N i2 ) = N (i1 + i2 )" |
"plus (N i) a = (if i = 0 then a else Plus (N i) a)" |
"plus a (N i) = (if i = 0 then a else Plus a (N i))" |
"plus a1 a2 = Plus a1 a2 "

lemma aval_plus: "aval (plus a1 a2 ) s = aval a1  s + aval a2 s"
  by( induction a1 a2 rule: plus.induct , simp_all)







(* end of Chapter3 *)
end
