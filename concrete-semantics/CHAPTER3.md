

# Chapter 3 Concrete Semantics 

# Case Study : IMP Expressions

The methods of the previous chapter suffice to define the arithmetic and
boolean expressions of the programming language IMP that is the subject
of this book. In this chapter we define their syntax and semantics, write
little optimizers for them and show how to compile arithmetic expressions
to a simple stack machine. Of course we also prove the correctness of the
optimizers and compiler!



## 3.1 Arithmetic Expressions

### 3.1.1 Syntax

Programming languages have both a concrete and an abstract syntax. Concrete syntax means strings. For example, "a + 5 * b" is an arithmetic expression given as a string. The concrete syntax of a language is usually defined
by a context-free grammar. The expression "a + 5 * b" can also be viewed
as the following tree:

todo - insert parse tree of "a + 5 * b"

The tree immediately reveals the nested structure of the object and is the
right level for analysing and manipulating expressions. Linear strings are more
compact than two-dimensional trees, which is why they are used for reading
and writing programs. But the first thing a compiler, or rather its parser,
will do is to convert the string into a tree for further processing. Now we
are at the level of abstract syntax and these trees are abstract syntax
trees. To regain the advantages of the linear string notation we write our
abstract syntax trees as strings with parentheses to indicate the nesting (and
with identifiers instead of the symbols + and *), for example like this: Plus a
(Times 5 b). Now we have arrived at ordinary terms as we have used them
all along. More precisely, these terms are over some datatype that defines the
abstract syntax of the language. Our little language of arithmetic expressions
is defined by the datatype aexp:

```
type_synonym vname = string
datatype aexp = N int | V vname | Plus aexp aexp
```

see type_synonym [^type_synonym] note 

where *int* is the predefined type of integers and vname stands for variable
name. Isabelle strings require two single quotes on both ends, for example
``` ''abc'' ```. The intended meaning of the three constructors is as follows: N represents numbers, i.e., constants, V represents variables, and Plus represents
addition. The following examples illustrate the intended correspondence:

- [ ] todo fix me table org mode 

|Concrete | Abstract|
---------------------
| 5 | N 5|
| x | V ''x'' |
| x+ y | Plus (V ''x'') (V ''y'') |
|2 + (z + 3) | Plus (N 2) (Plus (V ''z'') (N 3)) |

It is important to understand that so far we have only defined syntax, not
semantics! Although the binary operation is called Plus, this is merely a
suggestive name and does not imply that it behaves like addition. For example,
*Plus (N 0) (N 0) \notequal N 0*, although you may think of them as semantically
equivalent — but syntactically they are not.
Datatype *aexp* is intentionally minimal to let us concentrate on the essentials. Further operators can be added as desired. However, as we shall discuss
below, not all operators are as well behaved as addition.

### 3.1.2 Semantics

The semantics, or meaning of an expression, is its value. But what is the value
of x+1? The value of an expression with variables depends on the values of its
variables. The value of all variables is recorded in the (program) state. The
state is a function from variable names to values.

```
type_synonym val = int
type_synonym state = vname ⇒ val
```

[^typesynonym]: 

In our little toy language, the only values are integers.
The value of an arithmetic expression is computed like this:

```
fun aval :: "aexp ⇒ state ⇒ val" where
"aval (N n) s = n" |
"aval (V x ) s = s x" |
"aval (Plus a 1 a 2 ) s = aval a 1 s + aval a 2 s"
```

Function aval carries around a state and is defined by recursion over the form
of the expression. Numbers evaluate to themselves, variables to their value in
the state, and addition is evaluated recursively. Here is a simple example:

```isabelle/hol
value "aval (Plus (N 3) (V 0 0x 0 0)) (λx . 0)"
```

returns 3. However, we would like to be able to write down more interesting
states than (λx . 0 ) easily. This is where function update comes in.

To update the state, that is, change the value of some variable name, the
generic function update notation f (a := b) is used: the result is the same as
f, except that it maps a to b:

```
f (a := b) = (λx . if x = a then b else f x )
```

```
value "( λ z .  (if z = ''x'' then 7 else if z = ''y'' then 3 else 0 :: int)) " 
value "( λ z .  (if z = ''x'' then 7 else if z = ''y'' then 3 else 0 :: int)) ''x'' " (* 7 *)
value "( λ z .  (if z = ''x'' then 7 else if z = ''y'' then 3 else 0 :: int)) ''y'' " (* 3 *)
value "( λ z .  (if z = ''x'' then 7 else if z = ''y'' then 3 else 0 :: int)) ''z'' " (* 0 *)
```

This operator allows us to write down concrete states in a readable fashion.
Starting from the state that is 0 everywhere, we can update it to map certain variables to given values. For example, 

```((λx . 0) ( ''x'' := 7)) ( ''y'' := 3) ```
maps ''x'' to 7, ''y'' to 3 and all other variable names to 0. Below we employ the
following more compact notation

- [ ] question - verify finite map x to 7 , y to 3 , failed to work in isabelle 2026 , 
  but easily side stepped using 

```
< ''x'' := 7 , ''y'' := 3 >
```
which works for any number of variables, even for none: <> is syntactic sugar
for (λx . 0).

- [ ] todo - replace \x with lambda 
- [ ] todo - get emacs to recognise \lambda and convert it ?

```
<> means \x . 0 
```

### 3.1.2.b Examples of finite map 

technical word finite map allows lookup variable to a value 

```
(* sometimes a type hint is needed - in this case - int - so isabelle knows what type it should 
return *)
value "(λ x . 0 :: int) ''z''"
value "(λ x . 0 :: int) 4"
value "((λ x . 0) (''x'' := 4 )) ''x'' :: int"
value "((λ x . 0) (''x'' := 1 , ''y'' := 2)) ''x'' :: int" (* ⟹ 1 :: int *)
value "((λ x . 0) (''x'' := 1 , ''y'' := 2)) ''y'' :: int" (* ⟹ 2 :: int *)
value "((λ x . 0) (''x'' := 1 , ''y'' := 2)) ''z'' :: int" (* ⟹ 0 :: int *)

(* here we can check by using the proof infrastructure *)
lemma "(((λ x . 0) (''x'' := 1 , ''y'' := 2)) ''x'') = 1" 
  by simp
lemma "(((λ x . 0) (''x'' := 1 , ''y'' := 2)) ''y'') = 2" 
  by simp
lemma "(((λ x . 0) (''x'' := 1 , ''y'' := 2)) ''z'') = 0" 
  by simp
```

It would be easy to add subtraction and multiplication to *aexp* and extend
*aval* accordingly. However, not all operators are as well behaved: division by
zero raises an exception and C’s ++ changes the state. Neither exceptions nor
side effects can be supported by an evaluation function of the simple type
aexp ⇒ state ⇒ val; the return type has to be more complicated.

### 3.1.3 Constant Folding

Program optimization is a recurring theme of this book. We start with an
extremely simple example, **constant folding**, i.e., the replacement of constant subexpressions by their value. It is performed routinely by compilers. 

For example, the expression ```Plus (V x ) (Plus (N 3) (N 1))``` is simplified
to ```Plus (V ''x'') (N 4)```. 

Function asimp_const performs constant folding in a bottom-up manner:

```
fun asimp_const :: "aexp ⇒ aexp" where
"asimp_const (N n) = N n" 
| "asimp_const (V x ) = V x" 
| "asimp_const (Plus a 1 a 2 ) =
(case (asimp_const a 1, asimp_const a 2 ) of
 (N n 1 , N n 2 ) ⇒ N (n 1 +n 2 ) |
 (b 1,b 2 ) ⇒ Plus b 1 b 2 )"
```

Neither N nor V can be simplified further. Given a Plus, first the two subexpressions are simplified. If both become numbers, they are added. In all other
cases, the results are recombined with Plus.
It is easy to show that asimp_const is correct. Correctness means that
asimp_const does not change the semantics, i.e., the value of its argument:

```
lemma "aval (asimp_const a) s = aval a s"
```

The proof is by induction on a. The two base cases N and V are trivial. In
the Plus a1 a2 case, the induction hypotheses are 
```
aval (asimp_const a1) s = aval a1 s
aval (asimp_const a2) s = aval a2 s


If asimp_const a i = N n i for i =1,2, then aval (asimp_const (Plus a 1 a 2 )) s
= aval (N (n 1 +n 2)) s = n 1+n 2
= aval (asimp_const a 1 ) s + aval (asimp_const a 2 ) s
= aval (Plus a 1 a 2 ) s.
Otherwise
aval (asimp_const (Plus a 1 a 2 )) s
= aval (Plus (asimp_const a 1 ) (asimp_const a 2 )) s
= aval (asimp_const a 1 ) s + aval (asimp_const a 2 ) s
= aval (Plus a 1 a 2 ) s.
```

This is rather a long proof for such a simple lemma, and boring to boot. In
the future we shall refrain from going through such proofs in such excessive
detail. We shall simply write “The proof is by induction on a.” We will not even
mention that there is a case distinction because that is obvious from what we
are trying to prove, which contains the corresponding case expression, in the
body of asimp_const. We can take this attitude because we merely suppress
the obvious and because Isabelle has checked these proofs for us already and
you can look at them in the files accompanying the book. The triviality of
the proof is confirmed by the size of the Isabelle text:

```
lemma "aval (asimp_const a) s = aval a s"
apply (induction a)
apply (auto split : aexp.split )
done
```

The split modifier is the hint to auto to perform a case split whenever it sees
a case expression over aexp. Thus we guide auto towards the case distinction
we made in our proof above.

Let us extend constant folding: Plus (N 0) a and Plus a (N 0) should be
replaced by a. Instead of extending asimp_const we split the optimization process into two functions: one performs the local optimizations, the other traverses the term. The optimizations can be performed for each Plus separately
and we define an optimizing version of Plus:

```
fun plus :: "aexp ⇒ aexp ⇒ aexp" where
"plus (N i 1 ) (N i 2 ) = N (i 1+i 2 )" |
"plus (N i ) a = (if i =0 then a else Plus (N i ) a)" |
"plus a (N i ) = (if i =0 then a else Plus a (N i ))" |
"plus a 1 a 2 = Plus a 1 a 2 "
```

It behaves like Plus under evaluation:

```
lemma aval_plus: "aval (plus a1 a2 ) s = aval a 1 s + aval a 2 s"
```

The proof is by induction on a1 and a2 using the computation induction rule
for plus (plus.induct ). 

Now we replace Plus by plus in a bottom-up manner
throughout an expression:

```
fun asimp :: "aexp ⇒ aexp" where
"asimp (N n) = N n" |
"asimp (V x ) = V x" |
"asimp (Plus a 1 a 2 ) = plus (asimp a 1) (asimp a 2 )"
```

Correctness is expressed exactly as for asimp_const :

```
lemma "aval (asimp a) s = aval a s"
```

The proof is by structural induction on a; the Plus case follows with the help
of Lemma aval_plus.

- [ ] todo - check proofs work so far in isabelle hol 


## Exercises

### Exercise 3.1. 

To show that asimp_const really folds all subexpressions of
the form Plus (N i ) (N j ), define a function optimal :: aexp ⇒ bool that
checks that its argument does not contain a subexpression of the form Plus
(N i ) (N j ). Then prove optimal (asimp_const a).

### Exercise 3.2. 

In this exercise we verify constant folding for aexp where we
sum up all constants, even if they are not next to each other. For example, Plus
(N 1) (Plus (V x ) (N 2)) becomes Plus (V x ) (N 3). This goes beyond asimp.
Define a function full_asimp :: aexp ⇒ aexp that sums up all constants and
prove its correctness: aval (full_asimp a) s = aval a s.

### Exercise 3.3. 

Substitution is the process of replacing a variable by an ex-
pression in an expression. Define a substitution function subst :: vname ⇒
aexp ⇒ aexp ⇒ aexp such that subst x a e is the result of replacing every
occurrence of variable x by a in e. For example:

subst 0 0 x 0 0 (N 3) (Plus (V 0 0x 0 0) (V 0 0 y 0 0 )) = Plus (N 3) (V 0 0 y 0 0 )
Prove the so-called substitution lemma that says that we can either
substitute first and evaluate afterwards or evaluate with an updated state:
aval (subst x a e) s = aval e (s(x := aval a s)). As a consequence prove
aval a 1 s = aval a 2 s =⇒ aval (subst x a 1 e) s = aval (subst x a 2 e) s.

### Exercise 3.4. 

Take a copy of theory AExp and modify it as follows. Extend
type aexp with a binary constructor Times that represents multiplication.
Modify the definition of the functions aval and asimp accordingly. You can
remove asimp_const. Function asimp should eliminate 0 and 1 from multi-
plications as well as evaluate constant subterms. Update all proofs concerned.

### Exercise 3.5. 

Define a datatype aexp2 of extended arithmetic expressions
that has, in addition to the constructors of aexp, a constructor for modelling
a C-like post-increment operation x++, where x must be a variable. Define an
evaluation function aval2 :: aexp2 ⇒ state ⇒ val × state that returns both
the value of the expression and the new state. The latter is required because
post-increment changes the state.
Extend aexp2 and aval2 with a division operation. Model partiality of
division by changing the return type of aval2 to (val × state) option. In
case of division by 0 let aval2 return None. Division on int is the infix div.

### Exercise 3.6. 

The following type adds a LET construct to arithmetic ex-
pressions:
datatype lexp = Nl int | Vl vname | Plusl lexp lexp | LET vname lexp lexp
The LET constructor introduces a local variable: the value of LET x e 1 e 2
is the value of e 2 in the state where x is bound to the value of e 1 in the
original state. Define a function lval :: lexp ⇒ state ⇒ int that evaluates
lexp expressions. Remember s(x := i ).
Define a conversion inline :: lexp ⇒ aexp. The expression LET x e 1 e 2
is inlined by substituting the converted form of e 1 for x in the converted form
of e 2 . See Exercise 3.3 for more on substitution. Prove that inline is correct
w.r.t. evaluation.


## 3.2 Boolean Expressions





# Footnotes

- [ ] todo find video link 

[^type_synonym]: type synonym is to make datatype appear identical but at some time later the user can change alter it which may cause the system confusion 
see laurence paulson youtube video 

- [ ] video course youtube "Interactive Formal Verification"

course material online at [ ](https://www.cl.cam.ac.uk/2122/L21/)

youtube video series online [Interactive Formal Verification](https://youtu.be/5I5XuBzpmwQ?si=CkIe034cWmpgKUXB)




