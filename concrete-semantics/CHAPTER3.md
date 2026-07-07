

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

This operator allows us to write down concrete states in a readable fashion.
Starting from the state that is 0 everywhere, we can update it to map certain variables to given values. For example, 

```((λx . 0) ( ''x'' := 7)) ( ''y'' := 3) ```
maps ''x'' to 7, ''y'' to 3 and all other variable names to 0. Below we employ the
following more compact notation

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

### 3.1.2.b Examples of colon equals syntax

```
value "(λ x . 0 :: int) ''z''"
value "(λ x . 0 :: int) 4"
value "((λ x . 0) (''x'' := 4 )) ''x'' :: int"
value "((λ x . 0) (''x'' := 1 , ''y'' := 2)) ''x'' :: int" (* ⟹ 1 :: int *)
value "((λ x . 0) (''x'' := 1 , ''y'' := 2)) ''y'' :: int" (* ⟹ 2 :: int *)
value "((λ x . 0) (''x'' := 1 , ''y'' := 2)) ''z'' :: int" (* ⟹ 0 :: int *)

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
to ```Plus (V ''x'') (N 4)```. Function asimp_const performs constant folding
in a bottom-up manner:

```
fun asimp_const :: "aexp ⇒ aexp" where
"asimp_const (N n) = N n" 
| "asimp_const (V x ) = V x" 
| "asimp_const (Plus a 1 a 2 ) =
(case (asimp_const a 1, asimp_const a 2 ) of
 (N n 1 , N n 2 ) ⇒ N (n 1 +n 2 ) |
 (b 1,b 2 ) ⇒ Plus b 1 b 2 )"
```

