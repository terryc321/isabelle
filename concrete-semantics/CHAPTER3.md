

# Chapter 3 Concrete Semantics 

# Case Study : IMP Expressions

The methods of the previous chapter suffice to define the arithmetic and
boolean expressions of the programming language IMP that is the subject
of this book. In this chapter we define their syntax and semantics, write
little optimizers for them and show how to compile arithmetic expressions
to a simple stack machine. Of course we also prove the correctness of the
optimizers and compiler!

## 3.1 Arithmetic Expressions

3.1.1 Syntax

Programming languages have both a concrete and an abstract syntax. Con-
crete syntax means strings. For example, "a + 5 * b" is an arithmetic ex-
pression given as a string. The concrete syntax of a language is usually defined
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

## l

```
fun asimp_const :: "aexp ⇒ aexp" where
"asimp_const (N n) = N n" 
| "asimp_const (V x ) = V x" 
| "asimp_const (Plus a 1 a 2 ) =
(case (asimp_const a 1, asimp_const a 2 ) of
 (N n 1 , N n 2 ) ⇒ N (n 1 +n 2 ) |
 (b 1,b 2 ) ⇒ Plus b 1 b 2 )"
```


