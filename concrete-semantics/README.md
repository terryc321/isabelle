
# concrete semantics

create a ROOT file in concrete-semantics directory , i have one already 

```
session Sandbox = HOL +
  theories
    Exercise0304
```

using this command to check the proofs were actually accepted 

```
isabelle build -v -D .
```

we find actually , there were some bugs in our proof , namely they were not complete ! yikes !

so forget about what ide is showing , not proven until its terminal proven ??


```
 (main) ~/code/isabelle/concrete-semantics$ isabelle build -v -D .
Started at Sun Jul 5 02:00:25 GMT+1 2026 (polyml-5.9.2_x86_64_32-linux on terry-MS-7D96)
ISABELLE_TOOL_JAVA_OPTIONS="-Djava.awt.headless=true -Xms512m -Xmx4g -Xss16m"
ISABELLE_BUILD_OPTIONS=""

ML_PLATFORM="x86_64_32-linux"
ML_HOME="/opt/Isabelle2025-2/contrib/polyml-5.9.2-2/x86_64_32-linux"
ML_SYSTEM="polyml-5.9.2"
ML_OPTIONS="--minheap 500"

Session Pure/Pure
Session Misc/Tools
Session HOL/HOL (main)
Session Unsorted/Sandbox
Running Sandbox ...
Sandbox: theory Sandbox.Exercise0304
Sandbox FAILED (see also "isabelle build_log -H Error Sandbox")
...
***                      rns)
*** At command "by" (line 326 of "~/code/isabelle/concrete-semantics/Exercise0304.thy")
*** Failed to finish proof (line 260 of "~/code/isabelle/concrete-semantics/Exercise0304.thy"):
*** goal (1 subgoal):
***  1. ⟦⋀s. aval (full_asimp a1) s = aval a1 s;
***      ⋀s. aval (full_asimp a2) s = aval a2 s⟧
***     ⟹ aval
***         (let ns = flatEn a1 @ flatEn a2; vs = flatEv a1 @ flatEv a2;
***              rns = rebuild_nums ns (N 0); rvs = rebuild_vars vs (V ''x'')
***          in case ns of [] ⇒ rvs
***             | a # list ⇒ case vs of [] ⇒ rns | a # list ⇒ Plus rvs rns)
***         s =
***        aval a1 s +
***        aval a2
***         s
*** At command "by" (line 260 of "~/code/isabelle/concrete-semantics/Exercise0304.thy")
*** Failed to finish proof (line 235 of "~/code/isabelle/concrete-semantics/Exercise0304.thy"):
*** goal (1 subgoal):
***  1. x =
***     aval (simp (N x))
***      s
*** At command "by" (line 235 of "~/code/isabelle/concrete-semantics/Exercise0304.thy")
*** Failed to finish proof (line 119 of "~/code/isabelle/concrete-semantics/Exercise0304.thy"):
*** goal (1 subgoal):
***  1. ⟦hasN e1 = (case aleafs e1 of [] ⇒ False | a # list ⇒ True);
***      hasN e2 = (case aleafs e2 of [] ⇒ False | a # list ⇒ True)⟧
***     ⟹ ((case aleafs e1 of [] ⇒ False | a # list ⇒ True) ∨
***         (case aleafs e2 of [] ⇒ False | a # list ⇒ True)) =
***        (case aleafs e1 @ aleafs e2 of [] ⇒ False
***         | a # list ⇒
***             True)
*** At command "by" (line 119 of "~/code/isabelle/concrete-semantics/Exercise0304.thy")
*** Failed to finish proof (line 80 of "~/code/isabelle/concrete-semantics/Exercise0304.thy"):
*** goal (1 subgoal):
***  1. ⟦aval (asimp a1) s = aval a1 s; aval (asimp a2) s = aval a2 s⟧
***     ⟹ aval (Exercise0304.plus (asimp a1) (asimp a2)) s =
***        aval a1 s +
***        aval a2
***         s
*** At command "by" (line 80 of "~/code/isabelle/concrete-semantics/Exercise0304.thy")
Unfinished session(s): Sandbox

Finished at Sun Jul 5 02:00:29 GMT+1 2026
0:00:04 elapsed time, 0:00:04 cpu time, factor 0.93
```

## chapter 2 

to be honest chapter was a challenge . 

exercise 2.11 especially so . 

tried a few languages to write correct tree manipulation for coeffs procedure
```
polynomial.ml -- ocaml 
polynomial.lisp -- lisp 
polynomial.scm -- scheme 
```

