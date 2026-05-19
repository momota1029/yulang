# **A Correspondence between Continuation Passing Style and Static Single Assignment Form**

Richard A. Kelsey NEC Research Institute kelseyQresearch.nj.nec.eom

#### **Abstract**

We define syntactic transformations that convert continuation passing style (CPS) programs into static single assignment form (SSA) and vice versa. Some CPS programs cannot be converted to SSA, but these are not produced by the usual CPS transformation. The CPS-+SSA transformation is especially helpful for compiling functional programs. Many optimizations that normally require flow analysis can be performed directly on functional CPS programs by viewing them as SSA programs. We also present a simple program transformation that merges CPS procedures together and by doing so greatly increases the scope of the SSA flow information. This transformation is useful for analyzing loops expressed as recursive procedures.

Permission to copy without fee all or part of this material is granted provided that the copies are not made or distributed for direct commercial advantage, the ACM copyright notice and the title of the publication and its date appear, and notice is given that copying is by permission of the Association for Computing Machinery. To copy otherwise, or to republish, requires a fee and/or specific permission.

IR'95-1/95 San Francisco, California USA @1995 ACM 0-89791-754-5/95/0001 ...\$3.50

### **1 Introduction**

Continuation-passing style has been used as an intermediate language in a number of compilers for functional languages [1, 8, 12]. Static single assignment form has been used in optimizations targeted towards imperative languages, for example eliminating induction variables [13] and partim redundancies [2]. In this paper we define syntactic transformations for converting continuation passing style (CPS) programs into static single assignment form (SSA) and vice versa.

The similarities between CPS and SSA have been noted by others [1, 9]. In CPS there is exactly one binding form for every variable and variable uses are lexically scoped. In SSA there is exactly one assignment statement for every variable, and that statement dominates all uses of the variable. This is also the main difference between the two: the restriction on variable references in CPS is lexical, while in SSA it is dynamic.

The two forms have generally been used in very different contexts. CPS has been used in compilers for functional languages, and SSA for iraperative ones. As a result, the problem of flow analysis has come to be viewed as more difficult in CPS. This is really an artifact of the programs being compiled and not a problem with the CPS intermediate language. Functional programs express control flow through the use of procedures, resulting in large collections of small procedures, as opposed to small collections of large procedures in imperative languages (by 'large' procedure we mean one large enough to contain a loop). The writers of compilers for imperative languages have been quite successful with using SSA to express the results of intraprocedural flow-analysis and then analyzing the SSA program. CPS uses procedures to express practically everything, so anything but the most local optimization appears to require interprocedural analysis, which is hard in any language.

In this paper we are not going to concern ourselves with interprocedural flow analysis. What we will do is restrict our notion of what constitutes a procedure in CPS. The A forms in CPS programs will be annotated to indicate which represent full procedures and which are continuations. This reduces the number of full procedures and greatly simplifies analyzing the program.

Throughout the paper we will assume that any use of lexical scoping in the source program has been implemented by the introducing explicit environments, as described in [1, 7]. We further assume that in the CPS programs continuations are created and used in a last-in/first-out manner (see section 6 for a discussion). The latter restriction only affects the way in which nonlocal returns, such as longjumps in C or call-withcurrent-continuation in Scheme, are expressed in CPS.

The paper proceeds as follows. Section 2 contains the definition of an SSA language. Section 3 defines a source language, an annotated CPS language, and an algorithm for converting source programs into CPS programs. The following two sections define functions that convert CPS procedures into SSA procedures and vice versa. The remainder of the paper is a discussion of practical differences between SSA and CPS, followed by a comparison to previous work.

### **2 Static Single Assignment**

SSA is an imperative form in which there is exactly one assignment for every variable and that assignment dominates all uses of the variable (see [4] for a good overview of SSA).

To make the control-flow graph explicit, control flow is expressed entirely in terms of if and goto. We allow expressions in some nonstandard places, for example as the arguments to the C-functions; removing these only requires introducing a few additional assignment statements. The syntax of expressions does not matter and is left unspecified, with the restriction that they may not contain procedure calls (and they typically don't in SSA languages).

The grammar for a procedure in our SSA language is:

```
P ::= proc(x*) { B L* } 
L ::= I:I*B 
I ::= x ~- ¢(E*); 
B ::= x~-E; B ] z~-E(E*); B] 
      goto l~; I 
      return E; I return E(E*) ; I 
       if E then B else B 
E ::= xlE+E[... 
where x E variables 
       l E labels
```

The semantics is the 'obvious' one. ~-~ is assignment, E(E, ...) is a procedure call, and return returns from the current procedure. The C-functions at the beginning of a block each take one argument for each of the goto's that jump to that block. The i'th argument is returned when control reaches the block from goto l~.

Cytron et al. [4] describe a translation algorithm that efficiently converts programs into SSA while introducing the minimum number of C-functions.

Because every variable has a unique assignment, definition~use chains are trivial to compute. Many analyses and optimizations are simpler when applied to a program in SSA form than to the original source program.

Below is an example SSA procedure that counts the number of times zero appears in the sequence f(0) ... f(limit-i) for some function f and integer limit. Note that some of the computation occurs in the C-functions. In particular the second if makes sense only in the context of the C-function for c' at label j. We will be using this example throughout the paper.

```
proc (f limit) { 
     goto I0 ; 
   l:i *-¢(0, i+1); 
      c ~-¢(0, c'); 
      if i = limit then 
         return c ; 
      else 
         x ~-f (i) ; 
         if x = 0 then 
             goto j0 ; 
         else 
             goto jl; } 
   j:c' ~--¢(c+1, c); 
      goto 11 ; }
```

#### **3 Annotated CPS**

In continuation passing style procedures do not return. Instead they are passed an additional argument, a continuation, which is applied to the procedure's return value (see chapter 8 of [5] for a full discussion).

The correspondence between CPS and SSA requires a slightly modified algorithm for converting programs into CPS. The modified algorithm annotates the A forms in the CPS code to show how they are used. The annotations have no semantic content and, if not introduced by the CPS algorithm, could be added to the program via some suitable analysis (assuming the CPS program is in a suitable form; see section 6 below).

Our source language is a subset of Scheme [3], with the subset chosen as a compromise between simplicity and realism. For simplicity we will assume that the source and CPS languages use the same expressions as in the SSA language of the previous section. In the context of Scheme programs we will refer to the equivalents of the SSA expressions as trivial expressions, to keep from confusing them with other Scheme expressions. As described above, the main restriction on (trivial) expressions is that they cannot contain procedure calls.

To simplify the CPS algorithm the source language is restricted to allow non-trivial expressions only in tail position or as the bound value in a let. In an actual compiler the source program could be put in this form either by a pre-pass or as part of a more complex CPS algorithm. We also assume that every identifier is unique.

A loop expression is a version of Scheme's named-let with the restriction that calls to the label may only occur in tail position. It is included to show how iterative constructs, such as for and while loops, may be converted into CPS.

The grammar for this Scheme subset is:

```
M ::= E I (E E*) I (if E M M) I 
       (let ((xM)) M) [ 
       (loop l ((x E)*) M) I 
       (IE*) 
E ::= zI(+EE) I... 
P ::= (A (x*) M) 
where x C variables 
       l E labels
```

The semantics of the source language is that of Scheme. This subset is sufficient to implement most of Scheme, with explicit cells added for any variables that are the targets of set ! expressions in the source program.

As was done in the Rabbit compiler [12] our

```
,7": M x C~M' 
m([E, kl) = (k E) 
3F([E, (.~cont(X) M')])= (let ((xZ)) M') 
F(I(E...), C]) = (let ((v (E...))) (jr)) if C = x and x is bound by letrec 
               = (E... C) otherwise 
3K'([(let ((X M1)) M2) , el)= .7([M1, (~(X) ~([M2, C~))~) 
~7([(ie E ~/[1 M2), ~1) -~ (if E ~7([M1, ~1) ~7([M2, ~)) 
F([(±f E M1 M2), (~cont(Z) M')]) = 
    (letrec ((x (Ajump (X) M'))) (if E S([M1, z]) Y([M2, z~))) 
Jr([(loop l ( (x ginitial) ... )M), CI) = 
    (letrec ((I (Ajump (x ... ) 5r([M, C~)))) (l Einitial ... )) 
             CD = 
F: P~P' 
v([(A(,...) M)])= 7(Iv, k]))
```

Figure 1: Conversion to CPS

conversion to CPS will treat trivial expressions as values and not introduce continuations for them.

In the CPS grammar all A's are annotated as being either *proc, cont,* or *jump.* The annotations indicate how the A's are used, and, equivalently, how they can be compiled.

*Proc* is used as the translation of the A forms in the source program. These are full procedures that eventually return a value and for this reason take a continuation as an argument. The *cont*  and *jump* forms are continuations that are used in slightly different ways. The *cont* continuations are return points for calls to *proc's. Jump* indicates that the continuation is called within the current procedure instead of being passed to another one. The CPS algorithm introduces *,Xjump*  continuations when the two arms of a conditional have to rejoin at a common point and for the bodies of loop's.

In terms of compilation strategy, *cont* A's are return points, *jump's* can be compiled as gotos, and *prods* require a complete procedure-call mechanism.

The grammar for the CPS language is as follows:

```
M' ::= (E E* C) I 
       (k E) I 
       (if EM'M') ] 
       (let ((x E)) M') I 
       (letrec ((x P')) g') 
 C ::= k I (Aco~t (z) M') 
p/ ::= (Ap~oc (z* k) M/)[ 
       (Aj~p (x*) M') 
where x,k E variables
```

The semantics is the obvious call-by-value semantics. The annotated A's are all just A, let is syntactic sugar for A, and so on.

The identifiers x and k used in the grammar are members of the same syntactic class. Making them syntactically distinct, as is sometimes done [8], restricts how continuations are used and makes CPS and SSA entirely equivalent (see Section 6).

The function ~ defined in Figure 1 translates source expressions M to CPS expressions M'. It

```
(Aproc (f limit k) 
  (letrec ((i (Ajump 
                   (if 
     (i o o))) 
                         (i c) 
                        (= i limit) 
                        (k c) 
                        (f i (A~ont (x) 
                                 (letrec 
                                   (if 
                                           ((j (Aj~mp (c') 
                                                  (1 (+ i 1) c')))) 
                                        (=x0) 
                                        (j (+ c 1)) 
                                        (j c)))))))))
```

Figure 2: Example program in CPS

takes a continuation C, which is either an identifier or a *A~ont,* as its second argument.

F has two rules for applications. The first rule is used when the continuation argument is an identifier bound by a letrec in the rule for if and ensures that all uses of such identifiers are called directly. The second is used in all other cases. For let a new continuation is created for the value. Identifier continuations are propagated through if's; to avoid code expansion A continuations (as opposed to continuations that are just an identifier) are marked as *jump* and bound to an identifier. Loop is translated into a recursive continuation. The loop begins by calling the continuation on the initial values of the iterative variables. Calls to the loop's label become calls to the recursive continuation, ignoring the current continuation.

As we are not interested in interprocedural analysis we will treat each Apro~ as a separate program (here we depend on the assumption that explicit environments have been introduced to take care of lexical scoping for any nested *Aproc'S).* Because they are called at the point they are created, *A~o~t's* can be considered as inlined procedures. The call sites of *Ajump's* are easily found: the */~jurnp'S* only occur as the bound value in letrec's. Furthermore, all references to the variables to

which the Aj~mp's are bound are calls to those variables.

The following is the sample SSA procedure from above written in the source language for the CPS transformation:

```
(l (f limit) 
  (loop 1 ((i O) (c 0)) 
    (if (= i limit) 
         c 
         (let ((x (f i))) 
           (let ((c I (if (= x O) 
                           (+ c I) 
                          c))) 
             (1 (+ i i) c'))))))
```

Figure 2 presents the CPS version of the same procedure. A *Acont* is introduced as the continuation for the call to f and Aj~r~p'S are used as the join point for the if and for the loop.

### **4 Converting CPS to SSA**

In this section we define a syntactic translation that converts CPS procedures into SSA procedures.

The function G in Figure 3 translates nontrivial CPS expressions to SSA statements. The

```
g: M/-+B 
 (I(let M')]) = • E; 
g([(S ... (Aco (x) M'))]) = x E( ... ); 
O([(E ...It)I) ---- returnE(...); 
~([(k E)]) = return E; 
O([(j Eo,i El,i ... )]) = goto ji; 
g([(if E M i MS)I) = if E then g([Mi] ) else G([M%_I )
O([(letrec (...) M')]) = O([M']) 
Opro~ : P' ~P 
gproc([(Aproc (x ... ) M')]) = proc(x.., k){ Q([M']) Ojump([(Ajump ... )]) ...} 
gjump : J x (ljump (x...) M') --~ L 
Gjump([j, (Ajurnp (x...) M')]) =j: x+--¢(E0,0, E0,1,...); ... Q([M']))
```

Figure 3: Translation of CPS to SSA. The *Ei,j* on the right-hand side of the definition of *gjump* are those from the left-hand side of the definition of g([(j ... )]).

simple binding forms, let and */~cont,* become assignments. If is essentially the same in both syntaxes. Uses of a Apron'S continuation variable become return's while calls to letrec-bound continuation variables are translated as gotos.

The *,~jump'S* in the program are ignored when found by g. Each */~jump* is instead lifted up to become a labeled block in the SSA procedure. The arguments to the *,~jump'S,* which are also ignored by ~, become the arguments to the C-function that defines the value of the corresponding variable in the SSA program. In the definition of 6j~p, E0,1 is the first argument to the second call (in some arbitrary ordering) to j, the variable bound to (Aj~mp (X...) M'). That call is translated as goto Jl.

The translated program is syntactically correct, and it obeys the SSA restriction that there is exactly one assignment per variable (since each variable is bound exactly once in the CPS program). Variables in the translated program are assigned the values of the same expressions they were bound to in the CPS program, and evaluation order is preserved, so the two programs produce identical results.

Applying *Opro~* to the CPS example produces

the original SSA example from above.

#### **5 Converting SSA to CPS**

We would like to produce an inverse of g to convert SSA programs to CPS. The function 'H in Figure 4, produced by a simple editing of the definition of g, is almost an inverse of 0. The difficulty is the rule for the letrec's that bind Aj~mp's. In translating */~jurnp'S to* labeled blocks g ignores their position in the CPS program. Translating a labeled block back into a *,~jump* is straightforward, but we need to bind the Ajump with a letrec somewhere in the newly created CPS program. The *,~jump'S* need to be placed such that no variable is referred to outside the form that binds it.

Our placement algorithm uses the dominator tree of the SSA program. Statement M0 is said to dominate M1 if M0 appears in every execution path between the start of the program and M1. If M2 also dominates M1 then either M2 dominates M0 or vice versa. The dominator relation thus organizes a program's statements into a tree. The immediate dominator of M is M's parent in tile dominator tree.

Given a labeled block, d : I\* B, in the SSA

```
7-f : B--~ M' 
~([z ~ E; M])= (let ((z E)) ~([M])) 
           E(... );D = (E... k) 
                 = (k E) 
71([goto ,Ii;l) = (j E0,i ELi ...) 
"Hp~o~ : P -~ P' 
7l~proc([proc(x ... k){B L*}~)= (Ap~oc (x ... ) g(lBl)) 
"]-~jltmp : L ~ (Aju,7.p (Z...) M') 
~jump([j: x~¢(E0,0, Eo,1,...); ... B]) = (Aj~mp (z..) H([B]))
```

Figure 4: Translation of SSA to CPS. The E~,j on the right-hand side of the definition of "H([goto g~ ;]) are those from the left-hand side of the definition of 7-fjump.

program, with M the immediate dominator of I\* B, we will replace "H(IM~) with

in the CPS procedure. If two or more labels have the same immediate dominator their Aj~p's are placed in a single letrec.

Theorem: all uses of variables in the CPS program produced by 'H are properly in scope.

Proofi We know that every use of a variable in the SSA program is dominated by the variable's assignment statement. Assignment statements in the SSA program correspond to binding forms in the CPS program. By inspection H preserves the dominator tree, so it is sufficient to show that every statement in the CPS program is lexically inferior to its immediate dominator, and thus to all its dominators, including the binding forms for any referenced variables.

Again inspecting the definition of "H, we can see that when the M' produced by "]f is the body of either a LET, a *Aproc,* or a *Acont,* or if it is either arm of an if, then it is lexically inferior to its immediate dominator. The remaining possible location for an M' is as the body of a Ajump, and each *Aj,mp* is by construction lexically inferior to the dominators of its immediate dominator. This would lead to a problem if the immediate dominatot were a binding form, but this cannot happen. If (let ((z E)) M') or (E ... *(Aco~t (x)* M')) dominates a *~jump,* then M / does as well.

The arguments to tile C-functions are also placed so as to be lexically inferior to their dominators. QED.

Using 7-/ to convert the original SSA example to CPS produces a program identical to the CPS program shown in Figure 2.

# **6 Why CPS and SSA Are Not Identical**

The function g cannot be applied to all CPS programs. It depends on the A's being correctly annotated, which in turn depends on continuations being used in a somewhat restricted fashion. If non-local returns, such as longjumps in C or callwith-current-continuation in Scheme, are translated into uses of continuations in the CPS program there is no way to label the continuations so used. They are neither simply passed as a procedure's continuation, nor are all of their calls tailrecursive calls within the procedure in which they were created, so neither *A~.o~t* or Aj~mp is appropriate. A fourth annotation could be introduced

```
(Aproc (f limit k) 
  (letrec ((i (Aproc (i c k') 
                  (if (= i limit) 
                       (k' c) 
                       (f i (~cont (X) 
                               (letrec ((j 
    (i 0 0 k))) 
                                             (A/~p (c') 
                                               (i (+ i i) c' k')))) 
                                 (if (= x O) 
                                      (j (+ c i)) 
                                      (j c)))))))))
```

Figure 5: Example program using Scheme's named-let translated into CPS.

for continuations that are created in one procedure and called in another. There would still be no direct way to represent the program in SSA.

# **7 Compiling Imperative Programs**

We have shown that programs can be translated into CPS and from there to SSA programs by a series of syntactic transformations. Producing an SSA program normally requires flow-analysis, as the program directly expresses use~definition chaining. Where is the flow information in the CPS program coming from?

The source program for the CPS transformation is a functional program, and as such contained the required flow information. If we had started with an imperative program, meaning one using set! to modify the values of variables, translation into our CPS source language would have required adding explicit cells to hold the values of all variables that were the targets of set! expressions. The *Aj~mp'S* in the resulting CPS program would take no arguments and there would be no C-functions in the corresponding SSA program, only a lot of stores and fetches. Transforming such a program into a more useful form would require doing some flow-analysis, similar to that done in translating imperative programs to SSA.

# **8 Compiling (Mostly) Functional Programs**

For programs that do not side-affect the values of variables, viewing CPS procedures as SSA procedures shows that CPS nicely reflects intraprocedural definition~-~use associations without any need for flow analysis. There is still a problem. Programs written in languages such as ML and Scheme tend to have few side-affected variables, making dataflow visible as discussed above. The difficulty is that these same languages use recursion to express iteration. They do not use iterative constructs like loop in the CPS source language used above. So while we get intraprocedural flow information more or less for free, what we really want is interprocedural information.

Interprocedural analysis is difficult, but we can instead take the approach of increasing the size of the procedures. The idea is to find a set of procedures all of which are always called with the same continuation, and then to substitute that continuation for the procedures' continuation variables. The procedures are then themselves continuations nested within a single large procedure, removing any need for interprocedural information.

More precisely, given a set procedures P0 ... Pn bound by one or more letrec forms to identifiers *fo ... fn* and a continuation C such that every use *offi* is either a tail-recursive call from within Pj **or** 

a non-tail-recursive call being passed continuation C, we can perform the following transformation.

Let Pi = *(Aproc (... ki)* Mi). IfC is *(Acont ... ),*  let j be a new identifier; if C is an identifier, let j be that identifier.

- 1. Replace all references to the ki with j and remove them from the variable lists of the Pi, changing the Pi t¥om *Aproc'S* to */~jump'S.*
- 2. Remove the continuation from all calls to the
- 3. Let M be the smallest form containing every non-tail-recursive call to the fi. Replace M with (letrec (...) M) where (...) binds j to C if C = *(A~o~t ... )* and also binds *fi* to Pi for every fi whose original binding form is lexically apparent at M.

Because we restricted ourselves to having the *fi*  be bound by letrec and being called directly (as opposed to being passed to another procedure and then being called, for example), this is a purely syntactic transformation. More sophisticated versions are clearly possible. The simple syntactic version presented here applies to many common uses of recursive procedures.

If our CPS source program used Scheme's named-let syntax instead of the restricted loop version used above, applying ~ to it would produce the program shown in Figure 5. The recursive procedure is now a full procedure. Applying the above transformation to this program, with P0 = *(Aproc* (i c k/) ...) and C =j= 1, produces the procedure shown in Figure 2.

We need to show that the transformation is correct and preserves the map to SSA. Substituting the value C (or an identifier bound to C) for the variables *ki* is safe, because the ki are always bound to that value. Scoping is preserved, because any free identifiers in C are in scope at M, otherwise they would be out of scope at some occurrence of C in the original program. Moving the Pi to a lexically inferior form also preserves

scoping, and all uses of the *fi* are at or below the inserted letrec that now binds them.

The function G can be applied to the transformed program to produce an equivalent SSA version. We have created more Aj~mp's, but they obey the same restrictions as the ones created by the CPS algorithm: the .Xj.,mp's are bound by letrec, all uses of the variables to which they are bound are tail calls, and the bindings and uses all lie within a single Ap~oc (because any outlying Pi were moved in step 3 of the transformation).

# **9 Related Work and Conclusion**

The similarity between CPS and SSA has been noted by others. Appel [1] and O'Donnell [9] both briefly describe the relationship between Cfunctions and parameters to procedures whose call sites are known. Here we have shown that the correspondence is exact, and, more importantly, goes both ways. The main difference between a CPS procedure and an SSA procedure is the syntax. Compiler writers can use a single representation and take advantage of both the work on intraprocedural optimizations that has been done using SSA and the work on interprocedural optimizations done using CPS.

The other contribution of this paper is that the correspondence can be made to be useful. As long as procedures are too small to contain loops, considering them as SSA procedures does not help much. We have shown how to merge looping procedures together such that the result can treated as a single procedure (a restricted and somewhat more complex version of this transformation is mentioned in two of our earlier papers, [6, 7], but without any discussion of the implications for program analysis). Without this transformation analyzing loops that are expressed as recursive procedures requires interprocedural analysis, as in [11], and in this case using CPS may be more difficult than necessary [10].

### **References**

- [1] Andrew W. Appel. *Compiling with Continuations.* Cambridge University Press, Cambridge, 1992.
- **[2]**  Preston Briggs and Keith D. Cooper. Effective partial redundancy elimination. In *Proceedings A CM SIGPLAN '9~ Conference on Programming Language Design and Implementation,* pages 159-170, 1994.
- **[3]**  William Clinger and Jonathan Rees. Revised 4 report on the algorithmic language Scheme. *ACM Lisp Pointers,* 4(3):1-55, 1991.
- [4] Ron Cytron, Jeanne Ferrante, Barry K. Rosen, Mark N. Wegman, and F. Kenneth Zadeck. Efficiently computing static single assignment form and the control dependence graph. *A CM Transactions on Programming Languages and Systems,*  13(4):451-490, 1991.
- [5] Daniel P. Friedman, Mitchell Wand, and Christopher T. Haynes. *Essentials of Programming Languages.* MIT Press, Cambridge, MA, 1992. Also McGraw-Hill, Chicago, 1992.
- **[6]**  Richard Kelsey. Compilation by program transformation. Technical Report YALEU/DCS/TR-702, Department of Computer Science, Yale University, New Haven, CT, 1989.
- [7] Richard Kelsey and Paul Hudak. Realistic compilation by program transformation. In *Co@ Rec. 16 A CM Symposium on Principles of Programming Languages,*  pages 281-292, 1989.
- **[8]**  David A. Kranz, Richard Kelsey, Jonathan A. Rees, Paul Hudak, James Philbin, and Norman I. Adams. Orbit: An

- optimizing compiler for scheme. In *Proceedings SIGPLAN '86 Symposium on Compiler Construction,* 1986. *S[CPLAN Notices* 2i(7), July, 1986, 219-223.
- **[9]**  Ciaran O'Donnell. *High level compiling for low level machines.* PhD thesis, Ecole Nationale Supfirieure des Tfil~communications, 1994.
- [10] Amr Sabry and Matthias Felleisen. Is continutation-passing useful for data flow analysis? In *Proceedings of the A CM SIGPLAN '94 Conference on Programming Language Design and Implementation,*  pages 1-12, 1994.
- [11] Olin Shivers. *Control-Flow Analysis of Higher-Order Languages or Taming Lambda.* PhD thesis, School of Computer Science, Carnegie-Mellon University, 1991.
- **[12]**  Guy L. Steele. Rabbit: A compiler for Scheme. Technical Report 474, Massachusetts Institute of Technology, Cambridge, MA, May 1978.
- **[13]**  Michael Wolfe. Beyond induction variables. In *Proceedings of the A CM SIGPLAN '92 Conference on Programming Language Design and Implementation,* pages 162-174, 1992.