# **Koka: Programming with Row-polymorphic Effect Types**

Daan Leijen Microsoft Research daan@microsoft.com

We propose a programming model where effects are treated in a disciplined way, and where the potential side-effects of a function are apparent in its type signature. The type and effect of expressions can also be inferred automatically, and we describe a polymorphic type inference system based on Hindley-Milner style inference. A novel feature is that we support polymorphic effects through row-polymorphism using duplicate labels. Moreover, we show that our effects are not just syntactic labels but have a deep semantic connection to the program. For example, if an expression can be typed without an *exn* effect, then it will never throw an unhandled exception. Similar to Haskell's *runST* we show how we can safely encapsulate stateful operations. Through the state effect, we can also safely combine state with let-polymorphism without needing either imperative type variables or a syntactic value restriction. Finally, our system is implemented fully in a new language called Koka[1](#page-0-0) and has been used successfully on various small to medium-sized sample programs ranging from a Markdown processor to a tier-splitted chat application. You can try out Koka live at [www.rise4fun.com/koka/tutorial.](http://www.rise4fun.com/koka/tutorial)

## **1. Introduction**

We propose a programming model where effects are a part of the type signature of a function. Currently, types only tell us something about the input and output value of a function but say nothing about all *other* behaviors; for example, if the function writes to the console or can throw an exception. In our system, the squaring function:

```
function sqr(x : int) { x ∗ x }
will get the type:
sqr : int → total int
```

signifying that *sqr* has no side effect at all and behaves as a total function from integers to integers. If we add a *print* statement though:

```
function sqr(x : int) { print(x); x ∗ x }
```

the (inferred) type indicates that *sqr* has an input-output (*io*) effect:

```
sqr : int → io int
```

Note that there was no need to change the original function nor to promote the expression *x*∗*x* into the *io* effect. One of our goals is to make effects convenient for the programmer, so we automatically combine

<span id="page-0-0"></span><sup>1</sup>Koka means 'effect' or 'effective' in Japanese.

effects. In particular, this makes it convenient for the programmer to use precise effects without having to insert coercions.

There have been many proposals for effects systems in the past [\[2,](#page-21-0) [8,](#page-21-1) [24,](#page-22-0) [25,](#page-22-1) [28,](#page-22-2) [33,](#page-22-3) [36,](#page-22-4) [38,](#page-22-5) [42\]](#page-23-0). However, many such systems suffer from being syntactical in nature (i.e. effects are just labels), or by being quite restricted, for example being monomorphic or applied to a very specific set of effects. Some of the more general systems suffer from having complicated effect types, especially in a polymorphic setting that generally requires sub-effect constraints.

Our main contribution in this paper is the novel combination of existing techniques into the design of a practical ML-like language with strong effect typing. In addition, many known techniques are applied in a novel way: ranging from effect types as rows with duplicate labels to the safety of *runST* in a strict setting. In particular:

- We describe a novel effect system based on row polymorphism which allows *duplicated* effects. This simplifies the effect types and provides natural types to effect elimination forms, like catching exceptions.
- The effect types are not just syntactic labels but they have a deep semantic connection to the program (Section [6\)](#page-18-0). For example, we can prove that if an expression that can be typed without an *exn* effect, then it will never throw an unhandled exception; or if an expression can be typed without a *div* effect, then it always terminates.
- The interaction between polymorphism and mutable state is fraught with danger. We show that by modeling state as an effect we can safely combine mutability with let-polymorphism without needing either imperative type variables, nor a syntactic value restriction. Moreover, we can safely encapsulate local state operations and we prove that such encapsulation is sound where no references or stateful behavior can escape the encapsulation scope.
  - The interaction between divergence and higher-order mutable state is also tricky. Again, we show how explicit heap effects allow us to safely infer whether stateful operations may diverge.
- We have an extensive experience with the type system within the Koka language. The Koka language fully implements the effect types as described in this paper and we have used it successfully in various small to medium sized code examples ranging from a fully compliant Markdown text processor to a tier-splitted chat application (Section [2.8\)](#page-7-0).

## **2. Overview**

Types tell us about the behavior of functions. For example, if suppose we have the type of a function *foo* in ML with type *int* → *int*. We know that *foo* is well defined on inputs of type *int* and returns values of type *int*. But that is only part of the story, the type tells us nothing about all *other* behaviors: i.e. if it accesses the file system perhaps, or throws exceptions, or never returns a result at all.

Even 'pure' functional languages like Haskell do not fare much better at this. Suppose our function has the Haskell type *Int* → *Int*. Even though we know now there is no arbitrary side-effect, we still do not know whether this function terminates or can throw exceptions. Due to laziness, we do not even know if the result itself, when demanded, will raise an exception or diverge; i.e. even a simple transformation like *x* ∗ 0 to 0 is not possible under Haskell's notion of purity.

In essence, in both ML and Haskell the types are not precise enough to describe many aspects of the static behavior of a program. In the Haskell case, the real type is more like (*Int*⊥→ *Int*⊥)<sup>⊥</sup> while the type signature of the ML program should really include that any kind of side-effect might happen.

Functional programming has been done wrong! We believe it is essential for types to include potential behaviors like divergence, exceptions, or statefulness. Being able to reason about these aspects is crucial in many domains, including safe parallel execution, optimization, query embedding, tiersplitting, etc.

### **2.1. Effect types**

To address the previous problems, we take a fresh look at programming with side-effects in the context of a new language called Koka [\[18,](#page-21-2) [19\]](#page-21-3).

Like ML, Koka has strict semantics where arguments are evaluated before calling a function. This implies that an expression with type *int* can really be modeled semantically as an integer (and not as a delayed computation that can potentially diverge or raise an exception).

As a consequence, the *only point where side effects can occur is during function application*. We write function types as (<sup>τ</sup>1,...,<sup>τ</sup>*n*) <sup>→</sup> <sup>ε</sup> <sup>τ</sup> to denote that a function takes arguments of type <sup>τ</sup><sup>1</sup> to <sup>τ</sup>*n*, and returns a value of type <sup>τ</sup> with a potential side effect <sup>ε</sup>. As apparent from the type, functions need to be fully applied and are not curried. This is to make it immediately apparent where side effects can occur. For example, in ML, an expression like *f x y* can have side effects at different points depending on the arity of the function *f* . In our system this is immediately apparent, as one writes either *f*(*x*,*y*) or (*f*(*x*))(*y*).

### **2.2. Basic effects**

The effects in our system are extensible, but the basic effects defined in Koka are *total*, *exn*, *div*, *ndet*, *alloc*h*h*i, *read*h*h*i, *write*h*h*i, and *io*. Of course *total* is not really an effect but signifies the absence of any effect and is assigned to pure mathematical functions. When a function can throw an exception, it gets the *exn* effect. Potential divergence or non-termination is signified by the *div* effect. Currently, Koka uses a simple termination analysis based on inductive data types to assign this effect to recursive functions. Non-deterministic functions get the *ndet* effect. The effects *alloc*h*h*i, *read*h*h*i and *write*h*h*i are used for stateful functions over a heap *h*. Finally *io* is used for functions that do any input/output operations. Here are some type signatures of common functions in Koka:

```
random : () → ndet double
print : string → io ()
error : ∀α. string → exn a
(:=) : ∀α. (refhh,ai, a) → writehhi ()
```

Note that we use angled brackets to denote type application as usual in languages like C# or Scala. We also use angled brackets to denote a *row* of effects. For example, the program:

```
function sqr( x : int ) { error("hi"); sqr(x); x ∗ x }
will get the type
sqr : int → hexn,divi int
```

where we combined the two basic effects *exn* and *div* into a row of effects h*exn*, *div*i. The combination of the exception and divergence effect corresponds exactly to Haskell's notion of purity, and we call this

effect pure. Common type aliases are:

```
alias total = \langle \rangle
alias pure = \langle exn, div \rangle
alias st\langle h \rangle = \langle alloc\langle h \rangle, read\langle h \rangle, write\langle h \rangle \rangle
alias io = \langle st\langle ioheap \rangle, pure, ndet \rangle
```

This hierarchy is clearly inspired by Haskell's standard monads and we use this as a starting point for more refined effects which we hope to explore in Koka. For example, blocking, client/server side effects, reversable operations, etc.

#### 2.3. Polymorphic effects

Often, the effect of a function is determined by the effects of functions passed to it. For example, the *map* function which maps a function over all elements of a list will have the type:

```
map : \forall \alpha \beta \mu. (list \langle \alpha \rangle, \alpha \rightarrow \mu \beta) \rightarrow \mu list \langle \beta \rangle
```

where the effect of the *map* function itself is completely determined by the effect of its argument. In this case, a simple and obvious type is assigned to *map*, but one can quickly create more complex examples where the type may not be obvious at first. Consider the following program:

```
function foo(f,g) { f(); g(); error("hi") }
```

Clearly, the effect of foo is a combination of the effects of f and g, and the exn effect. One possible design choice is to have a  $\cup$  operation on effect types, and write the type of foo as:

$$\forall \mu_1 \mu_2. (() \rightarrow \mu_1 (), () \rightarrow \mu_2 ()) \rightarrow (\mu_1 \cup \mu_2 \cup exn) ()$$

Unfortunately, this quickly gets us in trouble during type inference: unification can lead to constraints of the form  $\mu_1 \cup \mu_2 \sim \mu_3 \cup \mu_4$  which cannot be solved uniquely and must become part of the type language. Another design choice is to introduce subtyping over effects and write the type of *foo* as:

$$\forall \mu_1 \mu_2 \mu_3. \ (\mu_1 \leq \mu_3, \ \mu_2 \leq \mu_3, \ \langle exn \rangle \leq \mu_3) \ \Rightarrow (() \to \mu_1 \ (), \ () \to \mu_2 \ ()) \to \mu_3 \ ()$$

This is the choice made in an earlier version of Koka described as a technical report [38]. However, in our experience with that system in practice we felt the constraints often became quite complex and the combination of polymorphism with subtyping can make type inference undecidable.

The approach we advocate in this paper and which is adopted by Koka is the use of row-polymorphism on effects. Row polymorphism is well understood and used for many inference systems for record calculi [7, 17, 23, 31, 34, 35]. We use the notation  $\langle l \mid \mu \rangle$  to extend an effect row  $\mu$  with an effect constant l. Rows can now have two forms, either a *closed* effect  $\langle exn, div \rangle$ , or an *open* effect ending in an effect variable  $\langle exn, div \mid \mu \rangle$ . Using an open effect, our system infers the following type for *foo*:

foo: 
$$\forall \mu. (() \rightarrow \langle exn \mid \mu \rangle (), () \rightarrow \langle exn \mid \mu \rangle ()) \rightarrow \langle exn \mid \mu \rangle ()$$

The reader may worry at this point that the row polymorphic type is more restrictive than the earlier type using subtype constraints: indeed, the row polymorphic type requires that each function argument now has the same effect  $\langle exn | \mu \rangle$ . However, in a calling context foo(f,g) our system ensures that we always infer a polymorphic open effect for each expression f and g. For example,  $f:() \to \langle exn | \mu_1 \rangle$  () and  $g:() \to \langle div | \mu_2 \rangle$  (). This allows the types  $\langle exn | \mu_1 \rangle$  and  $\langle div | \mu_2 \rangle$  to unify into a common type  $\langle exn, div | \mu_3 \rangle$  such that they can be applied to foo, resulting in an inferred effect  $\langle exn, div | \mu_3 \rangle$  for foo(f,g).

### **2.4. Duplicate effects**

Our effect rows differ in an important way from the usual approaches in that effect labels can be duplicated, i.e. h*exn*,*exn*i 6≡ h*exn*i **(1)**. This was first described by Leijen [\[17\]](#page-21-5) where this was used to enable scoped labels in record types. Enabling duplicate labels fits our approach well: first of all, it enables principal unification without needing extra constraints, and secondly, it enables us to give precise types to effect elimination forms (like catching exceptions).

In particular, during unification we may end up with constraints of the form h*exn* |µi ∼ h*exn*i. With regular row-polymorphism which are sets of labels, such constraint can have multiple solutions, namely µ = hi or µ = h*exn*i. This was first observed by Wand [\[43\]](#page-23-1) in the context of records. Usually, this problem is fixed by either introducing *lacks* constraints [\[7\]](#page-21-4) or polymorphic presence and absence flags on each label [\[32\]](#page-22-10) (as used by Lindley and Cheney [\[23\]](#page-22-6) for an effect system in the context of database queries). The problem with both approaches is that they complicate the type system quite a bit. With *lacks* contstraints we need a system of qualified types as in Haskell, while with presece and absence flags, we need a kind system that tracks for each type variable which labels cannot be present.

With rows allowing duplicate labels, we avoid any additional machinery and can use straight forward type inference techniques. In our case µ = hi is the only solution to the above constraint (due to (1)).

Moreover, duplicate labels make it easy to give types to effect elimination forms. For example, catching effects removes the *exn* effect:

$$catch: \forall \alpha \mu. (() \rightarrow \langle exn \mid \mu \rangle \ \alpha, \ exception \rightarrow \mu \ \alpha) \rightarrow \mu \ \alpha$$

Here we assume that *catch* takes two functions, the action and the exception handler that takes as an argument the thrown *exception*. The *exn* effect of the action is discarded in the final effect µ since all exceptions are caught by the handler. But of course, the handler can itself throw an exception and have an *exn* effect itself. In that case µ will unify with a type of the form h*exn*|µ ′ i giving action the effect h*exn*|*exn*|µ ′ i where *exn* occurs duplicated, which gives us exactly the right behavior. Note that with *lacks* constraints we would not be able to type this example because there would be a *exn* 6∈ µ constraint. We can type this example using flags but the type would arguably be more complex with a polymorphic presence/absence flag ϕ on the *exn* label in the result effect, something like:

$$catch: \forall \mu \alpha \phi. (() \rightarrow \langle exn_{\bullet} | \mu \rangle \alpha, exception \rightarrow \langle exn_{\phi} | \mu \rangle \alpha) \rightarrow \langle exn_{\phi} | \mu \rangle \alpha$$

There is one situation where an approach with flags is more expressive though: with flags one can state specifically that a certain effect must be absent. This is used for example in the effect system by Lindley and Cheney [\[23\]](#page-22-6) to enforce that database queries never have the *wild* effect (*io*). In our setting we can only enforce absence of an effect by explicitly listing a closed row of the allowed effects which is less modular. In our current experience this has not yet proven to be a problem in practice though but we may experiment with this in the future.

### **2.4.1. Injection**

There are some situations where having duplicate effects is quite different from other approaches though. Intuitively, we can do a monadic translation of a Koka program where effect types get translated to a sequence of monad transformers. Under such interpretation, duplicate effects would have real semantic significance. For example, we could provide an *injection* operation for exceptions:

inject: 
$$\forall \mu \alpha. (() \rightarrow \langle exn | \mu \rangle \alpha) \rightarrow (() \rightarrow \langle exn | exn | \mu \rangle \alpha)$$

Semantically, it would inject an extra exception layer, such that a *catch* operation would only catch exceptions raised from the outer *exn*, while passing the inner injected exceptions through. Internally, one can implement this by maintaining level numbers on thrown exceptions – increasing them on an *inject* and decreasing them on a *catch* (and only catching level 0 exceptions).

Now, suppose we have some library code whose exceptions we do not want to handle, but we do want to handle the exceptions in our own code. In that case, we could write something like:

```
catch( function() {
     ... my code ...
     x = inject( ... library code ...)()
     ... my code ...
     inject( ...morelibrarycode ...)()
}, handler )
```

In the example, all exceptions in 'my code' are caught, while exceptions raised in the library code are only caught by an outer exception handler. For this article though, we will not further formalize *inject* but only describe the core calculus.

### 2.5. Heap effects

One of the most useful side-effects is of course mutable state. Here is an example where we give a linear version of the fibonacci function using imperative updates:

```
 \begin{split} & \mathsf{function}\, \mathit{fib}(\,n\,:\mathit{int}\,)\, \big\{ \\ & \mathsf{val}\, x = \mathit{ref}(0);\, \mathsf{val}\, y = \mathit{ref}(1) \\ & \mathsf{repeat}(n)\, \big\{ \\ & \mathsf{val}\, y_0 = \,!y;\, y := \,!x + !y;\, x := \,y_0 \\ & \big\} \\ & \, !x \\ \big\} \end{aligned}
```

Here x and y are bound to freshly allocated references of type  $ref\langle h, int \rangle$ . The operator (!) dereferences a reference while the operator (:=) is used for assignment to references. Due to the reading and writing of x and y of type  $ref\langle h, int \rangle$ , the effect inferred for the body of the function is  $st\langle h \rangle$  for some heap h:

```
fib : \forall h. int \rightarrow st \langle h \rangle int
```

However, we can of course consider the function fib to be total: for any input, it always returns the same output since the heap h cannot be modified or observed from outside this function. In particular, we can safely remove the effect  $st\langle h \rangle$  whenever the function is polymorphic in the heap h and where h is not among the free type variables of argument types or result type. This notion corresponds directly to the use of the higher-ranked runST function in Haskell [30] (which we will call just run):

```
run: \forall \mu \alpha. (\forall h. () \rightarrow \langle st \langle h \rangle \mid \mu \rangle \alpha) \rightarrow \mu \alpha
```

Koka will automatically insert a *run* wrapper at generalization points if it can be applied, and infers a total type for the above fibonacci function:

```
fib : int \rightarrow total int
```

Again, using row polymorphism is quite natural to express in the type of *run* where the *st*h*h*i effect can be dismissed.

One complex example from a type inference perspective where we applied Koka, is the Garsia-Wachs algorithm as described by Filliˆatre [\[6\]](#page-21-6). The given algorithm was originally written in ML and uses updateable references in the leaf nodes of the trees to achieve efficiency comparable to the reference C implementation. However, Filliˆatre remarks that these side effects are local and not observable to any caller. We implemented Filliˆatre's algorithm in Koka and our system correctly inferred that the state effect can be discarded and assigned a pure effect to the Garsia-Wachs algorithm [\[18\]](#page-21-2).

### **2.6. Heap safety**

Combining polymorphism and imperative state is fraught with difficulty and requires great care. In particular, *let*-polymorphism may lead to unsoundness if references can be given a polymorphic type. A classical example from ML is:

$$let r = ref [] in (r := [true], !r+1)$$

Here, we let bind *r* to a reference with type ∀<sup>α</sup>. *ref*h*list*hαii. The problem is that this type can instantiate later to both a reference to an integer list and a boolean list. Intuitively, the problem is that the first binding of *r* generalized over type variables that are actually free in the heap. The ML language considered many solutions to prevent this from happening, ranging from imperative type variables [\[39\]](#page-22-12) to the current syntactic value restriction, where only value expressions can be generalized.

In our system, no such tricks are necessary. Using the effect types, we restrict generalization to expressions that are total, and we reject the ML example since we will not generalize over the type of *r* since it has an *alloc*h*h*i effect. We prove in Section [5.1](#page-15-0) that our approach is semantically sound. In contrast to the value restriction, we can still generalize over any expression that is not stateful regardless of its syntactic form.

The addition of *run* adds further requirements where we must ensure that encapsulated stateful computations truly behave like a pure function and do not 'leak' the state. For example, it would be unsound to let a reference escape its encapsulation:

```
run( function(){ ref(1) } )
```

or to encapsulate a computation where its effects can still be observed.

We prove in Section [5.2](#page-17-0) that well-typed terms never exhibit such behavior. To our knowledge we are the first to prove this formally for a strict language in combination with exceptions and divergence. A similar result is by Launchbury and Sabry [\[16\]](#page-21-7) where they prove heap safety of the Haskell's ST monad in the context of a lazy store with lazy evaluation.

### **2.7. Divergence**

Koka uses a simple termination checker (based on [\[1\]](#page-21-8)) to assign the divergence effect to potentially nonterminating functions. To do this safely, Koka has three kinds of data types, inductive, co-inductive, and arbitrary recursive data types. In particular, we restrict (co)inductive data types such that the type itself cannot occur in a negative position. Any function that matches on an arbitrary recursive data type is assumed to be potentially divergent since one can encode the Y combinator using such data type and write a non-terminating function that is not syntactically recursive.

Recursively defined functions should of course include the divergence effect in general. However, if the termination checker finds that each recursive call decreases the size of an inductive data type (or is productive for a co- inductive data type), then we do not assign the divergent effect. The current analysis is quite limited and syntactically fragile but seems to work well enough in practice (Section 2.8). For our purpose, we prefer a predictable analysis with clear rules.

However, in combination with higher-order mutable state, we can still define functions that are not syntactically recursive, but fail to terminate. Consider 'Landin's knot':

```
\begin{array}{l} \mathsf{function}\,\mathit{diverge}() \ \{ \\ \mathsf{val}\,r := \mathit{ref}(\mathit{id}) \\ \mathsf{function}\,\mathit{foo}() \, \{ \, (!r)() \, \} \\ r := \mathit{foo} \\ \mathit{foo}() \\ \} \end{array}
```

In this function, we first create a reference r initialized with the identify function. Next we define a local function foo which calls the function in r. Then we assign foo itself to r and call foo, which will now never terminate even though there is no syntactic recursion.

How can we infer in general that *diverge* must include the *div* effect? It turns out that in essence reading from the heap may result in divergence. A conservative approach would be to assign the *div* effect to the type of read (!). For simplicity, this is what we will do in the formal development.

But in Koka we use a more sophisticated approach. In order to cause divergence, we actually need to read a function from the heap which accesses the heap itself. Fortunately, our effect system makes this behavior already apparent in the inferred types! – in our example, the effect of *foo* contains  $read\langle h \rangle$ , which is being stored in a reference in the same heap of type  $ref\langle h, () \rightarrow read\langle h \rangle$  () $\rangle$ .

The trick is now that we generate a type constraint  $hdiv\langle h, \tau, \varepsilon \rangle$  for every heap read that keeps track of heap type h, the type of the value that was read  $\tau$  and the current effect  $\varepsilon$ . The constraint  $hdiv\langle h, \tau, \varepsilon \rangle$  expresses that if  $h \in \text{ftv}(\tau)$  then the effect  $\varepsilon$  must include divergence. In particular, this constraint is fine-grained enough that any reading of a non-function type, or non-stateful functions will never cause divergence (and we can dismiss the constraint) The drawback is that if  $\tau$  is polymorphic at generalization time, we need to keep the constraint around (as we cannot decide at that point whether h will ever be in  $\text{ftv}(\tau)$ ), which in turn means we need to use a system of qualified types [12]. Currently this is not fully implemented yet in Koka, and if at generalization time we cannot guarantee  $\tau$  will never contain a reference to the heap h, we conservatively assume that the function may diverge.

#### <span id="page-7-0"></span>2.8. Koka in practice

When designing a new type system it is always a question how well it will work in practice: does it infer the types you expect? Do the types become too complicated? Is the termination checker strong enough? etc. We have implemented the effect inference and various extensions in the Koka language which is freely available on the web [18]. The Koka system currently has a JavaScript backend and can generate code that runs in NodeJS or a web page. We have written many small to medium sized samples to see how well the system works in practice.

**Markdown** One application is a fully compliant Markdown text processor. This program consists of three phases where it first parses block elements, performs block analysis, collects link definitions,

numbers sections, and finally renders the inline elements in each block. The program passes the full Markdown test suite. In fact, this article has been written itself as a Madoko document [20].

Remarkably, almost all functions are inferred to be *total*, and only a handful of driver functions perform side effects, like reading input files. For efficiency though, many internal functions use local state. For example, when rendering all inline elements in a block, we use a local mutable string builder (of type  $builder\langle h \rangle$ ) to build the result string in constant time (actual Koka code):

```
function formatInline( ctx: inlineCtx, txt: string): string { formatAcc(ctx, builder(), txt) } function formatAcc( ctx: inlineCtx, acc: builder\langle h \rangle, txt: string): st\langle h \rangle string { if (txt == "") return acc.string val (s,next) = matchRules(ctx.grammar, ctx, txt, id) formatAcc(ctx, acc.append(s), txt.substr_1(next)) }
```

Note how *formatAcc* is stateful due to the calls to the *append* and *string* methods of the string builder *acc*, but the outer function *formatInline* is inferred to be *total* since Koka can automatically apply the *run* function and encapsulate the state: indeed it is not observable if we use a mutable string builder internally or not. This pattern also occurs for example in the block analysis phase where we use a mutable hashmap to build the dictionary of link definitions.

**Safe tier-splitting** Most of the HTML5 DOM and the Node API's are available in Koka which allows us to write more substantial programs and evaluate the effect inference system in practice. We use the effect *dom* for functions that may have any side effect through a DOM call.

On the web, many programs are split in a server and client part communicating with each other. It is advantageous to write both the client and server part as one program since that enables us to share one common type definition for the data they exchange. Also, their interaction will be more apparent, and they can share common functionality, like date parsing, to ensure that both parts behave consistently.

Safely splitting a program into a server and client part is difficult though. For example, the client code may call a library function that itself calls a function that can only be run on the server (like writing to a log file), or the other way around. Moreover, if the client and server part both access a shared global variable (or both call a library function that uses an internal global variable) then we cannot split this code anymore.

The Koka effect types tackle both problems and enable fully safe tier splitting. Our main tier splitting function has the following (simplified) type signature:

```
function tiersplit( serverPart: () \rightarrow server((\alpha \rightarrow server()) \rightarrow server(\beta \rightarrow server())), clientPart: (\beta \rightarrow client()) \rightarrow client(\alpha \rightarrow client()) ): io() where the server and client effects are defined as: alias server = io alias client = \langle dom, div \rangle
```

```
\kappa ::= * | e | k | h values, effect rows, effect constants, heaps
                       (\kappa_1, ..., \kappa_n) \rightarrow \kappa type constructor
             \begin{array}{ll} \tau^k ::= \alpha^k & \text{type variable (using } \mu \text{ for effects,} \xi \text{ for heaps)} \\ \mid c^{\kappa} & \text{type constant} \\ \mid c^{\kappa_0} \langle \tau_1^{\kappa_1}, ..., \tau_n^{\kappa_n} \rangle & \kappa_0 = (\kappa_1, ..., \kappa_n) \to \kappa \end{array}
types
schemes \sigma ::= \forall \alpha_1...\alpha_n. \tau^*
constants ()
                                                                     unit type
                   (-\rightarrow --) :: (*,e,*) \rightarrow * functions
                    \begin{array}{cccccccccccccccccccccccccccccccccccc
                                   :: (h,*) \rightarrow * references
                   exn.div :: k
                                                                     partial, divergent
                                   :: h \rightarrow k
                                                                     stateful
syntactic sugar \tau_1 \rightarrow \tau_2 = \tau_1 \rightarrow \langle \rangle \tau_2
                             \langle l_1,...,l_n \mid \varepsilon \rangle = \langle l_1 ... \langle l_n \mid \varepsilon \rangle ... \rangle
                             \langle l_1,...,l_n\rangle = \langle l_1,...,l_n \mid \langle \rangle \rangle
```

**Figure 1.** Syntax of types and kinds. An extra restriction is that effect constants cannot be type variables, i.e.  $\alpha^k$  is illegal.

The *tiersplit* function takes a server and client function and sets up a socket connection. On the server it will call the server part function which can initialize. Now, both the client and server part can be called for each fresh connection where *tiersplit* supplies a *send* function that takes a message of type  $\alpha$  for client messages, and  $\beta$  for server messages. Both the client and server part return a fresh 'connection' function that handles incoming messages from the server or client respectively. Note how this type guarantees that messages sent to the client, and messages handled by the client, are both of type  $\alpha$ , while for the server messages they will be  $\beta$ . Furthermore, because the effect types for *server* and *client* are closed, the client and server part are only able to call functions available for the client or server respectively.

Finally, the Koka effect system also prevents accidental sharing of global state by the client and server part. Both the client and server can use state that is contained in their handler. In that case the  $st\langle h\rangle$  effect will be inferred, and discarded because h will generalize. However, if either function tries to access a shared variable in an outer scope, then the h will *not* generalize (because the variable will have type  $ref\langle h,a\rangle$  and therefore h is not free in the environment), in which case the inferred  $st\langle h\rangle$  effect cannot be removed. Again, this will lead to a unification failure and the program will be statically rejected.

## <span id="page-9-0"></span>3. The type system

In this section we are going to give a formal definition of our polymorphic effect system for a small core-calculus that captures the essence of Koka. We call this  $\lambda^k$ . Figure 1 defines the syntax of types. The well-formedness of types  $\tau$  is guaranteed by a simple kind system. We put the kind  $\kappa$  of a type  $\tau$  in superscript, as  $\tau^{\kappa}$ . We have the usual kind \* and  $\rightarrow$ , but also kinds for effect rows (e), effect constants (k), and heaps (h). Often the kind of a type is immediately apparent or not relevant, and most of the time we will not denote the kind to reduce clutter, and just write plain types  $\tau$ . For clarity, we are using  $\alpha$  for

$$\begin{array}{c} (\text{EQ-REFL}) \; \boldsymbol{\varepsilon} \equiv \boldsymbol{\varepsilon} \quad (\text{EQ-TRANS}) \; \frac{\boldsymbol{\varepsilon}_1 \; \equiv \boldsymbol{\varepsilon}_2 \quad \boldsymbol{\varepsilon}_2 \; \equiv \boldsymbol{\varepsilon}_3}{\boldsymbol{\varepsilon}_1 \; \equiv \boldsymbol{\varepsilon}_3} \\ \\ (\text{EQ-HEAD}) \; \frac{\boldsymbol{\varepsilon}_1 \; \equiv \boldsymbol{\varepsilon}_2}{\langle l \, | \, \boldsymbol{\varepsilon}_1 \rangle \; \equiv \langle l \, | \, \boldsymbol{\varepsilon}_2 \rangle} \; \; (\text{EQ-SWAP}) \; \frac{l_1 \; \not\equiv l_2}{\langle l_1 \, | \, \langle l_2 \, | \, \boldsymbol{\varepsilon} \rangle \rangle \; \equiv \langle l_2 \, | \, \langle l_1 \, | \, \boldsymbol{\varepsilon} \rangle \rangle} \\ \\ (\text{UNEQ-LAB}) \; \frac{c \; \not= c'}{c \langle \tau_1, ..., \tau_n \rangle \; \not\equiv c' \langle \tau_1', ..., \tau_n' \rangle} \end{array}$$

**Figure 2.** Effect equivalence.

regular type variables,  $\mu$  for effect type variables, and  $\xi$  for heap type variables.

Effect types are defined as a row of effect labels l. Such effect row is either empty  $\langle \rangle$ , a polymorphic effect variable  $\mu$ , or an extension of an effect row  $\varepsilon$  with an effect constant l, written as  $\langle l|\varepsilon\rangle$ . The effect constants can be anything that is interesting to our language. For our purposes we will restrict the constants to exceptions (exn), divergence (div), and heap operations (st). It is no problem to generalize this to the more fine-grained hierarchy of Koka but this simplifies the presentation and proofs. The kind system ensures that an effect is always either a *closed effect* of the form  $\langle l_1, ..., l_n \rangle$ , or an *open effect* of the form  $\langle l_1, ..., l_n | \mu \rangle$ .

Figure 2 defines an equivalence relation ( $\equiv$ ) between effect types where we consider effects equivalent regardless of the order of the effect constants. In contrast to many record calculi [7, 32, 34] effect rows do allow duplicate labels where an effect  $\langle exn, exn \rangle$  is allowed (and not equal to the effect  $\langle exn \rangle$ ). The definition of effect equality is essentially the same as for scoped labels [17] where we ignore the type components. Note that for rule (EQ-SWAP) we use the rule (UNEQ-LAB) to compare effect constants where the type arguments are not taken into account: intuitively we consider the effect constants as the 'labels' of an effect record. Most constants compare directly. The only exception in our system is the state effect where  $st\langle h_1 \rangle \not\equiv st\langle h_2 \rangle$  does *not* hold even if  $h_1 \neq h_2$ .

Using effect equality, we define  $l \in \varepsilon$  iff  $e \equiv \langle l | \varepsilon' \rangle$  for some  $\varepsilon'$ .

#### <span id="page-10-0"></span>3.1. Type rules

Figure 3 defines the formal type rules of our effect system. The rules are defined over a small expression calculus:

```
e ::= x \mid p \mid e_1 e_2 \mid \lambda x. e (variables, primitives, applications, functions)

\mid x \leftarrow e_1; e_2 \mid \text{let } x = e_1 \text{ in } e_2 (sequence and let bindings)

\mid \text{catch } e_1 e_2 \mid \text{run } e (catch exceptions and isolate state)
```

$$p ::= () \mid \text{fix} \mid \text{throw} \mid \text{new} \mid (!) \mid (:=) \text{ (primitives)}$$

This expression syntax is meant as a surface syntax, but when we discuss the semantics of the calculus, we will refine and extend the syntax further (see Figure 4). We use the bind expression  $x \leftarrow e_1$ ;  $e_2$  for a monomorphic binding of a variable x to an expression  $e_1$  (which is really just syntactic sugar for the application  $(\lambda x. e_2) e_1$ ). We write  $e_1$ ;  $e_2$  as a shorthand for the expression  $x \leftarrow e_1$ ;  $e_2$  where  $x \notin fv(e_2)$ . We have added run and catch as special expressions since this simplifies the presentation where we can give direct type rules for them. Also, we simplified both catch and throw by limiting the exception type to the unit type (()).

$$(VAR) \frac{\Gamma(x) = \sigma}{\Gamma \vdash x : \sigma \mid \varepsilon} \qquad (APP) \frac{\Gamma \vdash e_1 : \tau_2 \rightarrow \varepsilon \tau \mid \varepsilon \quad \Gamma \vdash e_2 : \tau_2 \mid \varepsilon}{\Gamma \vdash e_1 e_2 : \tau \mid \varepsilon}$$

$$(LAM) \frac{\Gamma, x : \tau_1 \vdash e : \tau_2 \mid \varepsilon_2}{\Gamma \vdash \lambda x . e : \tau_1 \rightarrow \varepsilon_2 \tau_2 \mid \varepsilon} \qquad (LET) \frac{\Gamma \vdash e_1 : \sigma \mid \langle \rangle \quad \Gamma, x : \sigma \vdash e_2 : \tau \mid \varepsilon}{\Gamma \vdash \text{let } x = e_1 \text{ in } e_2 : \tau \mid \varepsilon}$$

$$(GEN) \frac{\Gamma \vdash e : \tau \mid \langle \rangle \quad \overline{\alpha} \not\in \text{ftv}(\Gamma)}{\Gamma \vdash e : \forall \overline{\alpha} . \tau \mid \varepsilon} \qquad (RUN) \frac{\Gamma \vdash e : \tau \mid \langle \text{st}\langle \xi \rangle \mid \varepsilon \rangle \quad \xi \not\in \text{ftv}(\Gamma, \tau, \varepsilon)}{\Gamma \vdash \text{run} e : \tau \mid \varepsilon}$$

$$(INST) \frac{\Gamma \vdash e : \forall \overline{\alpha} . \tau \mid \varepsilon}{\Gamma \vdash e : \overline{\alpha} : \overline{\epsilon}} \tau \mid \varepsilon \qquad (CATCH) \frac{\Gamma \vdash e_1 : \tau \mid \langle \text{exn} \mid \varepsilon \rangle \quad \Gamma \vdash e_2 : () \rightarrow \varepsilon \tau \mid \varepsilon}{\Gamma \vdash \text{catch } e_1 e_2 : \tau \mid \varepsilon}$$

$$(ALLOC) \quad \Gamma \vdash \text{ref} \qquad : \tau \rightarrow \langle \text{st}\langle h \rangle \mid \varepsilon \rangle \text{ref}\langle h, \tau \rangle \mid \varepsilon'$$

$$(READ) \quad \Gamma \vdash (!) \qquad : \text{ref}\langle h, \tau \rangle \rightarrow \langle \text{st}\langle h \rangle, \text{div} \mid \varepsilon \rangle \tau \mid \varepsilon'$$

$$(WRITE) \quad \Gamma \vdash (:=) \qquad : (\text{ref}\langle h, \tau \rangle, \tau) \rightarrow \langle \text{st}\langle h \rangle \mid \varepsilon \rangle () \mid \varepsilon'$$

$$(THROW) \quad \Gamma \vdash \text{throw} : () \rightarrow \langle \text{exn} \mid \varepsilon \rangle \tau \mid \varepsilon'$$

$$(UNIT) \quad \Gamma \vdash () \qquad : () \mid \varepsilon$$

$$(FIX) \quad \Gamma \vdash \text{fix} \qquad : ((\tau_1 \rightarrow \langle \text{div} \mid \varepsilon \rangle \tau_2) \rightarrow (\tau_1 \rightarrow \langle \text{div} \mid \varepsilon \rangle \tau_2)) \rightarrow (\tau_1 \rightarrow \langle \text{div} \mid \varepsilon \rangle \tau_2) \mid \varepsilon'$$

**Figure 3.** General type rules with effects.

The type rules are stated under a type environment  $\Gamma$  which maps variables to types. An environment can be extended using a comma. If  $\Gamma'$  is equal to  $\Gamma, x : \sigma$  then  $\Gamma'(x) = \sigma$  and  $\Gamma'(y) = \Gamma(y)$  for any  $y \neq x$ . A type rule of the form  $\Gamma \vdash e : \sigma \mid \varepsilon$  states that under an environment  $\Gamma$  the expression e has type  $\sigma$  with an effect  $\varepsilon$ .

Most of the type rules in Figure 3 are quite standard. The rule (VAR) derives the type of a variable. The derived effect is any arbitrary effect  $\varepsilon$ . We may have expected to derive only the total effect  $\langle \rangle$  since the evaluation of a variable has no effect at all (in our strict setting). However, there is no rule that lets us upgrade the final effect and instead we get to pick the final effect right away. Another way to look at this is that since the variable evaluation has no effect, we are free to assume any arbitrary effect.

The (LAM) rule is similar: the evaluation of a lambda expression is a value and has no effect and we can assume any arbitrary effect  $\varepsilon$ . Interestingly, the effect derived for the body of the lambda expression,  $\varepsilon_2$ , shifts from the derivation on to the derived function type  $\tau_1 \to \varepsilon_2$   $\tau_2$ : indeed, calling this function and evaluating the body causes the effect  $\varepsilon_2$ . The (APP) is also standard, and derives an effect  $\varepsilon$  requiring that its premises derive the same effect as the function effect.

Instantiation (INST) is standard and instantiates a type scheme. The generalization rule (GEN) has an interesting twist: it requires the derived effect to be total  $\langle \rangle$ . It turns out this is required to ensure a sound semantics as we show in Section 4. Indeed, this is essentially the equivalent of the value restriction in ML [21]. Of course, in ML effects are not inferred by the type system and the value restriction syntactically restricts the expression over which one can generalize. In our setting we can directly express that we only generalize over total expressions. The rule (LET) binds expressions with a polymorphic type scheme  $\sigma$  and just like (GEN) requires that the bound expression has no effect. It turns out that is still sound to allow more effects at generalization and let bindings. In particular, we can allow exn, div. However, for the formal development we will only consider the empty effect for now.

All other rules are just type rules for the primitive constants. Note that all the effects for the primitive constants are open and can be freely chosen (just as in the (VAR) rule). This is important as it allows us to always assume more effects than induced by the operation. In this article we limit exceptions to just the unit value () but of course in a practical implementation this would be a proper exception type. However, note that any exception type must be restricted to base values only and cannot contain function values! If this would be allowed our divergence theorem [4](#page-18-0) (in Section [6\)](#page-18-0) would not hold – indeed, unchecked exceptions that can include non-base values can be more expressive than call/cc [\[22\]](#page-22-14).

Given these type rules, we can construct an efficient type inference algorithm that infers principal types and is sound and complete with respect to the type rules. This is described in detail in Appendix [A](#page-24-0) and a separate technical report [\[19\]](#page-21-3).

### **3.2. Simplifying types**

The rule (APP) is a little surprising since it requires both the effect of the function and the argument to be the same. This only works because we set things up to always be able to infer effects on functions that are 'open' – i.e. have a polymorphic µ in their tail. For example, consider the identify function:

$$id = \lambda x. x$$

If we assign the valid type ∀<sup>α</sup>. <sup>α</sup> → hi <sup>α</sup> to the *id* function, we get into trouble quickly. For example, the application *id* (*throw* ()) would not type check since the effect of *id* is total while the effect of the argument is h*exn*|µi. Of course, the type inference algorithm always infers a most general type for *id*, namely:

$$id: \forall \alpha \mu. \ \alpha \rightarrow \mu \ \alpha$$

which has no such problems.

However, in practice we may wish to simplify the types more: for most users it is more natural to state that *id* is total, instead of stating that *id* can be any assigned any effect. One possible way that we explored in Koka was to display types in a simplified form. In particular, we can *close* a type of a let-bound variable of the form:

$$\forall \mu \alpha_1...\alpha_n. \ \tau_1 \to \langle l_1,...,l_m | \mu \rangle \ \tau_2)$$

where <sup>µ</sup> 6∈ ftv(<sup>τ</sup>1,<sup>τ</sup>2,*l*1,...,*lm*), to:

$$\forall \alpha_1...\alpha_n. \ \tau_1 \rightarrow \langle l_1,...,l_m \rangle \ \tau_2$$

However, this is not an ideal solution since in practice users often annotate functions with the more restrictive closed type. The solution we adopted in Koka is to actually close *all* the types of *let-bound* variables according the above rule, and at instantiation of such let-bound variable, we *open* the type again, introducing a fresh µ for any function type with a closed effect.

The way our system is set up in this paper, the most general type for a let-bound function will always have an open effect type, and therefore the programs accepted under the Koka system will be exactly the same. In general though, if we allow function constants with a closed effect type, then the more liberal Koka system may accept more programs since it will instantiate all such function types with a closed effect to an open effect. Of course, this is still a sound extension since we can always soundly assume more effects. Finally, note that we can only apply this form of simplification to let-bound variables, and not to lambda-bound parameters or otherwise type inference is no longer principal.

```
e ::= v | e1 e2 | let x = e1 in e2 (values, applications, let bindings)
  | hpϕ.e | rune (heap binding and isolation)
v ::= λx.e | catche (functions and partial catch)
  | b (basic value (contains no e))
b ::= x | c (variable and constants)
  | fix | throw | catch (fixpoint and exceptions)
  | r | ref | (!) | (:=) | (r :=) (references)
w ::= b | throwc (basic value or exception)
a ::= v | throwc | hpϕ.v | hpϕ.throwc (answers)
ϕ ::= hr1 7→ v1i ... hrn 7→ vni (heap bindings)
```

**Figure 4.** Full expression syntax

$$(\text{HEAP}) \frac{\forall \langle r_i \mapsto v_i \rangle \in \varphi. \ \Gamma, \overline{\varphi}_h \vdash v_i : \tau_i \mid \langle \rangle}{\Gamma, \overline{\varphi}_h \vdash e : \tau \mid \langle st \langle h \rangle \mid \varepsilon \rangle} \frac{\Gamma, \overline{\varphi}_h \vdash e : \tau \mid \langle st \langle h \rangle \mid \varepsilon \rangle}{\Gamma \vdash hp \varphi. e : \tau \mid \langle st \langle h \rangle \mid \varepsilon \rangle}$$

$$(\text{CONST}) \frac{\text{typeof}(c) = \sigma}{\Gamma \vdash c : \sigma \mid \varepsilon}$$

**Figure 5.** Extra type rules for heap expressions and constants. We write <sup>ϕ</sup>*<sup>h</sup>* for the conversion of a heap <sup>ϕ</sup> to a type environment: if <sup>ϕ</sup> equals h*r*<sup>1</sup> 7→ *v*1,..., *r<sup>n</sup>* 7→ *vn*i then <sup>ϕ</sup>*<sup>h</sup>* = *r*<sup>1</sup> : *ref*h*h*,<sup>τ</sup>1i,...,*r<sup>n</sup>* : *ref*h*h*,<sup>τ</sup>*n*i for some <sup>τ</sup><sup>1</sup> to <sup>τ</sup>*n*.

## <span id="page-13-0"></span>**4. Semantics of effects**

In this section we are going to define a precise semantics for our language, and show that well-typed programs cannot go 'wrong'. In contrast to our earlier soundness and completeness result for the type inference algorithm, the soundness proof of the type system in Hindley-Milner does not carry over easily in our setting: indeed, we are going to model many complex effects which is fraught with danger.

First, we strengthen our expression syntax by separating out value expressions *v*, as shown in Figure [4.](#page-13-0) We also define basic values *b* as values that cannot contain expressions themselves. Moreover, we added a few new expressions, namely heap bindings (hpϕ.*e*), a partially applied catch (catch*e*), a partially applied assignments (*v* :=), and general constants (*c*). Also, we denote heap variables using *r*. An expression hph*r*<sup>1</sup> 7→ *v*1i,...,h*r<sup>n</sup>* 7→ *vn*i.*e* binds *r*<sup>1</sup> to *r<sup>n</sup>* in *v*1,...,*v<sup>n</sup>* and *e*. By convention, we always require *r*<sup>1</sup> to *r<sup>n</sup>* to be distinct, and consider heaps <sup>ϕ</sup> equal modulo alpha-renaming.

The surface language never exposes the heap binding construct hpϕ.*e* directly to the user but during evaluation the reductions on heap operations create heaps and use them. In order to give a type to such expression, we need an extra type rule for heap bindings, given in Figure [5.](#page-13-0) Note how each heap value is typed under an enviroment that contains types for all bindings (much like a recursive let binding). Moreover, a heap binding induces the stateful effect *st*h*h*i. In the type rule for constants we assume a function typeof(*c*) that returns a closed type scheme for each constant.

```
(\delta)
                   cv
                                                                   \longrightarrow \delta(c,v) if \delta(c,v) is defined
                                                                   \longrightarrow [x \mapsto v]e
(\beta)
                   (\lambda x. e) v
                   let x = v in e
                                                                   \longrightarrow [x \mapsto v]e
(LET)
                                                                   \longrightarrow v(\lambda x. (\text{fix } v)x)
(FIX)
                   fix v
(THROW) X[\text{throw } c]
                                                                   \longrightarrow throw c
                                                                                               if X \neq []
(CATCHT) catch (throw c) e
                                                                   \longrightarrow ec
(CATCHV) catch ve
                                                                   \longrightarrow v
                                                                  \longrightarrow \operatorname{hp}\langle r \mapsto v \rangle . r
(ALLOC)
                   hp \varphi \langle r \mapsto v \rangle . R[!r]
                                                                 \longrightarrow \operatorname{hp} \varphi \langle r \mapsto v \rangle . R[v]
(READ)
                   \mathsf{hp}\, \varphi(r \mapsto v_1).R[r := v_2] \longrightarrow \mathsf{hp}\, \varphi(r \mapsto v_2).R[()]
(WRITE)
                                                                 \longrightarrow \mathsf{hp}\, \varphi_1 \varphi_2.e
(MERGE)
                   hp \varphi_1. hp \varphi_2. e
(LIFT)
                   R[\mathsf{hp}\,\boldsymbol{\varphi}.e]
                                                                  \longrightarrow \operatorname{hp} \varphi.R[e] \quad \text{if } R \neq []
                   run [hp \varphi.] \lambda x.e
                                                                 \longrightarrow \lambda x. \operatorname{run}([\operatorname{hp} \boldsymbol{\varphi}.] e)
(RUNL)
                                                                   \longrightarrow catch (run ([hp \varphi.] e))
(RUNC)
                   run [hp \varphi.] catch e
                   run [hp \varphi.] w
                                                                  \longrightarrow w \quad \text{if } \mathsf{frv}(w) \not \cap \mathsf{dom}(\boldsymbol{\varphi})
(RUNH)
                                            Evaluation contexts:
       X ::= [] | X e | v X | \text{let } x = X \text{ in } e
       R ::= [] | Re | vR | let x = R in e | catch Re
       E ::= [] | E e | v E | let x = E lin e | catch E e | hp <math>\varphi. E | run E
```

Figure 6. Reduction rules and evaluation contexts.

### <span id="page-14-0"></span>4.1. Reductions

We can now consider primitive reductions for the various expressions as shown in Figure 6. The first four reductions are standard for the lambda calculus. To abstract away from a particular set of constants, we assume a function  $\delta$  which takes a constant and a closed value to a closed value. If  $\operatorname{typeof}(c) = \forall \overline{\alpha}. \tau_1 \to \varepsilon \tau_2$ , with  $\theta = [\overline{\alpha} \mapsto \overline{\tau}]$  and  $\cdot \vdash \nu : \theta \tau_1 \mid \langle \rangle$ , then  $\delta(c, \nu)$  is defined, and  $\cdot \vdash \delta(c, \nu) : \theta \tau_2 \mid \theta \varepsilon$ . The reductions  $\beta$ , (LET) and (FIX) are all standard.

The next three rules deal with exceptions. In particular, the rule (THROW) progates exceptions under a context X. Since X does not include catch  $e_1e_2$ , hp  $\varphi$ . e or run e, this propagates the exception to the nearest exception handler or state block. The (CATCHT) reduction catches exceptions and passes them on to the handler. If the handler raises an exception itself, that exception will then propagate to its nearest enclosing exception hander.

The next five rules model heap reductions. Allocation creates a heap, while (!) and (:=) read and write from the a heap. Through the R context, these always operate on the nearest enclosing heap since R does not contain  $\operatorname{hp} \varphi$ . e or  $\operatorname{run} e$  expressions. The rules (LIFT) and (MERGE) let us lift heaps out of expressions to ensure that all references can be bound in the nearest enclosing heap.

The final three rules deal with state isolation through run. We write  $[hp \varphi]$  to denote an optional heap binding (so we really define six rules for state isolation). The first two rules (RUNL) and (RUNC) push a run operation down into a lambda-expression or partial catch expression. The final rule (RUNH) captures the essence of state isolation and reduces to a new value (or exception) discarding the heap  $\varphi$ .

The side condition frv(*w*)6∩ dom(ϕ) is necessary to ensure well-formedness where a reference should not 'escape' its binding.

Using the reduction rules, we can now define an evaluation function. Using the evaluation context *E* defined in Figure [6,](#page-14-0) we define *E*[*e*] 7−→ *E*[*e* ′ ] iff *e* −→ *e* ′ . The evaluation context ensures strict semantics where only the leftmost- outermost reduction is applicable in an expression. We define the relation 7−→→ as the reflexive and transtive closure of 7−→. We can show that 7−→→ is a function even though we need a simple diamond theorem since the order in which (LIFT) and (MERGE) reductions happen is not fixed [\[44\]](#page-23-2).

The final results, or answers *a*, that expressions evaluate to, are either values *v*, exceptions throw*c*, heap bound values hpϕ.*v* or heap bound exceptions hpϕ.throw*c* (as defined in Figure [4\)](#page-13-0).

Our modeling of the heap is sligthly unconventional. Usually, a heap is defined either as a parameter to the semantics, or always scoped on the outside. This has the advantage that one doesn't need operations like (MERGE) and (LIFT). However, for us it is important that the run operation can completely discard the heap which is hard to do in the conventional approach. In particular, in Section [6](#page-18-0) we want to state the *purity* Theorem [3](#page-18-0) that says that if Γ ⊢ *e* : <sup>τ</sup> | <sup>ε</sup> where *st*h*h*i 6∈ <sup>ε</sup> then we never have *e*7−→→ hpϕ.*v*. Such theorem is difficult to state if we modeled the heap more conventionally.

## **5. Semantic soundness**

We now show that well-typed programs cannot go 'wrong'. Our proof closely follows the subject reduction proofs of Wright and Felleisen [\[44\]](#page-23-2). Our main theorem is:

```
Theorem 1. (Semantic soundness)
```

```
If · ⊢ e : τ | ε then either e ⇑ or e 7−→→ a where · ⊢ a : τ | ε.
```

where we use the notation *e* ⇑ for a never ending reduction. The proof of this theorem consists of showing two main lemmas:

- Show that reduction in the operational semantics preserves well-typing (called subject reduction).
- Show that *faulty* expressions are not typeable.

If programs are closed and well-typed, we know from subject reduction that we can only reduce to welltyped terms, which can be either faulty, an answer, or an expression containing a further redex. Since faulty expressions are not typeable it must be that evaluation either produces a well-typed answer or diverges. Often, proofs of soundness are carried out using *progress* instead of *faulty* expressions but it turns out that for proving the soundness of state isolation, our current approach works better.

### <span id="page-15-0"></span>**5.1. Subject reduction**

The subject reduction theorem states that a well-typed term remains well-typed under reduction:

```
Lemma 1. (Subject reduction)
```

```
If Γ ⊢ e1 : τ | ε and e1 −→ e2 then Γ ⊢ e2 : τ | ε.
```

To show that subject reduction holds, we need to establish various lemmas. Two particularly important lemmas are the substitution and extension lemmas:

```
Lemma 2. (Substitution)
```

```
If Γ,x : ∀α.τ ⊢ e : τ
                      ′
                        | ε where x 6∈ dom(Γ), Γ ⊢ v : τ | hi, and α 6∩ ftv(Γ), then Γ ⊢ [x 7→ v]e : τ
                                                                                                          ′
                                                                                                            | ε.
```

### **Lemma 3.** (*Extension*)

```
If Γ ⊢ e : τ | ε and for all x ∈ fv(e) we have Γ(x) = Γ
                                                          ′
                                                           (x), then Γ
                                                                       ′ ⊢ e : τ | ε.
```

The proofs of these lemmas from [44] carry over directly to our system. However, to show subject reduction, we require an extra lemma to reason about state effects.

**Lemma 4.** (Stateful effects)

If  $\Gamma \vdash e : \tau \mid \langle st\langle h \rangle \mid \varepsilon \rangle$  and  $\Gamma \vdash R[e] : \tau' \mid \varepsilon'$  then  $st\langle h \rangle \in \varepsilon'$ .

The above lemma essentially states that a stateful effect cannot be discarded in an *R* context. Later we will generalize this lemma to arbitrary contexts and effects but for subject reduction this lemma is strong enough.

**Proof**. (Lemma 4) We proceed by induction on the structure of *R*:

**Case** R = []: By definition  $st\langle h \rangle \in \langle st\langle h \rangle | \varepsilon \rangle$ .

Case  $R = R'e_2$ : We have  $\Gamma \vdash (R'[e])e_2 : \tau' \mid \varepsilon'$  and by (APP) we have  $\Gamma \vdash R'[e] : \tau_2 \to \varepsilon' \tau' \mid \varepsilon'$ . By induction,  $st\langle h \rangle \in \varepsilon'$ .

Case R = vR': Similar to previous case.

Case  $R = \text{let } x = R' \text{ in } e_2$ : By (LET) we have  $\Gamma \vdash R'[e] : \tau_1 \mid \langle \rangle$  but that contradicts our assumption.

**Case**  $R = \operatorname{catch} R' e_2$ : By (CATCH) we have  $\Gamma \vdash \operatorname{catch} R'[e] e_2 : \tau' \mid \varepsilon'$  where  $\Gamma \vdash R'[e] : \tau' \mid \langle exn \mid \varepsilon' \rangle$ . By induction  $st\langle h \rangle \in \langle exn \mid \varepsilon' \rangle$  which implies that  $st\langle h \rangle \in \varepsilon'$ .

Before proving subject reduction we need one more type rule on our internal language. The (EXTEND) rule states that we can always assume a stateful effect for an expression:

(ST-EXTEND) 
$$\frac{\Gamma \vdash e : \tau \mid \varepsilon}{\Gamma \vdash e : \tau \mid \langle st \langle h \rangle \mid \varepsilon \rangle}$$

Now we are ready to prove the subject reduction theorem:

**Proof.** (Lemma 1) We prove this by induction on the reduction rules of  $\longrightarrow$ . We will not repeat all cases here and refer to [44], but instead concentrate on the interesting cases, especially with regard to state isolation.

**Case** let x = v in  $e \longrightarrow [x \mapsto v]e$ : From (LET) we have  $\Gamma \vdash v : \tau' \mid \langle \rangle$  and  $\Gamma, x : \text{gen}(\Gamma, \tau') \vdash e : \tau \mid \varepsilon$ . By definition,  $\text{gen}(\Gamma, \tau') = \forall \overline{\alpha} . \tau'$  where  $\overline{\alpha} \notin \text{ftv}(\Gamma)$  and by Lemma 2 we have  $\Gamma \vdash [x \mapsto v]e : \tau \mid \varepsilon$ .

Case  $R[hp \varphi, e] \longrightarrow hp \varphi, R[e]$ : This is case is proven by induction over the structure of R:

**case** R = []: Does not apply due to the side condition on  $\longrightarrow$ .

case R = R'e': Then  $\Gamma \vdash R'[\operatorname{hp} \varphi.e]e' : \tau \mid \varepsilon$  and by (APP) we have  $\Gamma \vdash R'[\operatorname{hp} \varphi.e] : \tau_2 \to \varepsilon \tau \mid \varepsilon$  (1) and  $\Gamma \vdash e' : \tau_2 \mid \varepsilon$  (2). By the induction hypothesis and (1), we have  $\Gamma \vdash \operatorname{hp} \varphi.R'[e] : \tau_2 \to \varepsilon \tau \mid \varepsilon$ . Then by (HEAP) we know  $\Gamma, \overline{\varphi}_h \vdash v_j : \tau_j \mid \langle \rangle$  (3) and  $\Gamma, \overline{\varphi}_h \vdash R'[e] : \tau_2 \to \varepsilon \tau \mid \varepsilon$  (4) where  $\varphi = \langle r_1 \mapsto v_1, ..., r_n \mapsto v_n \rangle$ . Since  $r_1, ..., r_n \notin \operatorname{fv}(e')$  we can use (2) and 3 to conclude  $\Gamma, \overline{\varphi} \vdash e' : \tau_2 \mid \varepsilon$  (5). Using (APP) with (4) and (5), we have  $\Gamma, \overline{\varphi} \vdash R'[e]e' : \tau \mid \varepsilon$  where we can use (HEAP) with (3) to conclude  $\Gamma \vdash \operatorname{hp} \varphi.R'[e]e' : \tau \mid \varepsilon$ .

case R = vR': Similar to the previous case.

case R = let x = R' in e': If this is well-typed, then by rule (LET) we must have  $\Gamma \vdash R'[\text{hp } \varphi.e] : \tau' \mid \langle \rangle$ . However, due to Lemma 4 and (HEAP), we have  $st\langle h \rangle \in \langle \rangle$  which is a contradiction. Note that this case is essential, as it prevents generalization of stateful references. For ML, this is also the tricky proof case that only works if one defines special 'imperative type variables' [44] or the value restriction. In our case the effect system ensures safety.

Case run ( $[hp \varphi] \lambda x.e$ )  $\longrightarrow \lambda x.$  run ( $[hp \varphi] e$ ): By rule (RUN) and (HEAP) we have that  $\Gamma \vdash \lambda x.e$ :  $\tau \mid \langle st \langle h \rangle \mid \varepsilon \rangle$  where  $h \notin \mathsf{ftv}(\Gamma, \tau, \varepsilon)$  (1). Applying (LAM) gives  $\Gamma, x : \tau_1 \vdash e : \tau_2 \mid \varepsilon_2$  with  $\tau = \tau_1 \to \varepsilon_2 \tau_2$ . Using (ST-EXTEND) we can also derive  $\Gamma, x : \tau_1 \vdash e : \tau_2 \mid \langle st \langle h \rangle \mid \varepsilon_2 \rangle$ . Due to (1) and  $h \notin \tau_1$ , we can apply (RUN) and (HEAP) again to infer  $\Gamma, x : \tau_1 \vdash \mathsf{run}([hp \varphi] e) : \tau_2 \mid \varepsilon_2$  and finally (LAM) again to conclude

```
\Gamma \vdash \lambda x. (\operatorname{run}([\operatorname{hp} \varphi.]e)) : \tau \mid \varepsilon.
```

Case run ( $[hp \varphi]$  catch  $e) \longrightarrow catch (run ([hp \varphi] e))$ : Similar to the previous case.

Case run ( $[hp \varphi] w$ )  $\longrightarrow w$  with frv(w)  $\not\cap$  dom( $\varphi$ ) (1): By rule (RUN) and (HEAP) we have that  $\Gamma, \overline{\varphi}_h \vdash w$ :  $\tau \mid \langle st \langle h \rangle \mid \varepsilon \rangle$  where  $h \not\in$  ftv( $\Gamma, \tau, \varepsilon$ ) (2). By (1) it must also be that  $\Gamma \vdash w : \tau \mid \langle st \langle h \rangle \mid \varepsilon \rangle$  (3) (this follows directly if there was no heap binding  $hp \varphi$ .). We proceed over the structure of w:

**case**  $w = \operatorname{throw} c$ : Then by (3) we have  $\Gamma \vdash \operatorname{throw} c : \tau \mid \langle st \langle h \rangle \mid \varepsilon \rangle$ , but also  $\Gamma \vdash \operatorname{throw} c : \tau \mid \varepsilon$  since we can choose the result effect freely in (THROW).

**case** w = r: By (VAR) and (3), we have  $\Gamma \vdash r : ref \langle h', \tau' \rangle \mid \langle st \langle h \rangle \mid \varepsilon \rangle$ . where  $h \neq h'$  satisfying (2). Since the result effect is free in (VAR), we can also derive  $\Gamma \vdash r : ref \langle h', \tau' \rangle \mid \varepsilon$ 

case w = (r :=): As the previous case.

case w = x: By (VAR) and (3), we have  $\Gamma \vdash x : \tau \mid \langle st \langle h \rangle \mid \varepsilon \rangle$  but in (VAR) the result effect is free, so we can also derive  $\Gamma \vdash x : \tau \mid \varepsilon$ .

case other: Similarly.

#### <span id="page-17-0"></span>**5.2.** Faulty expressions

The main purpose of type checking is of course to guarantee that certain bad expressions cannot occur. Apart from the usual errors, like adding a number to a string, we particularly would like to avoid state errors. There are two aspects to this. One of them is notorious where polymorphic types in combination with state can be unsound (which is not the case in our system because of Lemma 1). But in addition, we would like to show that in our system it is not possible to read or write to locations outside the local heap (encapsulated by run), nor is it possible to let local references escape. To make this precise, the *faulty* expressions are defined as:

- Undefined: cv where  $\delta(c,v)$  is not defined.
- Escaping read: run (hp  $\varphi$ . R[!r]) where  $r \notin \text{dom}(\varphi)$ .
- Escaping write: run (hp  $\varphi$ . R[r := v]) where  $r \notin \text{dom}(\varphi)$ .
- Escaping reference: run (hp  $\varphi$ . w) where frv(w)  $\cap$  dom( $\varphi$ )  $\neq \varnothing$ .
- Not a function: *ve* where *v* is not a constant or lambda expression.
- <span id="page-17-1"></span>• Not a reference: v or v := e where v is not a reference.
- Not an exception: throw c where c is not the unit value.

### **Lemma 5.** (Faulty expressions are untypeable)

If an expression e is faulty, it cannot be typed, i.e. there exists no  $\Gamma$ ,  $\tau$ , and  $\varepsilon$  such that  $\Gamma \vdash e : \tau \mid \varepsilon$ .

In the following proof, especially the case for escaping state is interesting. To our knowledge, this is the first proof of the safety of run in a strict setting (and in combination with other effects like exceptions).

**Proof**. (Lemma 5) Each faulty expression is handled separately. We show here the interesting cases for escaping reads, writes, and references:

Case run (hp  $\varphi$ . R[!r]) with  $r \notin \text{dom}(\varphi)$  (1): To be typed in a context  $\Gamma$  we apply (RUN) and (HEAP) and need to show  $\Gamma, \overline{\varphi}_h \vdash R[!r] : \tau \mid \langle st \langle h \rangle \mid \varepsilon \rangle$  (2), where  $h \notin \text{ftv}(\Gamma, \tau, \varepsilon)$  (3). For R[!r] to be well-typed, we also need  $\Gamma, \overline{\varphi}_h \vdash !r : \tau' \mid \langle st \langle h' \rangle \mid \varepsilon' \rangle$  (4) where  $\Gamma, \overline{\varphi}_h \vdash r : ref \langle h', \tau' \rangle \mid \langle st \langle h' \rangle \mid \varepsilon' \rangle$  (5). From Lemma 4, (4), and (2), it must be that h' = h (6). But since  $r \notin \text{dom}(\varphi)$  (1), it follows by (5) and (6), that  $\Gamma \vdash r : ref \langle h, \tau' \rangle \mid \langle st \langle h \rangle \mid \varepsilon' \rangle$ . But that means  $h \in \text{ftv}(\Gamma)$  contradicting (3).

Case run (hp  $\varphi$ . R[(r :=)]) with  $r \notin \text{dom}(\varphi)$ : Similar to the previous case.

Case run (hp  $\varphi$ . w) where frv(w)  $\cap$  dom( $\varphi$ )  $\neq \varnothing$  (1) To be typed in a context  $\Gamma$  we need to show by (HEAP) and (RUN) that  $\Gamma$ ,  $\overline{\varphi}_h \vdash w : \tau \mid \langle st \langle h \rangle \mid \varepsilon \rangle$  where  $h \not\in \mathsf{ftv}(\Gamma, \tau, \varepsilon)$  (2). If  $w = \mathsf{throw}\, c$  then by (THROW) the type of c is () and thus c is the unit constant. But  $\mathsf{frv}(()) = \varnothing$  contradicting our assumption. Otherwise,

w = b and cannot contain an arbitrary e. Since  $frv(w) \neq \emptyset$  (1), it must be that w is either one of r or (r :=) with  $r \in dom(\varphi)$ . To be well-typed,  $\Gamma, \overline{\varphi}_h \vdash r : ref\langle h, \tau' \rangle \mid \varepsilon'$  must hold. However, the possible types for r and (r :=) are  $ref\langle h, \tau' \rangle$  and  $\tau' \to st\langle h \rangle$  () and in both cases  $h \in ftv(\tau)$  which contradicts (2).

### <span id="page-18-0"></span>6. Effectful semantics

Up till now, we have used the effect types to good effect and showed that our system is semantically sound, even though state and polymorphic types are notoriously tricky to combine. Moreover, we showed that local state isolation through run is sound and statically prevents references from escaping.

But the true power of the effect system is really to enable more reasoning about the behavior of a program at a higher level. In particular, the absence of certain effects determines the absence of certain answers. For example, if the exception effect is not inferred, then evaluating the program will never produce an answer of the form throw c or p0 throw p1. It would not be entirely correct to say that such program never throws an exception: indeed, a local catch block can handle such exceptions. We can state the exception property formally as:

#### **Theorem 2.** (Exceptions)

If  $\Gamma \vdash e : \tau \mid \varepsilon$  where  $exn \notin \varepsilon$  then either  $e \uparrow \uparrow$ ,  $e \mapsto v$  or  $e \mapsto hp \varphi \cdot v$ .

**Proof**. (Theorem 2) By contradiction over the result terms:

Case  $e \mapsto$  throw c: By subject reduction (Lemma 1), it must be  $\Gamma \vdash$  throw  $c : \tau \mid \varepsilon$ . Using the type rule for throw with (APP), it must be the case that  $\varepsilon \equiv \langle exn \mid \varepsilon' \rangle$  contradicting our assumption.

Case  $e \mapsto hp \varphi$ . throw c: Similar to the previous case.

Similarly to the exception case, we can state such theorem over heap effects too. In particular, if the  $st\langle h\rangle$  effect is absent, then evaluation will not produce an answer that contains a heap, i.e.  $\operatorname{hp} \varphi.w$ . Again, it would not be right to say that the program itself never performs any stateful operations the state can be encapsulated inside a run construct and its stateful behavior is not observable from outside. Formally, we can state this as:

#### **Theorem 3.** (*State*)

Iff  $\Gamma \vdash e : \tau \mid \varepsilon$  where  $st\langle h \rangle \notin \varepsilon$  then either  $e \uparrow \uparrow$ ,  $e \longmapsto v$  or  $e \longmapsto$  throw c.

**Proof.** (Theorem 3) We prove by contradiction over the result terms:

Case  $e \mapsto hp \varphi . v$ : By subject reduction (Lemma 1), it must be  $\Gamma \vdash hp \varphi . v : \tau \mid \varepsilon$ . Using (HEAP), it must be the case that  $\varepsilon \equiv \langle st \langle h \rangle \mid \varepsilon' \rangle$  contradicting our assumption.

Case  $e \mapsto hp \varphi$ . throw c: Similar to the previous case.

Finally, our most powerful theorem is about the divergence effect; in particular, if the divergent effect is absent, then evaluation is guaranteed to terminate!

#### **Theorem 4.** (Divergence)

If  $\Gamma \vdash e : \tau \mid \varepsilon$  where  $div \notin \varepsilon$  then  $e \mapsto a$ .

The proof of the divergence theorem (Theorem 4) is more complicated as we cannot use subject reduction to show this by contradiction. Instead, we need to do this proof using induction over logical relations [9].

In our case, we say that if  $\cdot \vdash e : \tau \mid \varepsilon$ , then e is in the set  $\mathscr{R}(\tau \mid \varepsilon)$ , "the reducible terms of type  $\tau$  with effect  $\varepsilon$ ", if  $div \notin \varepsilon$  and (1) when  $\tau$  is a non-arrow type, if e halts, and (2) when  $\tau = \tau_1 \to \varepsilon_2 \tau_2$ , if e halts and if for all  $e_1 \in \mathscr{R}(\tau_1 \mid \varepsilon)$ , we have that  $e e_1 \in \mathscr{R}(\tau_2 \mid \varepsilon_2)$ .

The proof of Theorem 4 is a standard result [9] and is a corollary from the following two main lemmas:

**Lemma 6.** ( $\mathscr{R}$  is preserved by reduction) Iff  $\cdot \vdash e : \tau \mid \varepsilon, e \in \mathscr{R}(\tau \mid \varepsilon)$ , and  $e \longmapsto e'$ , then also  $e' \in \mathscr{R}(\tau \mid \varepsilon)$ .

**Lemma 7.** (A well-typed term is in  $\mathscr{R}$ ) If  $\cdot \vdash e : \tau \mid \varepsilon$  and  $div \notin \varepsilon$ , then  $e \in \mathscr{R}(\varepsilon \mid \tau)$ .

**Proof.** (Lemma 6) This is shown by induction over the type  $\tau$ . For atomic types, this holds by definition. For arrow types,  $\tau_1 \to \varepsilon_2 \ \tau_2$  we must show for a given  $e_1 \in \mathcal{R}(\tau_1 \mid \varepsilon)$  that if  $ee_1 \in \mathcal{R}(\tau_2 \mid \varepsilon_2)$ , then also  $e'e_1 \in \mathcal{R}(\tau_2 \mid \varepsilon_2)$  (and the other direction). By (APP), it must be  $\varepsilon_2 = \varepsilon$  (1). We can now proceed over the structure of reductions on  $ee_1$ :

Case  $(!)e_1$ : In this case, since (READ) has a *div* effect, we have by (1) that  $div \in \varepsilon$  contradicting our assumption. Note that if we would have cheated and not include div in the type, we would have gotten a reduction to some v which we could not show to be strongly normalizing, and thus if it is an element of  $\mathcal{R}(\tau_2 | \varepsilon_2)$ .

Case fix  $\varepsilon_1$ : As the previous case.

Case  $(\lambda x. e_2)e_1$ : In this case, we can reduce to  $e'e_1$ , and by the induction hypothesis  $e'e_1 \in \mathcal{R}(\tau | \varepsilon_2)$  since  $\tau_2$  is smaller.

**Proof.** (Lemma 7) This is proven over the structure of the type derivation. However, as usual, we need to strengthen our induction hypothesis to include the environment. We extend  $\mathcal{R}$  over environments to be a set of substitutions:

$$\mathscr{R}(\Gamma) = \{\theta \mid \mathsf{dom}(\Gamma) = \mathsf{dom}(\theta) \land \forall (x : \tau \in \Gamma). \, \theta x \in \mathscr{R}(\tau \mid \langle \rangle)\}$$

where we assume a monomorphic environment for simplicity but we can extend this easily to a (first-order) polymorphic setting. Our strengthened lemma we use for our proof is:

if 
$$\Gamma \vdash e : \tau \mid \varepsilon \land \theta \in \mathcal{R}(\Gamma) \land div \notin \varepsilon$$
 then  $\theta e \in \mathcal{R}(\tau \mid \varepsilon)$ 

The induction is standard, and we show only some sample cases:

Case (FIX): Since the result effect is free, we can choose any  $\varepsilon$  such that  $div \notin \varepsilon$ . Indeed, just an occurrence of fix is ok – only an application may diverge.

Case (APP): By the induction hypothesis and (APP) we have  $\theta e_1 \in \mathcal{R}(\tau_2 \to \varepsilon \tau \mid \varepsilon)$  and  $\theta e_2 \in \mathcal{R}(\tau_2 \mid \varepsilon)$ . By definition of  $\mathcal{R}(\tau_2 \to \varepsilon \tau \mid \varepsilon)$ ,  $\theta e_1 \theta e_2 \in \mathcal{R}(\tau_2 \mid \varepsilon)$  and therefore  $\theta(e_1 e_2) \in \mathcal{R}(\tau_2 \mid \varepsilon)$ . Note that the induction hypothesis ensures that  $div \notin \varepsilon$  and therefore we cannot apply a potentially divergent function (like fix or (!)).

Case other: Standard, except that for effect elimination rules, we need to show that div is not eliminated.

Contrast the results of this section to many other effect systems [25, 33] that just use effect types as syntactic 'labels'. In our case the theorems of this section are truly significant as they show there is a deep correspondence between the effect types and the dynamic semantics which eventually enables us to reason about our programs much more effectively.

### 7. Related work

A main contribution of this paper is showing that our notion of mutable state is sound, in particular the combination of mutable state and polymorphic let- bindings is tricky as shown by Tofte [39] for the ML language. Later, variants of the ML value restriction are studied by Leroy [21].

Safe state encapsulation using a lazy state monad was first proven formally by Launchbury and Sabry [16]. Their formalization is quite different though from ours and applies to a lazy store in a monadic setting. In particular, in their formalization there is no separate heap binding, but heaps are

always bound at the outer *run*. We tried this, but it proved difficult in our setting; for example, it is hard to state the stateful lemma since answers would never contain an explicit heap. Very similar to our state encapsulation is region inference [\[40\]](#page-22-15). Our *run* operation essentially delimits a heap region. Regions are values though, and we can for example not access references in several regions at once.

Independently of our work, Lindley and Cheney [\[23\]](#page-22-6) also used row polymorphism for effect types. Their approach is based on presence/absence flags [\[32\]](#page-22-10) to give effect types to database operations in the context of the Links web programming language. The main effects of the database operations are *wild*,*tame*, and*hear*, for arbitrary effects including divergence, pure queries, and asynchronous messages respectively. They report on practical experience exposing effect types to the programmer and discuss various syntax forms to easily denote effect types.

The problems with arbitrary effects have been widely recognized, and there is a large body of work studying how to delimit the scope of effects. There have been many effect typing disciplines proposed. Early work is by Gifford and Lucassen [\[8,](#page-21-1) [24\]](#page-22-0) which was later extended by Talpin [\[37\]](#page-22-16) and others [\[28,](#page-22-2) [36\]](#page-22-4). These systems are closely related since they describe polymorphic effect systems and use type constraints to give principal types. The system described by Nielson *et al.* [\[28\]](#page-22-2) also requires the effects to form a complete lattice with meets and joins.

Java contains a simple effect system where each method is labeled with the exceptions it might raise [\[10\]](#page-21-12). A system for finding uncaught exceptions was developed for ML by Pessaux *et al.* [\[29\]](#page-22-17). A more powerful system for tracking effects was developed by Benton [\[2\]](#page-21-0) who also studies the semantics of such effect systems [\[3\]](#page-21-13). Recent work on effects in Scala [\[33\]](#page-22-3) shows how even a restricted form of polymorphic effect types can track effects for many programs in practice.

Tolmach [\[41\]](#page-22-18) describes an effect analysis for ML in terms of effect monads, namely *Total*, *Partial*, *Divergent* and *ST*. This is system is not polymorphic though and meant more for internal compiler analysis. In the context proof systems there has been work to show absence of observable side effects for object-oriented programming languages, for example by Naumann [\[27\]](#page-22-19).

Marino *et al.* recently produced a generic type-and-effect system [\[25\]](#page-22-1). This system uses privilege checking to describe analytical effect systems. For example, an effect system could use try-catch statements to grant the *canThrow* privilege inside try blocks. *throw* statements are then only permitted when this privilege is present. Their system is very general and can express many properties but has no semantics on its own. For example, it would be sound for the effect system to have "+" grant the *canThrow* privilege to its arguments, and one has to do an additional proof to show that the effects in these systems actually correspond to an intended meaning.

Wadler and Thiemann showed the close relation between effect systems and monads [\[42\]](#page-23-0) and showed how any effect system can be translated to a monadic version. For our particular system though a monadic translation is quite involved due to polymorphic effects; essentially we need dependently typed operations and we leave a proper monadic semantics for future work.

Recently, *effect handlers* are proposed to program with effects [\[4,](#page-21-14) [14,](#page-21-15) [15\]](#page-21-16). In this work, computational effects are modeled as operations of an algebraic theory. Even though algebraic effects are subsumed by monads, they can be combined more easily and the specification of handlers offers new ways of programming. This work is quite different than what we described in this paper since we only considered effects that are intrinsic to the language while effect handlers deal specifically with 'user-defined' effects. However, we are currently working on integrating user-defined effects in Koka using effect handlers, and investigating how this can work well with the current effect type system.

## **References**

- <span id="page-21-8"></span><span id="page-21-0"></span>[1] Andreas Abel (1998): *Foetus – A Termination Checker for Simple Functional Programs*. Unpublished note.
- [2] Nick Benton & Peter Buchlovsky (2007): *Semantics of an effect analysis for exceptions*. In: TLDI '07: Proceedings of the <sup>2007</sup> ACM SIGPLAN international workshop on Types in languages design and implementation, pp. 15–26, doi[:10.1145/1190315.1190320.](http://dx.doi.org/10.1145/1190315.1190320)
- <span id="page-21-13"></span>[3] Nick Benton, Andrew Kennedy, Lennart Beringer & Martin Hofmann (2007): *Relational semantics for effectbased program transformations with dynamic allocation*. In: PPDP '07: Proc. of the 9th ACM SIGPLAN int. conf. on Principles and Practice of Declarative Prog., pp. 87–96, doi[:10.1145/1273920.1273932.](http://dx.doi.org/10.1145/1273920.1273932)
- <span id="page-21-14"></span>[4] Edwin Brady (2013): *Programming and Reasoning with Algebraic Effects and Dependent Types*. In: Proceedings of the 18th ACM SIGPLAN International Conference on Functional Programming, ICFP '13, ACM, New York, NY, USA, pp. 133–144, doi[:10.1145/2500365.2500581.](http://dx.doi.org/10.1145/2500365.2500581)
- <span id="page-21-18"></span>[5] Luis Damas & Robin Milner (1982): *Principal type-schemes for functional programs*. In: 9th ACM symp. on Principles of Programming Languages (POPL'82), pp. 207–212, doi[:10.1145/582153.582176.](http://dx.doi.org/10.1145/582153.582176)
- <span id="page-21-6"></span>[6] Jean-Christophe Filliˆatre (2008): *A Functional Implementation of the Garsia–wachs Algorithm: (Functional Pearl)*. In: Proceedings of the <sup>2008</sup> ACM SIGPLAN Workshop on ML, ML '08, ACM, New York, NY, USA, pp. 91–96, doi[:10.1145/1411304.1411317.](http://dx.doi.org/10.1145/1411304.1411317)
- <span id="page-21-4"></span>[7] Ben R. Gaster & Mark P. Jones (1996): *A Polymorphic Type System for Extensible Records and Variants*. Technical Report NOTTCS-TR-96-3, University of Nottingham.
- <span id="page-21-1"></span>[8] David K. Gifford & John M. Lucassen (1986): *Integrating functional and imperative programming*. In: LFP '86: Proceedings of the <sup>1986</sup> ACM conference on LISP and functional programming, pp. 28–38, doi[:10.1145/319838.319848.](http://dx.doi.org/10.1145/319838.319848)
- <span id="page-21-12"></span><span id="page-21-11"></span>[9] Jean-Yves Girard, Paul Taylor & Yves Lafont (1989): *Proofs and types*. Cambridge University Press.
- <span id="page-21-17"></span>[10] James Gosling, Bill Joy & Guy Steele (1996): *The Java Language Specification*. Addison-Wesley.
- [11] J.R. Hindley (1969): *The principal type scheme of an object in combinatory logic*. Trans. of the American Mathematical Society 146, pp. 29–60, doi[:10.2307/1995158.](http://dx.doi.org/10.2307/1995158)
- <span id="page-21-9"></span>[12] Mark P. Jones (1992): *A theory of qualified types*. In: 4th. European Symposium on Programming (ESOP'92), Lecture Notes in Computer Science 582, Springer-Verlag, pp. 287–306, doi[:10.1007/3-540-55253-7](http://dx.doi.org/10.1007/3-540-55253-7\protect _17) 17.
- <span id="page-21-19"></span>[13] Mark P. Jones (1995): *A system of constructor classes: overloading and implicit higher-order polymorphism*. Journal of Functional Programming 5(1), pp. 1–35, doi[:10.1145/165180.165190.](http://dx.doi.org/10.1145/165180.165190)
- <span id="page-21-15"></span>[14] Ohad Kammar, Sam Lindley & Nicolas Oury (2013): *Handlers in Action*. In: Proceedings of the 18th ACM SIGPLAN International Conference on Functional Programming, ICFP '13, ACM, New York, NY, USA, pp. 145–158, doi[:10.1145/2500365.2500590.](http://dx.doi.org/10.1145/2500365.2500590)
- <span id="page-21-16"></span>[15] Ohad Kammar & Gordon D. Plotkin (2012): *Algebraic Foundations for Effect-dependent Optimisations*. In: Proceedings of the 39th Annual ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages, POPL '12, ACM, New York, NY, USA, pp. 349–360, doi[:10.1145/2103656.2103698.](http://dx.doi.org/10.1145/2103656.2103698)
- <span id="page-21-7"></span>[16] John Launchbury & Amr Sabry (1997): *Monadic State: Axiomatization and Type Safety*. In: ICFP'97, pp. 227–238, doi[:10.1145/258948.258970.](http://dx.doi.org/10.1145/258948.258970)
- <span id="page-21-5"></span>[17] Daan Leijen (2005): *Extensible records with scoped labels*. In: In: Proceedings of the <sup>2005</sup> Symposium on Trends in Functional Programming, pp. 297–312.
- <span id="page-21-3"></span><span id="page-21-2"></span>[18] Daan Leijen (2012): *Try Koka online*. <http://rise4fun.com/koka/tutorial> and [http://koka.codeplex.com.](http://koka.codeplex.com)
- [19] Daan Leijen (2013): *Koka: Programming with Row-Polymorphic Effect Types*. Technical Report MSR-TR-2013-79, Microsoft Research.
- <span id="page-21-10"></span>[20] Daan Leijen (2014): *Madoko: A Scholarly Markdown processor*. [http://madoko.codeplex.com.](http://madoko.codeplex.com)

- <span id="page-22-13"></span>[21] Xavier Leroy (1993): *Polymorphism by name for references and continuations*. In: POPL '93: Proc. of the 20th ACM SIGPLAN-SIGACT symposium on Principles of programming languages, pp. 220–231, doi[:10.1145/158511.158632.](http://dx.doi.org/10.1145/158511.158632)
- <span id="page-22-14"></span>[22] Mark Lillibridge (1999): *Unchecked Exceptions Can Be Strictly More Powerful Than Call/CC*. Higher-Order and Symbolic Computation 12(1), pp. 75–104, doi[:10.1023/A:1010020917337.](http://dx.doi.org/10.1023/A:1010020917337)
- <span id="page-22-6"></span>[23] Sam Lindley & James Cheney (2012): *Row-based effect types for database integration*. In: TLDI'12, pp. 91–102, doi[:10.1145/2103786.2103798.](http://dx.doi.org/10.1145/2103786.2103798)
- <span id="page-22-1"></span><span id="page-22-0"></span>[24] J. M. Lucassen & D. K. Gifford (1988): *Polymorphic effect systems*. In: POPL '88, pp. 47–57, doi[:10.1145/73560.73564s.](http://dx.doi.org/10.1145/73560.73564s)
- [25] Daniel Marino & Todd Millstein (2009): *A generic type-and-effect system*. In: TLDI '09: Proceedings of the 4th international workshop on Types in language design and implementation, pp. 39–50, doi[:10.1145/1481861.1481868.](http://dx.doi.org/10.1145/1481861.1481868)
- <span id="page-22-20"></span>[26] Robin Milner (1978): *A theory of type polymorphism in programming*. Journal of Computer and System Sciences 17, pp. 248–375, doi[:10.1016/0022-007890014-4.](http://dx.doi.org/10.1016/0022-007890014-4)
- <span id="page-22-19"></span>[27] David A. Naumann (2007): *Observational purity and encapsulation*. Theor. Comput. Sci. 376(3), pp. 205–224, doi[:10.1007/978-3-540-31984-9](http://dx.doi.org/10.1007/978-3-540-31984-9\protect _15) 15.
- <span id="page-22-2"></span>[28] Hanne Riis Nielson, Flemming Nielson & Torben Amtoft (1997): *Polymorphic Subtyping for Effect Analysis: The Static Semantics*. In: Selected papers from the 5th LOMAPS Workshop on Analysis and Verification of Multiple-Agent Languages, pp. 141–171, doi[:10.1007/3-540-62503-8](http://dx.doi.org/10.1007/3-540-62503-8\protect _8) 8.
- <span id="page-22-17"></span>[29] Franc¸ois Pessaux & Xavier Leroy (1999): *Type-based analysis of uncaught exceptions*. In: POPL '99, pp. 276–290, doi[:10.1145/292540.292565.](http://dx.doi.org/10.1145/292540.292565)
- <span id="page-22-11"></span>[30] Simon L Peyton Jones & John Launchbury (1995): *State in Haskell*. Lisp and Symbolic Comp. 8(4), pp. 293–341, doi[:10.1007/BF01018827.](http://dx.doi.org/10.1007/BF01018827)
- <span id="page-22-7"></span>[31] Didier Remy (1994): *Programming Objects with ML-ART, an Extension to ML with Abstract and Record Types*. In: TACS '94: Proc. Int. Conf. on Theoretical Aspects of Computer Software, pp. 321–346, doi[:10.1007/3-540-57887-0](http://dx.doi.org/10.1007/3-540-57887-0\protect _102) 102.
- <span id="page-22-10"></span>[32] Didier R´emy (1994): *Theoretical Aspects of Object-oriented Programming*. chapter Type Inference for Records in Natural Extension of ML, MIT Press, Cambridge, MA, USA, pp. 67–95. Available at [http://dl.acm.org/citation.cfm?id=186677.186689.](http://dl.acm.org/citation.cfm?id=186677.186689)
- <span id="page-22-3"></span>[33] Lukas Rytz, Martin Odersky & Philipp Haller (2012): *Lightweight Polymorphic Effects*. In: Proceedings of the 26th European Conference on Object-Oriented Programming, ECOOP'12, Springer-Verlag, Berlin, Heidelberg, pp. 258–282, doi[:10.1007/978-3-642-31057-7](http://dx.doi.org/10.1007/978-3-642-31057-7\protect _13) 13.
- <span id="page-22-8"></span>[34] Martin Sulzmann (1997): *Designing record systems*. Technical Report YALEU/DCS/RR-1128, Yale University.
- <span id="page-22-9"></span><span id="page-22-4"></span>[35] Martin Sulzmann (1998): *Type systems for records revisited*. Unpublished.
- [36] Jean-Pierre Talpin & Pierre Jouvelot (1994): *The type and effect discipline*. Inf. Comput. 111(2), pp. 245–296, doi[:10.1006/inco.1994.1046.](http://dx.doi.org/10.1006/inco.1994.1046)
- <span id="page-22-16"></span>[37] J.P. Talpin (1993): *Theoretical and practical aspects of type and effect inference*. Ph.D. thesis, Ecole des Mines de Paris and University Paris VI, Paris, France.
- <span id="page-22-5"></span>[38] Ross Tate & Daan Leijen (2010): *Convenient Explicit Effects using Type Inference with Subeffects*. Technical Report MSR-TR-2010-80, Microsoft Research.
- <span id="page-22-12"></span>[39] Mads Tofte (1990): *Type inference for polymorphic references*. Inf. Comput. 89(1), pp. 1–34, doi[:10.1016/0890-5401\(90\)90018-D9](http://dx.doi.org/10.1016/0890-5401(90)0018-D).
- <span id="page-22-15"></span>[40] Mads Tofte & Lars Birkedal (1998): *A region inference algorithm*. ACM Trans. Program. Lang. Syst. 20(4), pp. 724–767, doi[:10.1145/291891.291894.](http://dx.doi.org/10.1145/291891.291894)
- <span id="page-22-18"></span>[41] Andrew P. Tolmach (1998): *Optimizing ML Using a Hierarchy of Monadic Types*. In: TIC '98, pp. 97–115, doi[:10.1007/BFb0055514.](http://dx.doi.org/10.1007/BFb0055514)

- <span id="page-23-0"></span>[42] Philip Wadler & Peter Thiemann (2003): *The marriage of effects and monads*. ACM Trans. Comput. Logic 4(1), pp. 1–32, doi[:10.1145/601775.601776.](http://dx.doi.org/10.1145/601775.601776)
- <span id="page-23-1"></span>[43] Mitchell Wand (1987): *Complete Type Inference for Simple Objects*. In: Proceedings of the 2nd. IEEE Symposium on Logic in Computer Science, pp. 37–44, doi[:10.1109/LICS.1988.5111.](http://dx.doi.org/10.1109/LICS.1988.5111) Corrigendum in LICS'88, page 132.
- <span id="page-23-2"></span>[44] Andrew K. Wright & Matthias Felleisen (1994): *A syntactic approach to type soundness*. Inf. Comput. 115(1), pp. 38–94, doi[:10.1006/inco.1994.1093.](http://dx.doi.org/10.1006/inco.1994.1093)

$$(VAR)_{S} \qquad \frac{\Gamma(x) = \forall \overline{\alpha}. \tau}{\Gamma \vdash_{s} x : [\overline{\alpha} \mapsto \overline{\tau}] \tau \mid \varepsilon}$$

$$\Gamma \vdash_{s} e_{1} : \tau_{1} \mid \langle \rangle \qquad \overline{\alpha} \notin \mathsf{ftv}(\Gamma)$$

$$(LET)_{S} \qquad \frac{\Gamma, x : \forall \overline{\alpha}. \tau_{1} \vdash_{s} e_{2} : \tau_{2} \mid \varepsilon}{\Gamma \vdash_{s} \mathsf{let} x = e_{1} \mathsf{in} e_{2} : \tau_{2} \mid \varepsilon}$$

**Figure 7.** Changed rules for the syntax directed system; Rule (INST) and (GEN) are removed, and all other rules are equivalent to the declarative system (Figure [3\)](#page-10-0)

## **Appendix**

## <span id="page-24-0"></span>**A. Type inference**

As a first step toward type inference, we first present in a syntax directed version of our declarative type rules in Figure [7.](#page-24-0) For this system, the syntax tree completely determines the derivation tree. Effectively, we removed the (INST) and (GEN) rules, and always apply instantiation in the (VAR) rule, and always generalize at let-bindings. This technique is entirely standard [\[11,](#page-21-17) [12,](#page-21-9) [26\]](#page-22-20) and we can show that the syntax directed system is sound and complete with respect to the declarative rules:

**Theorem 5.** (*Soundness of the syntax directed rules*)

When Γ ⊢*<sup>s</sup> e* : <sup>τ</sup> | <sup>ε</sup> then we also have Γ ⊢ *e* : <sup>τ</sup> | <sup>ε</sup>.

**Theorem 6.** (*Completeness of the syntax directed rules*)

When Γ ⊢ *e* : <sup>σ</sup> | <sup>ε</sup> then we also have Γ ⊢ *e* : <sup>τ</sup> | <sup>ε</sup> where <sup>σ</sup> can be instantiated to <sup>τ</sup>.

Both proofs are by straightforward induction using standard techniques as described for example by Jones [\[12\]](#page-21-9).

## <span id="page-24-1"></span>**A.1. The type inference algorithm**

Starting from the syntax directed rules, we can now give a the type inference algorithm for our effect system which is shown in Figure [8.](#page-24-1) Following Jones [\[12\]](#page-21-9) we present the algorithm as natural inference rules of the form <sup>θ</sup>Γ ⊢ *e* : <sup>τ</sup> | <sup>ε</sup> where <sup>θ</sup> is a substitution, Γ the environment, and *e*, <sup>τ</sup>, and <sup>ε</sup>, the expression, its type, and its effect respectively. The rules can be read as an attribute grammar where θ, <sup>τ</sup>, and <sup>ε</sup> are synthesised, and Γ and *e* inherited. An advantage is that this highlights the correspondence between the syntax directed rules and the inference algorithm.

The algorithm uses unification written as <sup>τ</sup><sup>1</sup> ∼ <sup>τ</sup><sup>2</sup> : <sup>θ</sup> which unifies <sup>τ</sup><sup>1</sup> and <sup>τ</sup><sup>2</sup> with a most general substitution <sup>θ</sup> such that θτ<sup>1</sup> = θτ2. %The unification algorithm is standard and effects are unified using standard row unificiation allowing for duplicate label as described by Leijen [\[17\]](#page-21-5). The gen function generalizes a type with respect to an environment and is defined as:

$$\mathrm{gen}(\Gamma,\tau) = \forall (\mathsf{ftv}(\tau) - \mathsf{ftv}(\Gamma)).\,\tau$$

We can prove that the inference algorithm is sound and complete with respect to the syntax directed rules (and by Theorem [5](#page-24-0) and [6](#page-24-0) also sound and complete to the declarative rules):

**Theorem 7.** (*Soundness*)

If <sup>θ</sup>Γ ⊢*<sup>i</sup> e* : <sup>τ</sup> | <sup>ε</sup> then there exists a <sup>θ</sup> ′ such that <sup>θ</sup>Γ ⊢*<sup>s</sup> e* : <sup>τ</sup> ′ | <sup>ε</sup> ′ where <sup>θ</sup> ′ <sup>τ</sup> = <sup>τ</sup> ′ and θ ′ <sup>ε</sup> = <sup>ε</sup> ′ .

$$\begin{array}{ll} \Gamma(x) &= \forall \overline{\alpha}.\,\tau \\ \hline \varnothing \Gamma \vdash_{i} x : [\overline{\alpha} \mapsto \overline{\beta}]\tau \mid \mu \\ \\ (\text{LAM})_{i} & \frac{\theta \Gamma, x : \alpha \vdash_{i} e : \tau_{2} \mid \varepsilon_{2}}{\theta \Gamma \vdash_{i} \lambda x.e : \theta \alpha \rightarrow \varepsilon_{2} \tau_{2} \mid \mu} \\ \\ (\text{APP})_{i} & \frac{\theta_{1} \Gamma \vdash_{i} e_{1} : \tau_{1} \mid \varepsilon_{1} \quad \theta_{2}(\theta_{1} \Gamma) \vdash_{i} e_{2} : \tau_{2} \mid \varepsilon_{2}}{\theta_{2} \tau_{1} \sim (\tau_{2} \rightarrow \varepsilon_{2} \alpha) : \theta_{3} \quad \theta_{3}\theta_{2}\varepsilon_{1} \sim \theta_{3}\varepsilon_{2} : \theta_{4}} \\ \hline \theta_{4}\theta_{3}\theta_{2}\theta_{1}\Gamma \vdash_{i} e_{1} e_{2} : \theta_{4}\theta_{3}\alpha \mid \theta_{4}\theta_{3}\varepsilon_{2} \\ \hline \theta_{1}\Gamma \vdash_{i} e_{1} : \tau_{1} \mid \varepsilon_{1} \quad \varepsilon_{1} \sim \langle \rangle : \theta_{2} \\ \hline \sigma = \text{gen}(\theta_{2}\theta_{1}\Gamma, \theta_{2}\tau_{1}) \\ \hline \theta_{3}(\theta_{2}\theta_{1}\Gamma, x : \sigma) \vdash_{i} e_{2} : \tau \mid \varepsilon \\ \hline \theta_{3}\theta_{2}\theta_{1}\Gamma \vdash_{i} let \quad x = e_{1} in e_{2} : \tau \mid \varepsilon \\ \hline \theta_{1}\Gamma \vdash_{i} e : \tau \mid \varepsilon \quad \varepsilon \sim \langle st \langle \xi \rangle \mid \mu \rangle : \theta_{2} \\ \hline \theta_{2}\xi \in \textit{TypeVar} \quad \theta_{2}\xi \not\in \text{ftv}(\theta_{2}\theta_{1}\Gamma, \theta_{2}\tau, \theta_{2}\mu) \\ \hline \theta_{2}\theta_{1}\Gamma \vdash_{i} \text{run} e : \theta_{2}\tau \mid \theta_{2}\mu \\ \hline \theta_{1}\Gamma \vdash_{i} e_{1} : \tau_{1} \mid \varepsilon_{1} \quad \theta_{2}(\theta_{1}\Gamma) \vdash_{i} e_{2} : \tau_{2} \mid \varepsilon_{2} \\ \theta_{2}\varepsilon_{1} \sim \langle exn \mid \varepsilon_{2} \rangle : \theta_{3} \\ \hline \theta_{3}\tau_{2} \sim () \rightarrow \theta_{3}\varepsilon_{2} \theta_{3}\theta_{2}\tau_{1} : \theta_{4} \\ \hline \theta_{4}\theta_{3}\theta_{2}\theta_{1}\Gamma \vdash \text{catch} e_{1} e_{2} : \theta_{4}\theta_{3}\tau_{2} \mid \theta_{4}\theta_{3}\varepsilon_{2} \\ \hline \end{array}$$

**Figure 8.** Type and effect inference algorithm. Any type variables <sup>α</sup>, µ, ξ , and <sup>α</sup> are considered fresh.

### **Theorem 8.** (*Completeness*)

If <sup>θ</sup>1Γ ⊢*<sup>s</sup> e* : <sup>τ</sup><sup>1</sup> | <sup>ε</sup><sup>1</sup> then <sup>θ</sup>2Γ ⊢*<sup>i</sup> e* : <sup>τ</sup><sup>2</sup> | <sup>ε</sup><sup>2</sup> and there exists a substitution <sup>θ</sup> such that <sup>θ</sup><sup>1</sup> ≈ θθ2, <sup>τ</sup><sup>1</sup> = θτ<sup>2</sup> and <sup>ε</sup><sup>1</sup> = θε2.

Since the inference algorithm is basically just algorithm W [\[5\]](#page-21-18) together with extra unifications for effect types, the proofs of soundness and completeness are entirely standard. The main extended lemma is for the soundness, completeness, and termination of the unification algorithm which now also unifies effect types.

The unification algorithm is shown in Figure [9.](#page-24-1) The algorithm is an almost literal adaption of the unification algorithm for records with scoped labels as described by Leijen [\[17\]](#page-21-5), and the proofs of soundness, completeness, and termination carry over directly.

The first four rules are the standard Robinson unification rules with a slight modification to return only kind-preserving substitutions [\[7,](#page-21-4) [13\]](#page-21-19). The rule (UNI-EFF) unifies effect rows. The operation tl(ε) is defined as:

$$\mathsf{tl}(\langle l_1,...,l_n \mid \mu \rangle) = \mu \\ \mathsf{tl}(\langle l_1,...,l_n \rangle) = \langle \rangle$$

As described in detail in [\[17\]](#page-21-5), the check tl(<sup>ε</sup>1) 6∈ dom(θ)<sup>1</sup> is subtle but necessary to guarantee termination of row unification. The final three rules unify an effect with a specific head. In particular, <sup>ε</sup> ≃ *l* | <sup>ε</sup> ′ : θ

<span id="page-26-0"></span>
$$(\text{UNI-VARL}) \qquad \qquad \alpha \sim \alpha : []$$

$$(\text{UNI-VARL}) \qquad \qquad \frac{\alpha \not\in \text{ftv}(\tau)}{\alpha^k \sim \tau^k : [\alpha \mapsto \tau]}$$

$$(\text{UNI-VARR}) \qquad \qquad \frac{\alpha \not\in \text{ftv}(\tau)}{\tau^k \sim \alpha^k : [\alpha \mapsto \tau]}$$

$$(\text{UNI-CON}) \qquad \frac{\kappa = (\kappa_1, ..., \kappa_n) \to \kappa'}{\epsilon^\kappa \langle \tau_1^{\kappa_1}, ..., \tau_n^{\kappa_n} \rangle \sim \epsilon^\kappa \langle t_1^{\kappa_1}, ..., t_n^{\kappa_n} \rangle : \theta_n ... \theta_1}$$

$$(\text{UNI-EFF}) \qquad \frac{\epsilon_2 \simeq l \mid \epsilon_3 : \theta_1 \quad \text{tl}(\epsilon_1) \not\in \text{dom}(\theta_1)}{\epsilon_1 \epsilon_1 \sim \theta_1 \epsilon_3 : \theta_2}$$

$$(\text{UNI-EFF}) \qquad \frac{\theta_1 \epsilon_1 \sim \theta_1 \epsilon_3 : \theta_2}{\langle l \mid \epsilon_1 \rangle \sim \epsilon_2 : \theta_2 \theta_1}$$

$$(\text{EFF-HEAD}) \qquad \frac{l \equiv l' \quad l \sim l' : \theta}{\langle l' \mid \epsilon \rangle \simeq l \mid \epsilon : \theta}$$

$$(\text{EFF-SWAP}) \qquad \frac{l \not\equiv l' \quad \epsilon \simeq l \mid \epsilon' : \theta}{\langle l' \mid \epsilon \rangle \simeq l \mid \langle l \mid \epsilon' \rangle : \theta}$$

$$(\text{EFF-TAIL}) \qquad \frac{\text{fresh } \mu'}{\mu \simeq l \mid \mu' : [\mu \mapsto \langle l \mid \mu' \rangle]}$$

**Figure 9.** Unification:  $\tau \sim \tau'$ :  $\theta$  unifies two types and returns a substitution  $\theta$ . It uses effect unification  $\varepsilon \simeq l \mid \varepsilon'$ :  $\theta$  which takes an effect  $\varepsilon$  and effect primitive l as input, and returns effect tail  $\varepsilon'$  and a substition  $\theta$ .

states that for a given effect row  $\varepsilon$ , we match it with a given effect constant l, and return an effect tail  $\varepsilon'$  and substitution  $\theta$  such that  $\theta\varepsilon \equiv \langle \theta l \mid \theta\varepsilon' \rangle$ . Each rule basically corresponds to the equivalence rules on effect rows (Figure 2).