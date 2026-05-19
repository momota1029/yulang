# A Framework for Higher-Order Effects & Handlers

Birthe van den Berg and Tom Schrijvers KU Leuven, Belgium

### Abstract

Algebraic effects & handlers are a modular approach for modeling side-effects in functional programming. Their syntax is defined in terms of a signature of effectful operations, encoded as a functor, that are plugged into the free monad; their denotational semantics is defined by fold-style handlers that only interpret their part of the syntax and forward the rest. However, not all effects are algebraic: some need to access an internal computation. For example, scoped effects distinguish between a computation in scope and out of scope; parallel effects parallellize over a computation, latent effects defer a computation. Separate definitions have been proposed for these higherorder effects and their corresponding handlers, often leading to expedient and complex monad definitions. In this work we propose a generic framework for higher-order effects, generalizing algebraic effects & handlers: a generic free monad with higher-order effect signatures and a corresponding interpreter. Specializing this higher-order syntax leads to various definitions of previously defined (scoped, parallel, latent) and novel (writer, bracketing) effects. Furthermore, we formally show our framework theoretically correct, also putting different effect instances on formal footing; a significant contribution for parallel, latent, writer and bracketing effects.

Keywords: algebraic effects and handlers, higher-order effects and handlers, free monad, datatypes `a la carte

#### 1. Introduction

Since the nineties, monads [\[16,](#page-32-0) [17](#page-32-1), [29\]](#page-34-0) have been the standard for modeling effects in a purely functional setting. Algebraic effects & handlers [\[21](#page-33-0), [23\]](#page-33-1), however, have been gaining significant interest in recent years [\[25,](#page-33-2) [10](#page-32-2), [11\]](#page-32-3). The latter offer a modular approach to combining different kinds of effects. In particular, it is their clean separation of algebraic operations (syntax) and handlers (semantics) that makes them so attractive. Composing different algebraic effects in a particular order using the coproduct of their operations [\[27\]](#page-34-1) implies a different order of handlers and consequently leads to a different interpretation [\[34](#page-34-2)]. Handlers only know their part of the syntax, forwarding unknown effects to other handlers.

Although this modular technique of algebraic effects & handlers is desirable for every effectful program, not all effects fit the approach. The algebraicity property, which states that effectful operations commute with sequencing, is not satisfied for all kinds of effects. The proposal of Plotkin and Power [\[23](#page-33-1)] to model non-algebraic effects as handlers, was shown [\[31,](#page-34-3) [33](#page-34-4)] to lose modularity.

In this work, we propose a generic syntax and denotational semantics for different effects so that the desired modularity of separate syntax and semantics is retained. In particular, we focus on higher-order effects, i.e., effects that have access to an internal computation. For example, scoped effects & handlers [\[33,](#page-34-4) [20,](#page-33-3) [31](#page-34-3)] (e.g., catching exceptions, local variables) distinguish between an operation in scope and a continuation out of scope; latent effects & handlers [\[1\]](#page-31-0) (e.g., lazy evaluation, staging) defer an internal computation until a later point of execution; parallel effects & handlers [\[32](#page-34-5)] (e.g., for-loops) parallellize an internal computation to improve performance or efficiency.

We achieve the desired modularity by extending the free monad definition of algebraic effects & handlers to support higher-order functors, which incorporate the internal computation in their effect signatures. This, together with a generic fold-style interpreter, forms the framework for modeling different effects. In particular, the contributions of this article can be summarized as follows:

- We define a generic free monad with higher-order effect signatures [\[24](#page-33-4)] and a corresponding fold-style interpreter to represent effects that can reason over an internal computation (Section [3\)](#page-5-0).
- We model different effects from the literature, such as algebraic effects & handlers, scoped effects & handlers, parallel effects & handlers, and latent effects & handlers, as instances of this framework (Section [4\)](#page-8-0).
- We model two novel classes of effects: writer effect & handler and bracketing effect & handler to denote the functionality of writing to a log and safely dealing with resources, respectively (Section [4\)](#page-8-0).
- We show that each class of (existing and novel) effects is modeled by a free monad with a corresponding recursion scheme (Section [4\)](#page-8-0).
- We provide practical programming examples for all effects, including combinations of different effects (Section [4\)](#page-8-0).

- We back our free monad definition by a categorical model that is based on a free-forgetful adjunction (Section [5\)](#page-24-0).
- We deliver a full implementation in Haskell with more, detailed examples (Supplementary Material).

We use Haskell as a vehicle throughout this paper to illustrate our findings.

### <span id="page-2-1"></span>2. Background and Motivation

This section deals with the necessary preliminaries, starting with functors, free monads, and their relation to algebraic effects & handlers.

### <span id="page-2-0"></span>2.1. Algebraic Effects & Handlers

Algebraic effects & handlers [\[21,](#page-33-0) [23](#page-33-1)] use a free monad and an interpreter to separate the syntax of effects from their semantics. At the level of the syntax we distinguish algebraic operations, determined by their signatures, from computations: a recursive structure over these operations via the free monad. Furthermore, a recursion scheme (handler ) interprets these computations.

Algebraic Operations: Signatures. Following the approach of Plotkin and Pretnar [\[22](#page-33-5)], we model effectful operations by their signature σ. Effect signatures are modeled as functors.

```
class Functor σ where
  fmap :: (a → b) → σ a → σ b
```

An effect signature groups several effectful operations. For example, a signature for the state effect contains two operations: Get for reading and returning the state, and Put for modifiying the state, overwriting it with the given value.

data State 
$$s \ a = Get \ (s \to a) \mid Put \ s \ a$$

Computations: Free Monads. Using a functor as signature, we can construct a recursive datatype to represent computations, which may be either pure or effectful. The computation may then call the operations included by the signature. This recursive datatype is known as the free monad:

data Free 
$$(\sigma :: * \to *)$$
 a where  
 $Var :: a \to Free \ \sigma \ a$   
 $Op :: \sigma \ (Free \ \sigma \ a) \to Free \ \sigma \ a$ 

```
instance Functor \sigma \Rightarrow Monad (Free \sigma)
return = Var
Var \ x \gg k = k \ x
Op \ t \gg k = Op (fmap (\gg k) t)
```

Here, the Var constructor represents pure computations, whereas Op recursively composes computations with a branching structure that is determined by signature  $\sigma$ . Isomorphically, we can present this Op constructor as taking two arguments: an operation and a continuation [9].

$$Op :: \forall b : \underbrace{\sigma b}_{operation} \rightarrow \underbrace{(b \rightarrow Free \ \sigma \ a)}_{continuation} \rightarrow Free \ \sigma \ a$$

For example, the monad Free ( $State\ String$ ) Int represents computations with a state of type String and a result of type Int. Often, we define constructors to ease programming with effectful computations. For example, for State s, we define get and put as computations that read and set the state, respectively.

We use the monadic bind for sequencing effectful computations.

Interpretation: Folds. A recursion scheme is used to interpret free monads: we write a fold-style interpreter that gives semantics to the computations in the free monad by means of a generator and an algebra. In particular, interpreting a free monad  $Free \ \sigma \ a$  into semantic domain b requires a generator  $gen :: a \to b$  to transform pure computations into semantic domain b and an algebra  $alq :: \sigma \ b \to b$  to interpret the signature's effectful operations.

```
\begin{array}{l} \mathsf{fold}_{\mathsf{Alg}} :: \mathit{Functor} \ \sigma \Rightarrow (a \to b) \to (\sigma \ b \to b) \to \mathit{Free} \ \sigma \ a \to b \\ \mathsf{fold}_{\mathsf{Alg}} \ \mathit{gen} \ \mathit{alg} \ (\mathit{Var} \ x) = \mathit{gen} \ x \\ \mathsf{fold}_{\mathsf{Alg}} \ \mathit{gen} \ \mathit{alg} \ (\mathit{Op} \ \mathit{op}) = \mathit{alg} \ (\mathsf{fmap} \ (\mathsf{fold}_{\mathsf{Alg}} \ \mathit{gen} \ \mathit{alg}) \ \mathit{op}) \end{array}
```

For example, the following handler interprets  $Free\ (State\ s)\ a$  into semantic domain  $s\to(s,a)$  using this structural recursion scheme.

$$h_{\mathsf{State}} :: Free \ (State \ s) \ a \to (s \to (a, s))$$
  
 $h_{\mathsf{State}} = \mathsf{fold}_{\mathsf{Alg}} \ (,) \ alg \ \mathbf{where}$   
 $alg \ (Get \ k) = \lambda s \to k \ s \ s$   
 $alg \ (Put \ s' \ k) = \lambda_{-} \to k \ s'$ 

One can apply the above state handler to a computation that increments the state and returns the original state, with an initial value of 0.

>>> 
$$h_{\mathsf{State}} \ (\mathsf{get} \ggg \lambda s \to \mathsf{put} \ (s+1) \gg \mathsf{return} \ s) \ 0 \ (0,1)$$

The result is (0,1), with 0 the resulting value and 1 the (incremented) state.

Modularly Combining Effects. Often, a combination of multiple effects is desired. Such a composition is commonly modeled by the "Datatypes à la Carte" [27] approach, using the coproduct of functors, or in this case effect signatures (denoted by +)<sup>1</sup>.

data 
$$(\sigma_1 + \sigma_2)$$
  $a = Inl(\sigma_1 a) \mid Inr(\sigma_2 a)$ 

For example, we can combine stateful computations with nondeterminism. Nondeterministic operations can either fail or branch.

$$\mathbf{data}\ Choice\ a = Fail\ |\ Or\ a\ a$$
 Free (State  $s + Choice$ )  $a$ 

This modular composition allows different effect interactions [3, 34], for instance, achieving local state versus global state semantics [19], by swapping the handlers for state and nondeterminism.

One could also combine effectful operations with *unknown* effects, which are then *forwarded* to other handlers. A separator # distinguishes between the algebras to interpret and forward effects, respectively. We redefine the above state handler to include "other" (unknown) effects, forwarding them to be interpreted by other handlers, and passing the state to these handlers.

```
\begin{array}{ll} h'_{\mathsf{State}} :: \mathit{Functor} \ \sigma \Rightarrow \mathit{Free} \ (\mathit{State} \ s + \sigma) \ a \to (s \to \mathit{Free} \ \sigma \ (a, s)) \\ h'_{\mathsf{State}} = \mathsf{fold}_{\mathsf{Alg}} \ \mathit{gen} \ (\mathit{alg} \ \# \mathit{fwd}) \ \mathbf{where} \\ \mathit{gen} \ x &= \lambda s \to \mathsf{return} \ (x, s) \\ \mathit{alg} \ (\mathit{Get} \ k) &= \lambda s \to k \ s \ s \\ \mathit{alg} \ (\mathit{Put} \ s' \ k) = \lambda_- \to k \ s' \\ \mathit{fwd} \ \mathit{op} &= \lambda s \to \mathit{Op} \ (\mathsf{fmap} \ (\$ s) \ \mathit{op}) \end{array}
```

#### 2.2. Non-Algebraic Effects

Not all effects are algebraic; some denote more advanced effectful computations [1, 31, 33]. Effects are algebraic if they satisfy the *algebraicity* property, which says that algebraic computations commute with sequencing:

<span id="page-4-0"></span><sup>&</sup>lt;sup>1</sup>For the sake of readability [27], we have omitted *Inl* and *Inr* in our examples.

$$(\gg k) \circ Op \equiv Op \circ \mathsf{fmap}(\gg k)$$

Although many effects satisfy this property, not all of them do.

For example, scoped effects & handlers [\[20](#page-33-3), [31,](#page-34-3) [33\]](#page-34-4) distinguish between a scoped computation, representing the part of the program that is in scope, and a continuation, referring to the rest of the program, out of scope. This complication requires a reformulation of the algebraicity property as well as a more complex free monad to represent these effects. Examples of scoped effects & handlers are local variables, catching exceptions, local pruning of nondeterminism, and more. Furthermore, parallel effects & handlers [\[32](#page-34-5)] parallellize computations with algebraic effects, using a for-loop, for example. These effects contain a computation to parallellize, as well as a continuation. Moreover, latent effects & handlers [\[1](#page-31-0)] delay parts of an effectful program to be evaluated later in the execution. Their syntax also consists of a computation to be delayed, and a continuation. Lazy evaluation strategies in the presence of effects, and staging, among others, can be modeled by this approach.

Each of these classes of effects[2](#page-5-1) has been denotationally modeled by a specialized version of the free monad, making their representations ad hoc and inherently distinct. Moreover, the monads used to model parallel and latent effects have not been shown to be a free structure.

This work builds on the fundamental insight that these effects have something in common: they have an internal computation. Indeed, for scoped effects this internal computation is the computation in scope; for parallel effects the computation to parallellize over; for latent effects the computation to defer. We call these effects higher-order effects. With this insight, we argue that we can generalize the framework for algebraic effects and handlers to model more advanced effects as well. This generic framework retains the modularity of having separate syntax (by means of a free monad) and semantics (by means of a fold). We back the framework by categorical foundations, showing that (1) it is indeed a free monad, and (2) that it works on a range of examples.

#### <span id="page-5-0"></span>3. A Generic Free Monad for Modeling Effects

Our framework for modeling higher-order effects uses a generic free monad and interpreter. This representation deliberately does not deviate far from the algebraic effects & handlers approach (Section [2.1\)](#page-2-0), the modularity of which has already proven its importance by the adoption of algebraic effects

<span id="page-5-1"></span><sup>2</sup>We discuss them in more detail in Section [4.](#page-8-0)

in different programming languages [\[2](#page-31-2), [5,](#page-31-3) [12](#page-32-5), [13](#page-32-6)] and libraries [\[10,](#page-32-2) [11,](#page-32-3) [25](#page-33-2)]. In particular, we again use a free monad, with higher-order functors to include the internal computation in the framework, also featuring a coproduct.

Effect Signatures. Higher-order effects need access to an internal computation. In order to reflect this in the signatures, a functor representation is not sufficiently powerful. Like Poulsen and van der Rest [\[24\]](#page-33-4), we generalize effect signatures to include a higher-order functor k : (∗ → ∗) → (∗ → ∗), which is a mapping between functors. Here, the functor argument (of kind ∗ → ∗) represents the internal computation so that k f has the familiar form of an algebraic effect signature (a plain functor). We model it accordingly [\[31\]](#page-34-3):

class 
$$(\forall f : Functor \ f \Rightarrow Functor \ (k \ f)) \Rightarrow HFunctor \ k \ \mathbf{where}$$
  
hmap ::  $(Functor \ f, Functor \ f') \Rightarrow f \leadsto f' \to k \ f \leadsto k \ f'$ 

Here, ( ) represents a natural transformation between two functors[3](#page-6-0) . For example, a higher-order signature for exceptions is the following:

**data** 
$$Exc f r = Throw \mid \forall a . Catch (f a) (Maybe  $a \rightarrow r$ )$$

The continuation of catching an exception (Maybe a → r ) depends on whether or not an exception was thrown in the internal computation f a.

Computations. Similar to the free monad for algebraic effects & handlers, we can now construct a free monad that uses the above generalization of signatures.

```
data F reeH k a where
 V arH :: a → F reeH k a
 OpH :: k (F reeH k) (F reeH k a) → F reeH k a
instance HF unctor k ⇒ Monad (F reeH k) where
 return = V arH
 V arH x >>= k = k x
 OpH op >>= k = OpH (fmap (>>=k) op)
```

In Section [5](#page-24-0) we show that this is indeed a free monad. Again, using the co-yoneda lemma, we rewrite the Op<sup>H</sup> constructor: it contains an operation, an internal computation and a continuation.

$$Op_{\mathsf{H}} :: \forall f \ b : \underbrace{(k \ f \ b)}_{operation} \to \underbrace{(f \leadsto Free_{\mathsf{H}} \ k)}_{internal \ computation} \to \underbrace{(b \to Free_{\mathsf{H}} \ k \ a)}_{continuation} \to Free_{\mathsf{H}} \ k \ a$$

<span id="page-6-0"></span><sup>3</sup> type f g = ∀a . f a → g a

For example, progExc throws an exception if its argument is smaller than 0.

```
progExc :: Int → F reeH Exc String
progExc x = OpH (Catch (if x > 0 then return x else OpH Throw) k)
  where k Nothing = return "Too small"
         k (Just x ) = return (show x )
```

Interpretation. We equip this free monad with a fold-style interpreter:

```
fold :: ∀k g a b .(HF unctor k, Pointed g)
    ⇒ (a → g b) → (∀x . k g (g x ) → g x ) → (F reeH k a → g b)
fold gen alg (V arH x ) = gen x
fold gen alg (OpH op) = alg (hmap fold2 (fmap (fold gen alg) op))
  where fold2 :: F reeH k g
          fold2 (V arH x ) = η x
          fold2 (OpH t) = alg (hmap fold2 (fmap fold2 t))
```

This fold consists of two parts: one interpreting F ree<sup>H</sup> k a into semantic domain g b, and another interpreting the internal computation: F ree<sup>H</sup> k g. Consequently, from these two folds, one would expect two generators and two algebras. However, fold<sup>2</sup> relies on the fact that g is a pointed functor, which has an implicit generator ∀ a . a → g a, so that a single explicit generator suffices.

```
class Functor g ⇒ Pointed g where
  η :: a → g a
```

Furthermore, to keep things concise, we opt to reuse the same algebra for the two folds (the domain is universally quantified) to interpret the internal computation and the continuation consistently. This significantly reduces the handler's complexity but also implies that some effects are not supported (Section [4.2\)](#page-10-0). For example, our exception handler interprets the result in terms of Maybe.

```
hExc :: F reeH Exc a → Maybe a
hExc = fold Just alg where
  alg Throw = Nothing
  alg (Catch c k) = k c
                                     >>> hExc (progExc 5)
                                     Just "5"
                                     >>> hExc (progExc (−5))
                                     Just "Too small"
```

Modular Composition. In order to make a combination of different effects in the style of "Datatypes `a la Carte" [\[27](#page-34-1)], we require a coproduct of higherorder functors k<sup>1</sup> and k2. This coproduct[4](#page-8-1) (denoted by ⊕, with separator # ) works in a similar way as that for functors (Section [2\)](#page-2-1).

**data** 
$$(k_1 \oplus k_2)$$
  $f$   $a = In$   $(k_1 f a) \mid Out (k_2 f a)$   
 $(\#) :: (k_1 f a \to g b) \to (k_2 f a \to g b) \to (k_1 \oplus k_2)$   $f$   $a \to g b$   
 $(lft \# rht)$   $(In \quad op) = lft \quad op$   
 $(lft \# rht)$   $(Out \quad op) = rht \quad op$ 

### <span id="page-8-0"></span>4. Different Effects as Instances of our Framework

Different effects (algebraic and higher-order) can be viewed as instances of our generic framework, defining an appropriate higher-order functor that maps their signature to the generic setting. In particular, instantiating the framework consists of four steps:

- Step 1 Map the effect signatures to a higher-order representation by defining a higher-order functor K that maps a functor F and type A onto a type of kind ∗.
- Step 2 Show that this K is indeed a higher-order functor.
- Step 3 Plug it in the generic free monad F ree<sup>H</sup> and show that it is isomorphic to the specialized effect definition.
- Step 4 Use the generic fold function to write a handler for the effects and show that it is isomorphic to the specialized effect handler (if it exists).

In what follows, we instantiate our framework using these four steps for different classes of effects.

#### <span id="page-8-2"></span>4.1. Algebraic Effects & Handlers

We follow these steps for algebraic effects, showing their specialization of the framework isomorphic to their definition in Section [2.1.](#page-2-0)

Step 1 Our mapping ignores functor argument F, since algebraic effects do not have an internal computation. Σ is a functor for algebraic operations.

$$K_{\Sigma}^{\mathsf{Alg}} \ F \ A = \Sigma \ A$$
 
$$\operatorname{\mathbf{data}} \ K^{\mathsf{Alg}} \ \sigma \ f \ a \ \mathbf{where}$$
 
$$\operatorname{\mathsf{Op}} :: \sigma \ a \to K^{\mathsf{Alg}} \ \sigma \ f \ a$$

<span id="page-8-1"></span><sup>4</sup>For the sake of readability, we omit In and Out from our examples.

Step 2 This definition of K Alg Σ is a higher-order functor:

instance Functor 
$$\sigma \Rightarrow HFunctor\ (K^{\mathsf{Alg}}\ \sigma)$$
 where hmap  $k\ (\mathsf{Op}\ x) = \mathsf{Op}\ x$ 

Step 3 We can show that the following isomorphism holds [\(Appendix C\)](#page-39-0):

Free 
$$\sigma$$
  $a \cong Free_{\mathsf{H}}(K^{\mathsf{Alg}}\sigma)$   $a$ 

Step 4 The generic handler for algebraic effects is defined by hAlg. In [Appendix C](#page-39-0) we show that hAlg gen alg is isomorphic to foldAlg gen (alg . Op).

$$\begin{array}{l} h_{\mathsf{Alg}} :: (\mathit{Functor}\ \sigma, \mathit{Pointed}\ g) \\ \quad \Rightarrow (a \to g\ b) \to (\forall x \,.\, K^{\mathsf{Alg}}\ \sigma\ g\ (g\ x) \to g\ x) \to \mathit{Free}_{\mathsf{H}}\ (K^{\mathsf{Alg}}\ \sigma)\ a \to g\ b \\ h_{\mathsf{Alg}} = \mathsf{fold} \end{array}$$

Example: State. We have already introduced the state effect as a functor (Section [2.1\)](#page-2-0). The handler for state is written modularly in terms of F reeH.

$$\begin{array}{l} h_{\mathsf{State}} :: Functor \ \sigma \\ \qquad \Rightarrow Free_{\mathsf{H}} \ (K^{\mathsf{Alg}} \ (State \ s + \sigma)) \ a \rightarrow (s \rightarrow Free_{\mathsf{H}} \ (K^{\mathsf{Alg}} \ \sigma) \ (a, s)) \\ h_{\mathsf{State}} = h_{\mathsf{Alg}} \ \eta \ alg_{\mathsf{Alg}} \ \mathbf{where} \\ alg_{\mathsf{Alg}} \ (\mathsf{Op} \ op) = (alg \ \# \ fwd) \ op \ \mathbf{where} \\ alg \ (Get \ k) = \lambda s \rightarrow k \ s \ s \\ alg \ (Put \ s' \ k) = \lambda_{-} \rightarrow k \ s' \\ fwd \ op = \lambda s \rightarrow Op_{\mathsf{H}} \ (\mathsf{Op} \ (\mathsf{fmap} \ (\$ s) \ op))) \end{array}$$

We define smart constructors get and put to progam with the state effect and revisit the example of Section [2.1.](#page-2-0)

>>> 
$$h_{\mathsf{State}}$$
 ( $\mathbf{do}\ x \leftarrow \mathsf{get}; \mathsf{put}\ (x+1); \mathsf{return}\ 5)\ 0\ (5,1)$ 

Example: Nondeterminism. A handler for nondeterminism interprets computations in terms of a list with all possible results.

$$\begin{array}{l} h_{\mathsf{ND}} :: Functor \ \sigma \\ \qquad \Rightarrow Free_{\mathsf{H}} \ (K^{\mathsf{Alg}} \ (Choice + \sigma)) \ a \rightarrow Free_{\mathsf{H}} \ (K^{\mathsf{Alg}} \ \sigma) \ [a] \\ h_{\mathsf{ND}} = h_{\mathsf{Alg}} \ \eta \ alg_{\mathsf{Alg}} \ \mathbf{where} \\ \qquad alg_{\mathsf{Alg}} \ (\mathsf{Op} \ op) = (alg \ \# \ fwd) \ op \ \mathbf{where} \\ \qquad alg \ Fail \qquad = \mathsf{return} \ [\,] \end{array}$$

$$\begin{array}{ll} alg \; (\mathit{Or} \; p \; q) = (++) \; \langle \$ \rangle \; p \; \langle * \rangle \; q \\ fwd & = \mathit{Op}_{\mathsf{H}} \, . \, \mathsf{Op} \end{array}$$

Constructors fail and or allow programming with nondeterminism as an effect (similar to get and put). For instance, consider the following example.

>>> 
$$h_{\rm ND}$$
 (or (return 1) (or (or (return 2) (return 3)) fail))  $[1,2,3]$ 

### <span id="page-10-0"></span>4.2. Scoped Effects & Handlers

Definition. Scoped effects & handlers model effects that delimit a certain scope, with as most prominent examples exceptions, nondeterminism with once, and local state variables. In order to retain the separation between syntax and semantics, and to achieve the same modularity as for algebraic effects, the literature [\[20](#page-33-3), [31,](#page-34-3) [33\]](#page-34-4) proposes to model scoped effects by a recursive datatype Prog that captures both algebraic and scoped effects. Algebraic operations are represented by a functor σ, whereas another functor γ is used for scoped operations.

### data Prog σ γ a where

$$Var :: a \longrightarrow Prog \ \sigma \ \gamma \ a$$

$$Op :: \sigma \ (Prog \ \sigma \ \gamma \ a) \longrightarrow Prog \ \sigma \ \gamma \ a$$

$$Enter :: \gamma \ (Prog \ \sigma \ \gamma \ (Prog \ \sigma \ \gamma \ a)) \longrightarrow Prog \ \sigma \ \gamma \ a$$

Here, Op corresponds to algebraic effects, and Enter enters a scope, representing scoped effects. Enter can be rewritten (using the co-yoneda lemma) as a program with (1) a scoped computation that represents the program in scope, and (2) a continuation, outside the scope.

$$Enter :: \forall b \ c . \ \gamma \ b \rightarrow \underbrace{(b \rightarrow Prog \ \sigma \ \gamma \ c)}_{scoped \ computation} \rightarrow \underbrace{(c \rightarrow Prog \ \sigma \ \gamma \ a)}_{continuation} \rightarrow Prog \ \sigma \ \gamma \ a$$

We zoom in on scoped effects only, to later compose them again with algebraic effects. F reeSc is isomorphic to Prog without Op for algebraic effects.

### data F reeSc γ a where

$$Var :: a \longrightarrow Free_{\mathsf{Sc}} \gamma \ a$$
  
 $Enter :: \gamma \ (Free_{\mathsf{Sc}} \ \gamma \ (Free_{\mathsf{Sc}} \ \gamma \ a)) \longrightarrow Free_{\mathsf{Sc}} \gamma \ a$ 

Interpretation. To interpret scoped effects, Yang et al. [\[33\]](#page-34-4) have proposed functorial algebras as a structured way of handling scoped effects, in contrast with the more tedious approach of Pir´og et al. [\[20\]](#page-33-3) in terms of indexed algebras. A functorial algebra [\[33](#page-34-4)] consists of two parts: an endo-algebra (AlgE) interprets the part of the program in scope, whereas a base algebra (AlgB) interprets the continuation.

data 
$$Alg_E \ \gamma \ f = Alg_E \ \{$$
 data  $Alg_B \ \gamma \ f \ a = Alg_B \ \{$   $enter_B :: \gamma \ (f \ a) \rightarrow a \}$   $enter_E :: \forall x . \gamma \ (f \ (f \ x)) \rightarrow f \ x \}$ 

Nearly always, the two algebras (endo- and base algebra) have the same implementation, simplifying the code significantly but disallowing a different interpretation inside and outside the scope. A different interpretation is desirable, for example, when abstracting over evaluation strategies such as depth-first search, breadth-first search or depth-bound search, the latter of which can be modeled as a scoped effect [\[33\]](#page-34-4). In our generic framework, we require the two algebras to be the same for simplicity reasons. The structural recursion scheme foldSc is specialized to interpreting F reeSc, a free monad with only scoped effects.

```
foldSc :: Functor γ
     ⇒ (a → b) → AlgE γ f → AlgB γ f b → F reeSc γ a → b
foldSc gen algE algB (V ar x ) = gen x
foldSc gen algE algB (Enter sc) = enterB algB (fmap endo sc)
  where endo = hcata . fmap (foldSc gen algE algB)
         hcata (V ar x ) = returnE algE x
         hcata (Enter sc) = (enterE algE . fmap (hcata . fmap hcata)) sc
```

Generic Framework. Scoped effects & handlers fit our generic framework. Step 1 We define a mapping using a functor Γ to represent scoped operations.

$$K_{\Gamma}^{\mathsf{Sc}} \ F \ A = \Gamma \ (F \ A)$$
 
$$\qquad \qquad \mathbf{data} \ K^{\mathsf{Sc}} \ \gamma \ f \ a \ \mathbf{where}$$
 
$$\mathsf{Enter} :: \gamma \ (f \ a) \to K^{\mathsf{Sc}} \ \gamma \ f \ a$$

Step 2 This mapping KSc Γ is a higher-order functor.

instance Functor 
$$\gamma \Rightarrow HFunctor (K^{Sc} \gamma)$$
 where hmap  $k$  (Enter  $sc) =$ Enter (fmap  $k$   $sc)$ 

Step 3 We say that the following isomorphism holds [\(Appendix C\)](#page-39-0):

$$Free_{\mathsf{Sc}} \ \gamma \ a \cong Free_{\mathsf{H}} \ (K^{\mathsf{Sc}} \ \gamma) \ a$$

Step 4 We write a handler in terms of the generic recursion scheme. In [Appendix C](#page-39-0) we show that foldSc gen alg alg is isomorphic to hSc gen (λ(Enter sc) → enter<sup>E</sup> alg sc) with return<sup>E</sup> alg = η. Notice that we use the same implementation for endo-algebra and base-algebra.

$$\begin{array}{l} h_{\mathsf{Sc}} :: (Functor \ \gamma, Pointed \ g) \\ \quad \Rightarrow (a \to g \ b) \to (\forall x \, . \, K^{\mathsf{Sc}} \ \gamma \ g \ (g \ x) \to g \ x) \to Free_{\mathsf{H}} \ (K^{\mathsf{Sc}} \ \gamma) \ a \to g \ b \\ h_{\mathsf{Sc}} = \mathsf{fold} \end{array}$$

We reconstruct the Prog datatype using the coproduct of the higher-order functors for algebraic and scoped effects, and define a corresponding handler.

$$\begin{array}{ll} \operatorname{Prog} \ \sigma \ \gamma \ a \ \cong \ \operatorname{Free_H} \ (K^{\mathsf{Alg}} \ \sigma + K^{\mathsf{Sc}} \ \gamma) \ a \\ h_{\mathsf{Prog}} :: (\operatorname{Functor} \ \sigma, \operatorname{Functor} \ \gamma, \operatorname{Pointed} \ g) \\ \quad \Rightarrow (a \to g \ b) \to (\forall x \ . \ (K^{\mathsf{Alg}} \ \sigma \oplus K^{\mathsf{Sc}} \ \gamma) \ g \ (g \ x) \to g \ x) \\ \quad \to \operatorname{Free_H} \ (K^{\mathsf{Alg}} \ \sigma \oplus K^{\mathsf{Sc}} \ \gamma) \ a \to g \ b \\ h_{\mathsf{Prog}} = \mathsf{fold} \end{array}$$

Example: Nondeterminism with Once. To exemplify this approach, we use nondeterminism with once, an operation that only returns the first result of a nondeterministic program. We distinguish between the nondeterministic algebraic operations Fail and Or , and the scoped operation Once.

```
data Once a = Once a
```

Again, we interpret nondeterministic programs in terms of a list, that retains all found results. The handler for nondeterminism with once features both algebraic (Or and Fail) and scoped (Once) operations.

```
hOnce :: (Functor σ, Functor γ)
     ⇒ F reeH (KAlg (Choice + σ) ⊕ KSc (Once + γ)) a
     → F reeH (KAlg σ ⊕ KSc γ) [a ]
hOnce = fold gen (algAlg # algSc) where
  gen x = return [x ]
  algAlg (Op op) = (algChoice # fwdChoice) op where ...
  algSc (Enter sc) = (algOnce # fwdOnce ) sc where
    algOnce (Once y) = join (fmap head y)
    fwdOnce = OpH . Enter . fmap (fmap liftOnce)
       where liftOnce = foldr (λx xs → (++) h$i x h∗i xs) (return [ ])
```

We define smart constructors fail, or and once in the usual way to write nondeterministic programs. For example, consider the difference between the following program with scoped operation once, which effectively continues the rest of the program after the first result, and the equivalent program without once.

```
>>> hOnce ( once (or (return 1) (return 5)) >>=
    λx → or (return x ) (return (x + 1)))
[1, 2]
>>> hOnce (or (return 1) (return 5) >>=
    λx → or (return x ) (return (x + 1)))
[1, 2, 5, 6]
```

### 4.3. Parallel Effects & Handlers

Definition. In general, algebraic effects are executed sequentially. However, in several cases, for example for performance reasons, a parallel execution of effects might be desired. Xie et al. [\[32\]](#page-34-5) define parallel effects & handlers, with an operational semantics that supports both algebraic and parallel effects. In particular, they represent parallel effects by means of a for keyword to iterate over parallellizable computations. Their work comes with an implementation in Dex [\[18](#page-32-7)] and in Haskell. They represent parallel effects by F reePar ρ a, where ρ is an iterable functor to represent parallel operations[5](#page-13-0) .

```
data F reePar ρ a where
 V ar :: a → F reePar ρ a
 For :: ρ (F reePar ρ b) → (ρ b → F reePar ρ a) → F reePar ρ a
```

Here, V ar is a pure computation and For represents a parallellizable computation. For takes two arguments: an iterable structure of computations (indicated by functor ρ), and a continuation.

Xie et al. [\[32](#page-34-5)] do not show that this representation of parallel effects is a free monad.

Generic Framework. Parallel effects can be expressed in terms of our framework.

Step 1 We define a higher-order functor KPar P for mapping effect signatures:

$$K_{\mathbf{P}}^{\mathsf{Par}} \ F \ A = \mathbf{P} \ (F \ B) \times (\mathbf{P} \ B \Rightarrow A)$$

<span id="page-13-0"></span><sup>5</sup>This differs from the implementation of Xie et al. [\[32](#page-34-5)] in two ways: it omits algebraic effects and uses a generic functor ρ instead of Lists to iterate over computations.

data 
$$K^{\mathsf{Par}} \ \rho \ f \ a \ \mathbf{where}$$
  
For ::  $\rho \ (f \ b) \to (\rho \ b \to a) \to K^{\mathsf{Par}} \ \rho \ f \ a$ 

Step 2 Indeed, KPar P is a higher-order functor:

instance Functor 
$$\rho \Rightarrow HFunctor\ (K^{\mathsf{Par}}\ \rho)$$
 where hmap  $k$  (For  $iters\ c) = \mathsf{For}\ (\mathsf{fmap}\ k\ iters)\ c$ 

Step 3 Now, the following isomorphism holds [\(Appendix C\)](#page-39-0):

$$Free_{\mathsf{Par}} \ \rho \ a \ \cong \ Free_{\mathsf{H}} \ (K^{\mathsf{Par}} \ \rho) \ a$$

This implies that also F reePar is a free monad.

Step 4 A handler for parallel effects can now be defined generically. In [Appendix C,](#page-39-0) we show that the handler of [\[32](#page-34-5)] (in our adapted version) is isomorphic to hPar gen (λ(For iters k) → hFor alg iters k).

$$\begin{array}{l} h_{\mathsf{Par}} :: (Functor \; \rho, Pointed \; g) \\ \quad \Rightarrow (a \to g \; b) \to (\forall \, x \, . \, K^{\mathsf{Par}} \; \rho \; g \; (g \; x) \to g \; x) \to Free_{\mathsf{H}} \; (K^{\mathsf{Par}} \; \rho) \; a \to g \; b \\ h_{\mathsf{Par}} = \mathsf{fold} \end{array}$$

Example: Parallel Accumulation. We revisit the example of Xie et al. [\[32](#page-34-5)] that imitates Dex's accumulation effect, which is similar to state but can only increment and is implicitly initialized with the identity of this increment. The accumulation is represented by an algebraic operation Accum m, where m is a monoid[6](#page-14-0) .

data Accum m a = Accum m a

The handler for parallel accumulation features algebraic and parallel effects.

```
hAccum :: (Monoid m, Functor σ)
      ⇒ F reeH (KAlg (Accum m + σ) ⊕ KPar [ ] a
      → F reeH (KAlg σ) (m, a)
hAccum = fold gen (algAlg # algPar) where
  gen x = return (ǫ, x )
  algAlg (Op op) = (algAccum # fwdAccum) op where
    algAccum (Accum m′
                      k) = fmap (λ(m, x ) → (m′ ⋄ m, x )) k
    fwdAccum = OpH . Op
```

<span id="page-14-0"></span><sup>6</sup>A monoid is defined as a set equipped with an associative binary operation ⋄, and an identity ǫ.

```
alg_{\mathsf{Par}} (For iters\ k) = \mathbf{do}

(ms, xs) \leftarrow \mathsf{fmap}\ unzip\ (sequence\ iters)

\mathsf{let}\ append\ (m, x) = (foldr\ (\diamond)\ m\ ms, x)\ \mathsf{in}\ \mathsf{fmap}\ append\ (k\ xs)
```

We define constructors **accum** and **for** to accumulate and iterate over computations, respectively. Consider the following example that computes the sum of a list of integers. We use the Sum monoid for our accumulator.

```
>>> h_{\mathsf{Accum}} (for (fmap (accum . Sum) [1,2,10,4])) 17
```

#### 4.4. Writer Effect & Handler

To define writer effects & handlers, we use the writer monad as a running example. The writer monad keeps track of both return values and output messages, for example in a log file. The minimal complete definition of the writer effect, according to the MonadWriter library<sup>7</sup>, requires three operations: tell, listen and pass. The former is an algebraic operation, producing output messages of type w.

```
\mathsf{tell} :: w \to m \ ()
```

Both listen and pass do not fit any of the previously defined effects. We reformulate their definitions to make them fit our generic framework. listen executes a computation and returns a tuple of the resulting value and the output message. It is used to *inspect* what a subcomputation has written to the output.

```
\begin{array}{l} \text{listen} :: m \ a \to m \ (a,w) \\ \cong \text{ listen} :: m \ a \to ((a,w) \to m \ b) \to m \ b \\ \cong \text{ listen} :: m \ (w \to m \ b) \\ \cong \text{ listen} :: m \ (\varphi_{\mathsf{listen}} \ (m \ b)) \\ \to m \ b \end{array} \quad \text{with} \ \varphi_{\mathsf{listen}} \ w = ((\to) \ w) \end{array}
```

Furthermore, pass executes a computation, resulting in a value and a function, the latter of which is applied to the output message. It is used to *modify* what is written to the output.

$$\begin{array}{l} \mathsf{pass} :: m \ (a, w \to w) \to m \ a \\ \cong \ \mathsf{pass} :: m \ (\varphi_{\mathsf{pass}} \ a) \\ \end{array} \to m \ a \qquad \mathsf{with} \ \varphi_{\mathsf{pass}} \ w = ((,) \ (w \to w)) \end{array}$$

We now abstract over these two definitions of listen and pass, defining a novel kind of effects and showing that they are a special case of our generic framework.

<span id="page-15-0"></span><sup>&</sup>lt;sup>7</sup>https://hackage.haskell.org/package/mtl-2.2.2/docs/Control-Monad-Writer-Class.html

Definition. We dub these effects writer effects and denote them by F reeWrite ϕ a, where ϕ is a functor for writer effect operations.

data F reeWrite ϕ a where

$$Var :: a \longrightarrow Free_{\mathsf{Write}} \ \varphi \ a$$

$$Exec :: Free_{\mathsf{Write}} \ \varphi \ (\varphi \ (Free_{\mathsf{Write}} \ \varphi \ a)) \rightarrow Free_{\mathsf{Write}} \ \varphi \ a$$

Here, V ar represents a pure computation and Exec is a writer computation. In fact, one can rewrite (using the co-yoneda lemma) Exec so that it consists of a writer action, of which the result is decorated by some functor ϕ, and a continuation.

$$Exec :: \forall b . \underbrace{Free_{\mathsf{Write}} \ \varphi \ (\varphi \ b)}_{\mathsf{writer} \ computation} \to \underbrace{(b \to Free_{\mathsf{Write}} \ \varphi \ a)}_{continuation} \to Free_{\mathsf{Write}} \ \varphi \ a$$

In particular, for listen this functor ϕ is ((→) w) as the result type of the writer action is w → m a. Similarly, pass is decorated by the functor ((,) (w → w)) as its inner action has result type (a, w → w).

Generic Framework. We show that the writer effect fits our generic framework.

Step 1 We choose an appropriate mapping KWrite <sup>Φ</sup> to express writer effects in terms of our theoretical model. Notice the similarity with scoped effects & handlers, with the order of the functors reversed.

$$K_{\Phi}^{\mathsf{Write}} \ F \ A = F \ (\Phi \ A)$$
 
$$\qquad \qquad \mathbf{data} \ K^{\mathsf{Write}} \ \varphi \ f \ a \ \mathbf{where}$$
 
$$\mathsf{Exec} :: f \ (\varphi \ a) \to K^{\mathsf{Write}} \ \varphi \ f \ a$$

Step 2 KWrite <sup>Φ</sup> is a higher-order functor:

instance Functor 
$$\varphi \Rightarrow HFunctor\ (K^{\mathsf{Write}}\ \varphi)$$
 where hmap  $k\ (\mathsf{Exec}\ x) = \mathsf{Exec}\ (k\ x)$ 

Step 3 Furthermore, the following isomorphism holds [\(Appendix C\)](#page-39-0):

$$Free_{\mathsf{Write}} \varphi \ a \cong Free_{\mathsf{H}} (K^{\mathsf{Write}} \varphi) \ a$$

This implies that also F reeWrite is a free monad.

Step 4 A handler for writer effects can now be defined in terms of our framework:

$$\begin{array}{l} h_{\mathsf{Wr}} :: (Functor \ \varphi, Pointed \ g) \\ \quad \Rightarrow (a \to g \ b) \to (\forall \, x \, . \, K^{\mathsf{Write}} \ \varphi \ g \ (g \ x) \to g \ x) \to Free_{\mathsf{H}} \ (K^{\mathsf{Write}} \ \varphi) \ a \to g \ b \\ h_{\mathsf{Wr}} = \mathsf{fold} \end{array}$$

Writing an isomorphism for this handler is not meaningful as no specialized handler for F reeWrite exists.

Example: Resetting the Log. The writer monad uses both algebraic and writer effects. Tell constructs output messages, where w is a monoid that keeps track of the output message.

```
data Tell w a = Tell w a
```

Listen sees what a (sub-)computation wrote to the output. Pass is able to adapt the message that is written to the output. Both operations are represented by a functor corresponding to the argument type of listen and pass, respectively.

```
type Listen w = ((→) w) type Pass w = ((,) (w → w))
```

The handler for writing is defined in terms of our generic framework:

```
hWrite :: (Functor σ, Monoid w)
     ⇒ F reeH (KAlg (Tell w + σ) ⊕ KWrite (Listen w + Pass w + ϕ)) a
     → F reeH (KAlg σ ⊕ KWrite ϕ) (a, w)
hWrite = fold gen (algAlg # algWrite) where
  gen x = return (x , ǫ)
  algAlg (Op op) = (algTell # fwdTell) op where
    algTell (Tell w k) = do (x , w
                               ′
                                ) ← k; return (x , w ⋄ w
                                                     ′
                                                      )
    fwdTell = OpH . Op
  algWrite (Exec k) = k >>= λcase
    (f , w) → f w
    ((f , mx)), ) → fmap (fmap f ) mx
    (op , ) → OpH (Exec (return op))
```

We define constructors tell, listen and pass to define a function reset which resets the log to empty it.

```
reset :: (Functor σ, Functor ϕ, Monoid w)
     ⇒ F reeH (KAlg (Tell w + σ) ⊕ KWrite (Listen w + (Pass w + ϕ))) ()
reset = pass (return ((), const ǫ))
```

For example, consider the following program which first logs "pre", then resets the log and then logs "post".

```
>>> hWrite (tell "post" >> reset >> tell "pre")
((), "post")
```

Alternatively, this reset function can be written in terms of censor. a derived method in the MonadWriter library, which takes a function w → w and a computation m a and modifies the writer after the computation has taken place, leaving the return value untouched. censor can either be defined as a scoped effect, or as a special case of pass [\(Appendix B\)](#page-38-0).

### 4.5. Latent Effects & Handlers

Definition. Latent effects & handlers [\[1](#page-31-0)] represent those effects that have a control-flow in which some computations are deferred for evaluation at a later point in the program interpretation. Examples of latent effects are function abstractions with effectful bodies, call-by-name or call-by-need evaluation strategies and staging. Latent effects are represented by F reeLat ζ ℓ a where ζ is the regular effect functor, and ℓ is the latent effect functor, representing the effects that are deferred[8](#page-18-0) .

```
data F reeLat ζ ℓ a where
  Leaf :: a → F reeLat ζ ℓ a
  Node :: ζ p c → ℓ () → (∀x . c x → ℓ () → F reeLat ζ ℓ (ℓ x ))
        → (ℓ p → F reeLat ζ ℓ a) → F reeLat ζ ℓ a
```

Here, Leaf is a pure computation, and Node is an internal node that contains (1) an operation ζ p c with result type p and a number of subcomputations c; (2) the effect state ℓ () in the node; (3) a function (∀ x . c x → ℓ () → F reeLat ζ ℓ (ℓ x )) to interpret a subcomputation c with result type x , given the current effect state; and (4) a continuation (ℓ p → F reeLat ζ ℓ a) to interpret the remainder of the program.

Van den Berg et al. [\[1\]](#page-31-0) do not show that F reeLat ζ ℓ a is a free monad.

Generic Framework. Latent effects are an instance of our generic free monad. Step 1 We choose a mapping[9](#page-18-1) KLat ζ,L to represent latent effects & handlers with effect functor ζ and latent effect functor L. It contains a Node constructor to represent internal nodes, similar to the Node constructor of F reeLat.

$$\begin{split} K_{\zeta,\mathcal{L}}^{\mathsf{Lat}} \ F \ A &= \int^{P,C} \zeta \ P \ C \times \mathcal{L} \ 1 \times (\int_X C \ X \times \mathcal{L} \ 1 \Rightarrow F \ (\mathcal{L} \ X)) \times (\mathcal{L} \ P \Rightarrow A) \\ \mathbf{data} \ K^{\mathsf{Lat}} \ \zeta \ \ell \ f \ a \ \mathbf{where} \\ \mathsf{Node} &:: \zeta \ p \ c \to \ell \ () \to (\forall x \ . \ c \ x \to \ell \ () \to f \ (\ell \ x)) \\ & \to (\ell \ p \to a) \to K^{\mathsf{Lat}} \ \zeta \ \ell \ f \ a \end{split}$$

Step 2 It has a corresponding higher-order functor instance.

instance 
$$HFunctor\ (K^{\mathsf{Lat}}\ \zeta\ \ell)$$
 where hmap  $k\ (\mathsf{Node}\ sub\ \ell\ st\ c) = \mathsf{Node}\ sub\ \ell\ (\mathsf{fmap}\ k\ .st)\ c$ 

Step 3 From this, the following isomorphism holds [\(Appendix C\)](#page-39-0):

<span id="page-18-0"></span><sup>8</sup>This datatype is equivalent to the Tree datatype of van den Berg et al. [\[1](#page-31-0)].

<span id="page-18-1"></span><sup>9</sup>Using ends and coends from the Algebra of Types, corresponding to Haskell's universal and existential quantification, respectively.

$$Free_{\mathsf{Lat}} \zeta \ell a \cong Free_{\mathsf{H}} (K^{\mathsf{Lat}} \zeta \ell) a$$

This implies that also F reeLat is a free monad.

Step 4 We can now write a generic handler for latent effects.

$$\begin{array}{l} h_{\mathsf{Lat}} :: Pointed \ g \\ \qquad \Rightarrow (a \to g \ b) \to (\forall \, x \, . \, K^{\mathsf{Lat}} \ \zeta \ \ell \ g \ (g \ x) \to g \ x) \to Free_{\mathsf{H}} \ (K^{\mathsf{Lat}} \ \zeta \ \ell) \ a \to g \ b \\ h_{\mathsf{Lat}} = \mathsf{fold} \end{array}$$

Writing an isomorphism for this handler is not meaningful as no specialized handler for F reeLat exists in the literature.

Example: Lazy Evaluation with Memoization. We implement call-by-need with memoization and call-by-value. This example is an adapted version of the lazy evaluation example of van den Berg et al.[\[1](#page-31-0)]. Consider the following program:

$$prog_{Lazy} = app (abs (return 3)) (do put 42; return 5)$$

It applies a constant function to an argument that changes the state of the program. With a call-by-need evaluation strategy, we expect the state to remain unchanged, as the argument is never needed and thus never executed. With an eager strategy, we expect the state of the program to be 42.

We require algebraic, scoped and latent effects to model this example. First, the algebraic state effect (Section [4.1\)](#page-8-2) can get the state and put a new state. Second, we require an environment to know which variables are in scope. We model this functionality with the scoped reader effect, which has two operations: ask, which is algebraic, for getting the current environment, and local, which is scoped, for modifying the environment before executing a computation in the modified environment. For more details on ask and local, we refer to Haskell's MonadReader[10](#page-19-0) library. Finally, the latent effect for lazy evaluation with memoization has two operations: thunk for deferring the evaluation of an operation, and force for forcing it to evaluate.

```
data Thunking v :: ∗ → (∗ → ∗) → ∗where
  Thunk :: Thunking v Ptr (OneSub v)
  Force :: Ptr → Thunking v v NoSub
data NoSub :: ∗ → ∗where
data OneSub v :: ∗ → ∗
  where One :: OneSub v v
```

<span id="page-19-0"></span><sup>10</sup><https://hackage.haskell.org/package/mtl-2.3/docs/Control-Monad-Reader.html>

Here, Ptr is a pointer (Int) to the environment that keeps track of thunks and memoized values. NoSub and OneSub indicate that Thunk and Force have no or one latent subcomputations, respectively.

For brevity, we omit forwarding of unknown effects and define an expression datatype that contains the above algebraic, scoped and latent effects.

**type** 
$$Expr\ v\ a = Free_{\mathsf{H}}\ (K^{\mathsf{Alg}}\ (State\ v + Ask\ [v]) \oplus K^{\mathsf{Sc}}\ (Local\ [v]) \oplus K^{\mathsf{Lat}}\ (Thunking\ v)\ Id)\ a$$

The semantic domain of our handler is State<sup>L</sup> s l a, where in this case, state s consists of a tuple (v, [Thunk v ]) and l is the identity functor.

```
newtype StateL s l a = StateL {unStateL :: (s, l a)}
```

A handler for lazy evaluation has three environments: (1) the state of type v; (2) the evaluation environment of type [v ] to know which variables are in scope; and (3) the environment of thunks and memoized values of type [Thunk v ]. A thunk is an unevaluated operation.

**type** Thunk 
$$v = Either (Id () \rightarrow v \rightarrow [v] \rightarrow [Thunk v] \rightarrow State_L (v, [Thunk v]) Id v) v$$

Environments (1) and (3) are part of the result of the interpreted expression. With this in place we can define hLazy, which lazily interprets a stateful program[11](#page-20-0) .

```
hLazy :: Expr v a → v → [v ] → [Thunk v ] → StateL (v, [Thunk v ]) Id a
hLazy prog s nv th = fold gen (algAlg # algSc # algLat) prog where
  gen x = StateL ((s, th),Id x )
  algAlg (Op op) = (algSt # algAsk) op where ...
  algSc (Enter sc) = algLocal sc where ...
  algLat (Node Thunk l st k) = k (length th <$ l) s nv
                                    (th ++ [Left (st One)])
  algLat (Node (Force p) l st k) = case (th !! p) of
    Left t → let StateL ((s
                             ′
                              , th′
                                  ),Id lv) = (t l) s nv th
      in unId $ fmap (λv → (k lv) s
                                     ′ nv (replace p (Right v) th′
                                                                )) lv
    Right v → (k (v <$ l)) s nv th
```

The algebras for algebraic and scoped effects hold little surprises. When thunking an operation, we call the continuation and add the current operation

<span id="page-20-0"></span><sup>11</sup>We use a compact datatype data Id a = Id {unId :: a } for the identity functor.

to the list of thunks. When forcing an operation, we get the thunk or value from the list of thunks. In case of a thunk we evaluate it, then replace it with its value in the list of thunks in order to memoize it, and call the continuation. In case of a value, we immediately call the continuation with this value.

An eager handler has the same type signature and implementation for the algebraic and scoped effects, but swaps the behaviour of Thunk and Force:

```
hEager prog s nv th = ...where
  algLat (Node Thunk l st k) =
    let StateL ((s
                   ′
                    , th′
                        ), lv) = (st One l) s nv th
    in unId $
       fmap (λv → k (length th′ <$ l) s
                                         ′ nv (th′ ++ [Right v ])) (unId lv)
  algLat (Node (Force p) l st k) = case (th !! p) of
    Right v → k (v <$ l) s nv th
```

We define constructors get, put, ask, local, thunk and force and go back to our example program to define the standard λ-calculus functionality in terms of these constructors. Values can be either integers or function abstractions:

$$\mathbf{data}\ V = Val\ Int \mid Abs\ (Expr\ V\ V)$$

We define variables, function abstraction and function application as follows. We thunk the argument of function application and evaluate it

```
var :: Ptr → Expr V V
var x = do nv ← ask; local ([nv !! x ]) (force 0)
abs :: Expr V V → Expr V V
abs body = return (Abs body)
app :: Expr V V → Expr V V → Expr V V
app e1 e2 = do vf ← e1; nv ← ask; p ← thunk e2
               case vf of Abs body → local ([nv !! p ]) body
```

We now lazily and eagerly evaluate the above program prog. We start with state 0, an empty environment and an empty list of thunks.

```
>>> hLazy progLazy (Val 0) [ ] [ ]
(0, [Left "thunk"], 3)
                                          >>> hEager progLazy (Val 0) [ ] [ ]
                                          (42, [Right 5], 3)
```

The first element of the triple is the current state, the second element is the list of thunks or memoized values, and the third element is the program result.

#### 4.6. Bracketing Effect & Handler

Consider the situation where a (built-in) exception is raised while a resource (such as a file) was being used. It is not always straightforward what has to happen in this scenario, but in each case we want to avoid that our resource is unreachable by code. The function bracket [15] acquires a resource, does something with it and then safely releases the resource again. Also if an exception occurs, bracket correctly releases the resource and re-raises the exception. This is reflected in its type:  $m \ r$  acquires the resource r, the function  $r \to m \ b$  releases the resource, the function  $r \to m \ a$  uses the resource, and  $m \ a$  is the result.

```
\begin{array}{ll} \mathsf{bracket} :: m \ r \to (r \to m \ b) \to (r \to m \ a) \to m \ a \\ \cong \mathsf{bracket} :: m \ r \to (r \to (m \ b, m \ a)) \to m \ a \\ \cong \mathsf{bracket} :: m \ (m \ b, m \ a) \to m \ a \end{array}
```

Typically, b is the unit type ()<sup>12</sup> and the monad m is the IO-monad. For example, consider the program firstTwo that opens a file "foo.txt" and reads and prints its first two characters. In case an exception occurs, the file is released (indicated by printing "released").

```
firstTwo = bracket (openFile "foo.txt" ReadMode)
(\lambda_{-} \rightarrow \text{print "released"})
(\lambda h \rightarrow \text{do } x \leftarrow \text{hGetChar } h; y \leftarrow \text{hGetChar } h; \text{print } (x, y))
```

The following prints the contents of "foo.txt" and then executes firstTwo.

```
>>> readFile "foo.txt" >>= print >> firstTwo
"HELLO, WORLD!" "H"
('H','E') "released"
"released" "***Exception: foo.txt hGetChar end of file"
```

There are two possible situations: either "foo.txt" contains enough characters (left) or an exception occurs as no more characters can be read (right). Notice that the resource is released in both cases, but in case of an error, the exception is re-raised after release.

Definition. bracket does not fit any of the previous higher-order effects. For that reason, we define  $Free_{\mathsf{Res}}$  a to represent the bracketing effect & handler.

```
\begin{array}{ccc} \mathbf{data} \; Free_{\mathsf{Res}} \; a \; \mathbf{where} \\ Var & :: a & \rightarrow Free_{\mathsf{Res}} \; a \\ Bracket :: Free_{\mathsf{Res}} \; (Free_{\mathsf{Res}} \; (), Free_{\mathsf{Res}} \; a) \rightarrow Free_{\mathsf{Res}} \; a \end{array}
```

<span id="page-22-0"></span> $<sup>^{12}</sup>$ In what follows, we replace this type b by ().

Here, V ar represents a pure computation and Bracket has the same structure as bracket, rewritten above.

Generic Framework. We show that the bracketing effect fits our framework. Step 1 We choose an appropriate mapping KRes to express bracketing.

$$K^{\mathsf{Res}} \ F \ A = F \ (F \ (), F \ A)$$
 data  $K^{\mathsf{Res}} \ f \ a \ \mathbf{where}$ 

$$\mathsf{Bracket} :: f \ (f \ (), f \ a) \to K^{\mathsf{Res}} \ f \ a$$

Step 2 KRes is a higher-order functor:

instance 
$$HFunctor\ K^{\mathsf{Res}}$$
 where hmap  $k$  (Bracket  $res$ ) = Bracket  $(k$  (fmap  $(\lambda(rel, use) \to (k\ rel, k\ use))\ res))$ 

Step 3 Furthermore, the following isomorphism holds [\(Appendix C\)](#page-39-0):

$$Free_{\mathsf{Res}} \ a \cong Free_{\mathsf{H}} \ K^{\mathsf{Res}} \ a$$

Step 4 A handler for the bracketing effect can be defined in terms of our framework:

$$\begin{array}{l} h_{\mathsf{Res}} :: (Pointed \ g) \\ \qquad \Rightarrow (a \to g \ b) \to (\forall x \, . \, K^{\mathsf{Res}} \ g \ (g \ x) \to g \ x) \to Free_{\mathsf{H}} \ K^{\mathsf{Res}} \ a \to g \ b \\ h_{\mathsf{Res}} = \mathsf{fold} \end{array}$$

Writing an isomorphism for this handler is not meaningful as no specialized handler for F reeRes exists.

Example: Print First Two Characters of File. We revisit the above example that prints the first two characters of a file, if possible. To model this example with our framework, we require algebraic effects to open (OpenFile) and read a file (ReadFile), to read a character from a file (HGetChar ), and to print it to the standard output (Print). Furthermore, we require the bracketing effect to encode the bracketing behaviour for safely releasing resources.

data Teletype 
$$a = HGetChar\ Handle\ (Char \to a)$$
  
 $|\ Print\ String\ a$   
 $|\ ReadFile\ FilePath\ (String \to a)$   
 $|\ OpenFile\ FilePath\ IOMode\ (Handle \to a)$ 

The handler for bracketing is defined in terms of our generic framework:

$$h_{\mathsf{Bracket}} :: Free_{\mathsf{H}} \ (K^{\mathsf{Alg}} \ Teletype \oplus K^{\mathsf{Res}}) \ a \to \mathsf{IO} \ a$$
  
 $h_{\mathsf{Bracket}} = \mathsf{fold} \ \eta \ (alg_{\mathsf{Tele}} \oplus alg_{\mathsf{Res}}) \ \mathbf{where}$ 

```
\begin{array}{ll} alg_{\mathsf{Tele}} \; (\mathsf{Op} \; (HGetChar \; h \qquad k)) = \mathsf{hGetChar} \; h \qquad \ggg k \\ alg_{\mathsf{Tele}} \; (\mathsf{Op} \; (Print \qquad s \qquad k)) = \mathsf{print} \; s \qquad \gg k \\ alg_{\mathsf{Tele}} \; (\mathsf{Op} \; (ReadFile \quad fp \qquad k)) = \mathsf{readFile} \; fp \qquad \ggg k \\ alg_{\mathsf{Tele}} \; (\mathsf{Op} \; (OpenFile \quad fp \; mode \; k)) = \mathsf{openFile} \; fp \; mode \; \ggg k \\ alg_{\mathsf{Res}} \; (\mathsf{Bracket} \; res) = \mathbf{do} \; (rel, use) \leftarrow res; \\ \mathsf{bracket} \; (\mathsf{return} \; ()) \; (const \; rel) \; (const \; (\mathsf{join} \; use)) \end{array}
```

We define constructors hGetC, prnt, brckt, readF and openF to revisit the example.

```
>>> h_{\rm Bracket} (readF "foo.txt" \gg= prnt \gg firstTwo) 
"HELLO, WORLD!" "H" 
"('H','E')" "released" 
"released" "***Exception: foo.txt hGetChar end of file"
```

#### <span id="page-24-0"></span>5. Formalizing the Free Monad

In what follows we present the categorical foundations of our generic free monad. For the reader who is not familiar with categories, adjunctions and free structures, we refer to Appendix A.

Summarized, our framework is based on the  $\overline{Free} \circ (Id \rtimes -) \dashv App \circ \overline{U}$  adjunction, which is a composition of two simpler adjunctions  $\overline{Free} \dashv \overline{U}$  and  $Id \rtimes - \dashv App$ . This composed adjunction gives rise to our monad  $Free_{\mathsf{H}}$  in  $\mathbb{C}$ .

$$H-Alg(\mathbb{P}\rtimes\mathbb{C}) \xleftarrow{\overline{Free}} \xrightarrow{\overline{Free}} \mathbb{P}\rtimes\mathbb{C} \xleftarrow{Id\rtimes-} \xrightarrow{App} \mathbb{C}$$

We want a monad in  $\mathbb C$  that represents higher-order effects. However, our operation signatures are no longer endofunctors in  $\mathbb C$  (as for algebraic effects), but rather higher-order endofuctors. For that reason, it is necessary to make an intermediate step from  $\mathbb C$  to a custom product category before constructing the free-forgetful adjunction.

In what follows we explain the two adjunctions with their corresponding categories and functors before putting them together.

#### 5.1. The $Id \rtimes - \dashv App \ Adjunction$

We first focus on the rightmost adjunction in the overview diagram. It connects the base category  $\mathbb{C}$  with the category  $\mathbb{P} \rtimes \mathbb{C}$ , the latter of which

is defined as a variation on the product of the category  $\mathbb{P}$  of pointed endofunctors on  $\mathbb{C}$  and the base category  $\mathbb{C}$ . This category  $\mathbb{P} \rtimes \mathbb{C}$  represents the higher-order signatures of effect operations, consisting of an internal computation (in  $\mathbb{P}$ ) and a continuation (in  $\mathbb{C}$ ). The following table summarizes the objects and morphisms of the different categories.

| Symbol                          | Objects                                      | Morphisms                                               |
|---------------------------------|----------------------------------------------|---------------------------------------------------------|
| $\mathbb{C}$                    | A, B                                         | $f:A\to B$                                              |
| $\mathbb{P}$                    | F, G                                         | $\alpha: F \to G$                                       |
| $\mathbb{P} \times \mathbb{C}$  | $\langle F, A \rangle, \langle G, B \rangle$ | $\langle \alpha : F \to G, f : A \to B \rangle$         |
| $\mathbb{P} \rtimes \mathbb{C}$ | $\langle F, A \rangle, \langle G, B \rangle$ | $\langle \alpha : F \to G, f : F \ A \to G \ B \rangle$ |

Objects in  $\mathbb{P} \rtimes \mathbb{C}$  have the form  $\langle F, A \rangle$ , where F is a pointed endofunctor on  $\mathbb{C}$  and A is an object of  $\mathbb{C}$ . Morphisms are represented by pairs  $\langle \alpha, f \rangle$  of a structure-preserving natural transformation  $\alpha : F \to G$  ( $\alpha \circ \eta^F = \eta^G$ ), and a morphism  $f : F \to G$  ( $\alpha \circ \eta^F = \eta^G$ ), are defined componentwise:

$$\langle \beta, g \rangle \circ \langle \alpha, f \rangle = \langle \beta \circ \alpha, g \circ f \rangle$$
  $id_{\langle F, A \rangle} = \langle id_F, id_{F, A} \rangle$ 

The left adjoint, functor  $Id \times -$ , maps objects and morphisms from  $\mathbb{C}$  to  $\mathbb{P} \rtimes \mathbb{C}$ . Furthermore, Id itself is a pointed endofunctor with  $\eta^{Id} = id$ . The right adjoint, functor App, does the opposite: it maps objects and morphisms from  $\mathbb{P} \rtimes \mathbb{C}$  to  $\mathbb{C}$ , applying the pointed endofunctor on  $\mathbb{C}$  to the object in  $\mathbb{C}$  and forgetting the natural transformation in the morphism.

$$(Id \rtimes -) A = \langle Id, A \rangle \qquad App \langle F, A \rangle = F A$$
$$(Id \rtimes -) f = \langle \eta^{Id}, Id f \rangle = \langle id, f \rangle \qquad App \langle \alpha, f \rangle = f$$

The adjunction is witnessed by the following isomorphism, where the left adjunct  $\psi$  and right adjunct  $\psi^{-1}$  are defined as follows:

$$\psi: \mathbb{P} \rtimes \mathbb{C} \left( (Id \rtimes -) A, \langle F, B \rangle \right) \cong \mathbb{C} \left( A, App \langle F, B \rangle \right) : \psi^{-1}$$

$$\psi(\alpha, f) = f$$

$$\psi^{-1} q = \langle \eta^F, q \rangle$$

These witnesses of the isomorphism satisfy the requisite round-trip properties.

## 5.2. The $\overline{Free} \dashv \overline{U}$ Adjunction

We now explain the free-forgetful adjunction on the left side of the diagram. In fact, category  $\mathbb{P} \rtimes \mathbb{C}$  is a special case of the product category, for which the free-forgetful adjunction is an established construction. We exploit

this situation to define our free-forgetful adjunction as a special instance of the product category.

$$H-Alg(\mathbb{C}^{\mathbb{C}}\times\mathbb{C}) \xrightarrow{L(2)} \mathbb{C}^{\mathbb{C}}\times\mathbb{C}$$

$$J \uparrow (3) \qquad U \qquad \downarrow (1) \uparrow I$$

$$H-Alg(\mathbb{P}\times\mathbb{C}) \xrightarrow{\overline{U}} \qquad (2) \downarrow I$$

$$H \to \mathbb{C}$$

In particular, we work in 4 steps: (1) we include category  $\mathbb{P} \rtimes \mathbb{C}$  in  $\mathbb{C}^{\mathbb{C}} \times \mathbb{C}$ ; (2) we discuss the free-forgetful adjunction of functor  $H: \mathbb{C}^{\mathbb{C}} \times \mathbb{C} \to \mathbb{C}^{\mathbb{C}} \times \mathbb{C}$ ; (3) we present  $H-Alg(\mathbb{P} \rtimes \mathbb{C})$  as a restricted version of the category of H-algebras; and (4) we demonstrate how  $\overline{Free} \dashv \overline{U}$  is a composition of  $Free \dashv U$  and two inclusion functors expressing the subcategory relations.

Generalizing the  $\mathbb{P} \rtimes \mathbb{C}$  Category.  $\mathbb{P} \rtimes \mathbb{C}$  is isomorphic to a subcategory of the product category  $\mathbb{P} \times \mathbb{C}$ . Indeed, every object  $\langle F, A \rangle$  in  $\mathbb{P} \rtimes \mathbb{C}$  corresponds to an object  $\langle F, F | A \rangle$  in  $\mathbb{P} \times \mathbb{C}$ . Moreover,  $\mathbb{P} \times \mathbb{C}$  is a subcategory<sup>13</sup> of  $\mathbb{C}^{\mathbb{C}} \times \mathbb{C}$  such that every object in  $\mathbb{P} \times \mathbb{C}$  is an object in  $\mathbb{C}^{\mathbb{C}} \times \mathbb{C}$ , forgetting F's pointedness.

$$\mathbb{P} \rtimes \mathbb{C} \left( \langle F, A \rangle, \langle G, B \rangle \right) = \mathbb{P} \times \mathbb{C} \left( \langle F, F A \rangle, \langle G, G B \rangle \right)$$
$$\subseteq \mathbb{C}^{\mathbb{C}} \times \mathbb{C} \left( \langle F, F A \rangle, \langle G, G B \rangle \right)$$

By transitively combining these two relations, we conclude that  $\mathbb{P} \rtimes \mathbb{C}$  is isomorphic to a subcategory of  $\mathbb{C}^{\mathbb{C}} \times \mathbb{C}$ , captured by an inclusion functor  $I:(\mathbb{P} \rtimes \mathbb{C}) \to (\mathbb{C}^{\mathbb{C}} \times \mathbb{C})$  such that  $I\langle F, A \rangle = \langle F, F, A \rangle$  and  $I\langle h_1, h_2 \rangle = \langle h_1, h_2 \rangle$ .

Generalized Adjunction. We shift our focus to the  $\mathbb{C}^{\mathbb{C}} \times \mathbb{C}$  category. Provided that  $\mathbb{C}$  has fixpoints of endofunctors,  $\mathbb{C}^{\mathbb{C}} \times \mathbb{C}$  also does. Hence, we can instantiate the free-forgetful adjunction over  $\mathbb{C}^{\mathbb{C}} \times \mathbb{C}$ , based on an endofunctor  $H: (\mathbb{C}^{\mathbb{C}} \times \mathbb{C}) \to (\mathbb{C}^{\mathbb{C}} \times \mathbb{C})$ . Here,  $H^*$  is a free monad, defined as  $H^* = U$  Free. Moreover, this fixpoint is equipped with a fold recursion scheme.

Specializing the Adjunction. In what follows we impose five restrictions that make the adjunction act between categories  $H-Alg(\mathbb{P}\rtimes\mathbb{C})$  and  $\mathbb{P}\rtimes\mathbb{C}$ .

(1) We restrict ourselves to the subcategory of  $\mathbb{C}^{\mathbb{C}} \times \mathbb{C}$  where objects are of the form  $\langle F, F, A \rangle$ .

<span id="page-26-0"></span><sup>&</sup>lt;sup>13</sup>No isomorphism since not every natural transformation preserves  $\eta$ .

- (2) We only consider endofunctors H created out of higher-order bifunctor  $K: \mathbb{C}^{\mathbb{C}} \times \mathbb{C} \to \mathbb{C}$  such that  $H\langle F, A \rangle = \langle K \ F \ \circ \ F, K \ F \ A \rangle$ . Furthermore, algebra actions for carriers  $\langle F, F \ A \rangle$  under  $Free: \mathbb{C}^{\mathbb{C}} \times \mathbb{C} \to H-Alg(\mathbb{C}^{\mathbb{C}} \times \mathbb{C})$  have the form  $\langle \alpha : K \ F \ \circ \ F \to F, f : K \ F \ (F \ A) \to F \ A \rangle$ .
- (3) We restrict ourselves further to the subcategory of algebras where  $f = \alpha_A$  and consider only actions  $\langle \alpha, \alpha_A \rangle$  that are uniquely determined by their natural transformation  $\alpha$ .
- (4) We only study  $\mathbb{C}^{\mathbb{C}}$  objects F that are pointed functors, i.e., that are also objects in  $\mathbb{P}$  with an associated  $\eta^F: Id \to F$ .
- (5) Finally, we consider solely those morphisms  $\langle h_1, h_2 \rangle$  where  $h_1$  is a pointed functor homomorphism.

It turns out that under (1) and (2),  $H^*\langle F, F A \rangle$  takes the form  $\langle Free_H K F, Free_H K F A \rangle$ , where  $H^*$  is the generalized free monad.

$$Free_H K F = \Lambda X . F X + K Free_H (Free_H X)$$

Hence,  $H^*\langle F, F, A \rangle$  is part of the subcategory of (1). Furthermore, the algebra action created by Free (2) also resides in this subcategory (3). Notice that  $Free_H$  is not a monad in  $\mathbb{P} \rtimes \mathbb{C}$ , but that it is pointed (4) because F is. Also (5) holds, as functor Free respects it: the first component of the fold with generator  $\langle h_1, h_2 \rangle$  and algebra  $\langle \alpha, \alpha_A \rangle$  is a pointed functor morphism. From these five restrictions on category  $H-Alg(\mathbb{C}^{\mathbb{C}} \times \mathbb{C})$ , we can define category  $H-Alg(\mathbb{P} \rtimes \mathbb{C})$ . Objects in  $H-Alg(\mathbb{P} \rtimes \mathbb{C})$  are tuples  $\langle \langle F, A \rangle, a : K F \circ F \to F \rangle$ , where carrier  $\langle F, A \rangle$  is an object in  $\mathbb{P} \rtimes \mathbb{C}$  and action a is a morphism in  $\mathbb{C}^{\mathbb{C}}$ . Morphisms  $\langle h_1, h_2 \rangle : \langle \langle F, A \rangle, a \rangle \to \langle \langle G, B \rangle, b \rangle$  in  $H-Alg(\mathbb{P} \rtimes \mathbb{C})$  are homomorphisms  $\langle h_1, h_2 \rangle : \langle F, A \rangle \to \langle G, B \rangle$  in  $\mathbb{P} \rtimes \mathbb{C}$ :

$$\begin{array}{cccccccccccccccccccccccccccccccccccc$$

Observe that objects  $\langle\langle F,A\rangle,a\rangle$  in  $H-Alg(\mathbb{P}\rtimes\mathbb{C})$  are in one-to-one correspondence with  $\langle\langle F,F,A\rangle,\langle a,a_A\rangle\rangle$  of  $H-Alg(\mathbb{C}^{\mathbb{C}}\times\mathbb{C})$  that are subject to the above restrictions. Similarly, morphisms  $\langle h_1,h_2\rangle$  in  $H-Alg(\mathbb{P}\rtimes\mathbb{C})$  are also morphisms in  $H-Alg(\mathbb{C}^{\mathbb{C}}\times\mathbb{C})$  that meet the restrictions. The above two correspondences are witnessed by an inclusion functor  $J:H-Alg(\mathbb{P}\rtimes\mathbb{C})\to H-Alg(\mathbb{C}^{\mathbb{C}}\times\mathbb{C})$  such that  $J\langle\langle F,A\rangle,a\rangle=\langle\langle F,F,A\rangle,\langle a,a_A\rangle\rangle$  and  $J\langle h_1,h_2\rangle=\langle h_1,h_2\rangle$ .

The Specialized Adjunction. In categorical terms we define the  $\overline{Free} \dashv \overline{U}$  adjunction as  $J^{-1} \circ Free \circ I \dashv I^{-1} \circ U \circ J$ . This implies that the  $\overline{Free} \dashv \overline{U}$  adjunction is the composition of the  $Free \dashv U$  adjunction with the two adjunctions from isomorphisms  $J^{-1} \dashv J$  and  $I \dashv I^{-1}$ . Moreover, the universal property of Free carries over to  $\overline{Free}$ . Hence,  $\overline{Free} \dashv \overline{U}$  is also a free-forgetful adjunction and  $\overline{U} \circ \overline{Free}$  is a free monad in  $\mathbb{P} \rtimes \mathbb{C}$ .

#### 5.3. Composing the Two Adjunctions

When we compose the two adjunctions, the diagram is complete.

$$H-Alg(\mathbb{C}^{\mathbb{C}}\times\mathbb{C}) \xrightarrow{\underline{I}} \mathbb{C}^{\mathbb{C}}\times\mathbb{C}$$

$$\downarrow J \uparrow \qquad \qquad \downarrow U \qquad \uparrow I \qquad \downarrow Id \rtimes -$$

$$H-Alg(\mathbb{P}\times\mathbb{C}) \xrightarrow{\underline{I}} \mathbb{P}\times\mathbb{C} \xrightarrow{\underline{I}} \mathbb{A}pp \qquad \mathbb{C}$$

In order to get a free monad in  $\mathbb{C}$ , we apply the  $\overline{Free} \circ (Id \rtimes -) \dashv App \circ \overline{U}$  adjunction. We start with an object A in  $\mathbb{C}$ , and transform it to  $\langle Id, A \rangle$  in  $\mathbb{P} \rtimes \mathbb{C}$ , where the identity functor Id is pointed. Using the free-forgetful adjunction and applying the above restrictions, we get a free monad  $\langle Free_H \ K \ Id, Free_H \ K \ Id \ A \rangle$  in  $\mathbb{P} \rtimes \mathbb{C}$ . If we then apply the App functor, we get a free monad  $Free_H \ K \ Id \ A$  in  $\mathbb{C}$ , which is indeed the monad we have used for our instantiations. Notice that  $Free_H \ K \ Id$  of this section is isomorphic to  $Free_H \ K$  of Section 3.

#### 6. Related Work

Modularly Combining Side-Effects. Alternative approaches to (modularly) combining different effects exist, with the most prominent one being monad transformers [4]. Schrijvers et al. [26] have described in detail under which circumstances or conditions the approach of algebraic effects & handlers, on which our work is based, is better or worse than the approach with monad transformers. Usually, monad transformers appear more expressive, but algebraic effects & handlers more modular. Jaskelioff [6, 7] has investigated how to make monad transformers more modular.

Non-Algebraic Effects. We are not the first to realize that not all effectful operations fit in the approach of algebraic effects & handlers. Plotkin and Power [23] first proposed to model so-called non-algebraic operations as handlers. However, this approach comes at the cost of modularity: it mixes syntax and semantics; the clear separation of both is one of the coveted properties

of algebraic effects & handlers. Wu et al. [\[31](#page-34-3)] and Yang et al. [\[33](#page-34-4)] have shown that the approach of Plotkin and Power indeed loses modularity for scoped effects and handlers and came up with a different, but very specific representation. Xie et al. [\[32\]](#page-34-5) and van den Berg et al. [\[1](#page-31-0)] have proposed similar (ad hoc) representations for parallel and latent effects, respectively. The latter two representations are, as far as we know, not yet put on formal footing.

Adoption of Algebraic and Higher-Order Effects. Algebraic effects & handlers have been picked up in many practical programming languages, such as Links [\[5\]](#page-31-3), Koka [\[12\]](#page-32-5), Effekt [\[2\]](#page-31-2), and Frank [\[13\]](#page-32-6), and libraries (e.g., fused-effects [\[25\]](#page-33-2), extensible-effects [\[10](#page-32-2)], Eff in Ocaml [\[11](#page-32-3)]). Higher-order effects are following the same trend, evidenced by their adoption at GitHub [\[28\]](#page-34-6) and in Haskell libraries such as eff [\[8\]](#page-31-5), polysemy [\[14](#page-32-9)], fused-effects [\[25\]](#page-33-2), and in-other-words [\[30\]](#page-34-7).

Scoped Effects & Handlers as Higher-Order Effects. Scoped effects & handlers have been studied denotationally, with Wu et al. [\[31](#page-34-3)] also implementing the coproduct for scoped operations. Furthermore, our instance of the framework for scoped effects corresponds to their monad E. In their work, they suggest a higher-order syntax for effect signatures, with explicit "weaving" (also sometimes called "forwarding") of handlers: threading of the handler through the higher-order syntax, distributing it for every signature. Their design is made for scoped effects specifically, and, compared to our framework, requires extra verboseness (the weaving) in order to achieve the desired modularity.

Yang et al. [\[33\]](#page-34-4) have studied a free monad for scoped effects that approximates our generic monad closely. However, their signature is tailored to algebraic and scoped effects only, not generalizing to other higher-order effects. Furthermore, they opt for two algebras to interpret scoped effects: one for the computation in scope, another for the continuation. They have only a single example in which these different algebras seem meaningful: alternating search strategies (e.g., depth-first, breadth-first and depth-bounded search).

A Calculus for Higher-Order Effects. Poulsen and van der Rest [\[24](#page-33-4)] present a calculus that models higher-order effects, of which the operational semantics contrasts with the denotational and categorical semantics of our work. Although Poulsen and van der Rest use a similar encoding of higher-order effects with higher-order functors and so-called hefty algebras, their focus is different. Their work is about the elaboration of scoped and latent effects into algebraic effects. Whereas they only consider scoped and latent effects, we provide a broader range of higher-order effects (parallel, writer, bracketing effects). Furthermore, we back up our framework with a categorical model and show it theoretically correct.

### 7. Conclusion

In summary, this work has provided a generic way of encoding different (algebraic and higher-order) effects, retaining the coveted modularity of algebraic effects & handlers.

Some design choices impact the reusability and accessibility of this work. For instance, our monad closely resembles the "regular" free monad, as we know from algebraic effects, because we choose pointed endofunctors and a custom definition of the product category. This design choice implies that we have a single, but consistent interpreter for the internal computation and the continuation of our effects. Although this seems to limit the expressivity at first sight, we found little meaningful examples in which a different interpretation is desired.

A possible strain of research to follow-up on this work is to investigate the interactions and laws for the composition of different higher-order effects (e.g., what if we parallellize scoped effects?), in the same spirit as many works [\[3,](#page-31-1) [34\]](#page-34-2) have studied the interactions of state and nondeterminism.

### References

- <span id="page-31-0"></span>[1] van den Berg, B., Schrijvers, T., Poulsen, C.B., Wu, N.: Latent effects for reusable language components. In: Oh, H. (ed.) Programming Languages and Systems. pp. 182–201. Springer International Publishing, Cham (2021)
- <span id="page-31-2"></span>[2] Brachth¨auser, J.I., Schuster, P., Ostermann, K.: Effects as capabilities: Effect handlers and lightweight effect polymorphism. Proc. ACM Program. Lang. 4(OOPSLA) (Nov 2020). https://doi.org/10.1145/3428194, <https://doi.org/10.1145/3428194>
- <span id="page-31-1"></span>[3] Gibbons, J., Hinze, R.: Just do it: Simple monadic equational reasoning. SIGPLAN Not. 46(9), 2–14 (sep 2011). https://doi.org/10.1145/2034574.2034777, <https://doi.org/10.1145/2034574.2034777>
- <span id="page-31-4"></span>[4] Gill, A.: mtl: Monad transformer library (2008), <https://hackage.haskell.org/package/mtl-1.1.0.2>
- <span id="page-31-3"></span>[5] Hillerstr¨om, D., Lindley, S.: Liberating effects with rows and handlers. In: Proceedings of the 1st International Workshop on Type-Driven Development. p. 15–27. TyDe 2016, Association for Computing Machinery, New York, NY, USA (2016). https://doi.org/10.1145/2976022.2976033, <https://doi.org/10.1145/2976022.2976033>
- [6] Jaskelioff, M.: Monatron: An extensible monad transformer library. In: Scholz, S., Chitil, O. (eds.) Implementation and Application of Functional Languages - 20th International Symposium, IFL 2008, Hatfield, UK, September 10-12, 2008. Revised Selected Papers. Lecture Notes in Computer Science, vol. 5836, pp. 233– 248. Springer (2008). https://doi.org/10.1007/978-3-642-24452-0 13, [https://doi.org/10.1007/978-3-642-24452-0\\_13](https://doi.org/10.1007/978-3-642-24452-0_13)
- [7] Jaskelioff, M.: Modular monad transformers. In: Castagna, G. (ed.) Programming Languages and Systems, 18th European Symposium on Programming, ESOP 2009, Held as Part of the Joint European Conferences on Theory and Practice of Software, ETAPS 2009, York, UK, March 22-29, 2009. Proceedings. Lecture Notes in Computer Science, vol. 5502, pp. 64–79. Springer (2009). https://doi.org/10.1007/978-3- 642-00590-9 6, [https://doi.org/10.1007/978-3-642-00590-9\\_6](https://doi.org/10.1007/978-3-642-00590-9_6)
- <span id="page-31-5"></span>[8] King, A.: eff – screaming fast extensible effects for less (2019), <https://github.com/hasura/eff>

- <span id="page-32-4"></span>[9] Kiselyov, O., Ishii, H.: Freer monads, more extensible effects. SIGPLAN Not. 50(12), 94–105 (aug 2015). https://doi.org/10.1145/2887747.2804319, <https://doi.org/10.1145/2887747.2804319>
- <span id="page-32-2"></span>[10] Kiselyov, O., Sabry, A., Swords, C., Foppa, B.: extensibleeffects: An alternative to monad transformers (2019), <https://hackage.haskell.org/package/extensible-effects>
- <span id="page-32-3"></span>[11] Kiselyov, O., Sivaramakrishnan, K.: Eff directly in ocaml. Electronic Proceedings in Theoretical Computer Science 285, 23–58 (Dec 2018). https://doi.org/10.4204/eptcs.285.2, <http://dx.doi.org/10.4204/EPTCS.285.2>
- <span id="page-32-5"></span>[12] Leijen, D.: Koka: Programming with row polymorphic effect types. Electronic Proceedings in Theoretical Computer Science 153 (06 2014). https://doi.org/10.4204/EPTCS.153.8
- <span id="page-32-6"></span>[13] Lindley, S., McBride, C., McLaughlin, C.: Do be do be do. In: Proceedings of the 44th ACM SIGPLAN Symposium on Principles of Programming Languages. p. 500–514. POPL 2017, Association for Computing Machinery, New York, NY, USA (2017). https://doi.org/10.1145/3009837.3009897, <https://doi.org/10.1145/3009837.3009897>
- <span id="page-32-9"></span>[14] Maguire, S.: polysemy: Higher-order, low-boilerplate free monads (2019), <https://hackage.haskell.org/package/polysemy>
- <span id="page-32-8"></span>[15] Marlow, S., Jones, S.P., Moran, A., Reppy, J.: Asynchronous exceptions in haskell. SIGPLAN Not. 36(5), 274–285 (may 2001). https://doi.org/10.1145/381694.378858, <https://doi.org/10.1145/381694.378858>
- <span id="page-32-0"></span>[16] Moggi, E.: An abstract view of programming languages. Tech. Rep. ECS-LFCS-90-113, Edinburgh University, Department of Computer Science (June 1989)
- <span id="page-32-1"></span>[17] Moggi, E.: Notions of computation and monads. Information and Computation 93(1), 55 – 92 (1991). https://doi.org/https://doi.org/10.1016/0890-5401(91)90052-4, selections from 1989 IEEE Symposium on Logic in Computer Science
- <span id="page-32-7"></span>[18] Paszke, A., Johnson, D.D., Duvenaud, D., Vytiniotis, D., Radul, A., Johnson, M.J., Ragan-Kelley, J., Maclaurin, D.: Getting to the

- point: Index sets and parallelism-preserving autodiff for pointful array programming. Proc. ACM Program. Lang. 5(ICFP) (aug 2021). https://doi.org/10.1145/3473593, <https://doi.org/10.1145/3473593>
- <span id="page-33-6"></span>[19] Pauwels, K., Schrijvers, T., Mu, S.C.: Handling local state with global state. In: Hutton, G. (ed.) Mathematics of Program Construction. pp. 18–44. Springer International Publishing, Cham (2019)
- <span id="page-33-3"></span>[20] Pir´og, M., Schrijvers, T., Wu, N., Jaskelioff, M.: Syntax and semantics for operations with scopes. In: Proceedings of the 33rd Annual ACM/IEEE Symposium on Logic in Computer Science. p. 809–818. LICS '18, Association for Computing Machinery, New York, NY, USA (2018). https://doi.org/10.1145/3209108.3209166, <https://doi.org/10.1145/3209108.3209166>
- <span id="page-33-0"></span>[21] Plotkin, G., Pretnar, M.: Handlers of algebraic effects. In: Castagna, G. (ed.) Programming Languages and Systems. pp. 80–94. Springer Berlin Heidelberg, Berlin, Heidelberg (2009). https://doi.org/10.1007/978-3- 642-00590-9 7
- <span id="page-33-5"></span>[22] Plotkin, G., Pretnar, M.: Handling algebraic effects. Logical Methods in Computer Science 9(4) (dec 2013). https://doi.org/10.2168/lmcs-9(4:23)2013
- <span id="page-33-1"></span>[23] Plotkin, G.D., Power, J.: Algebraic operations and generic effects. Appl. Categorical Struct. 11(1), 69– 94 (2003). https://doi.org/10.1023/A:1023064908962, <https://doi.org/10.1023/A:1023064908962>
- <span id="page-33-4"></span>[24] Poulsen, C.B., van der Rest, C.: Hefty algebras: Modular elaboration of higher-order algebraic effects (2023)
- <span id="page-33-2"></span>[25] Rix, R., Thomson, P., Wu, N., Schrijvers, T.: fusedeffects: A fast, flexible, fused effect system (2018), <https://hackage.haskell.org/package/fused-effects>
- <span id="page-33-7"></span>[26] Schrijvers, T., Pir´og, M., Wu, N., Jaskelioff, M.: Monad transformers and modular algebraic effects: What binds them together. In: Proceedings of the 12th ACM SIGPLAN International Symposium on Haskell. p. 98–113. Haskell 2019, Association for Computing Machinery, New York, NY, USA (2019). https://doi.org/10.1145/3331545.3342595, <https://doi.org/10.1145/3331545.3342595>

- <span id="page-34-1"></span>[27] Swierstra, W.: Data types `a la carte. J. Funct. Program. 18(4), 423–436 (jul 2008). https://doi.org/10.1017/S0956796808006758, <https://doi.org/10.1017/S0956796808006758>
- <span id="page-34-6"></span>[28] Thomson, P., Rix, R., Wu, N., Schrijvers, T.: Fusing industry and academia at github (experience report). In: Proceedings of the 18th ACM SIGPLAN International Conference on Functional Programming (2022), <https://arxiv.org/abs/2206.09206>
- <span id="page-34-0"></span>[29] Wadler, P.: Monads for functional programming. In: Advanced Functional Programming, First International Spring School on Advanced Functional Programming Techniques-Tutorial Text. pp. 24–2. Springer-Verlag, Berlin, Heidelberg (1995). https://doi.org/10.5555/647698.734146
- <span id="page-34-7"></span>[30] Waern, L.: in-other-words: A higher-order effect system where the sky's the limit (2022), <https://hackage.haskell.org/package/in-other-words>
- <span id="page-34-3"></span>[31] Wu, N., Schrijvers, T., Hinze, R.: Effect handlers in scope. SIGPLAN Not. 49(12), 1–12 (sep 2014). https://doi.org/10.1145/2775050.2633358, <https://doi.org/10.1145/2775050.2633358>
- <span id="page-34-5"></span>[32] Xie, N., Johnson, D.D., Maclaurin, D., Paszke, A.: Parallel algebraic effect handlers. CoRR abs/2110.07493 (2021), <https://arxiv.org/abs/2110.07493>
- <span id="page-34-4"></span>[33] Yang, Z., Paviotti, M., Wu, N., van den Berg, B., Schrijvers, T.: Structured handling of scoped effects. In: Sergey, I. (ed.) Programming Languages and Systems. pp. 462–491. Springer International Publishing, Cham (2022)
- <span id="page-34-2"></span>[34] Yang, Z., Wu, N.: Reasoning about effect interaction by fusion. Proc. ACM Program. Lang. 5(ICFP) (aug 2021). https://doi.org/10.1145/3473578, <https://doi.org/10.1145/3473578>

#### <span id="page-35-0"></span>Appendix A. Background on Category Theory

In this Appendix, we go over some basic definitions, concepts and terminology. This subsection provides the necessary preliminaries for Section 5, which elaborates on the categorical foundations of our generic framework.

**Definition 1 (Category).** A category  $\mathbb{C}$  is defined in terms of four parts:

- 1. A collection of objects A, B.
- 2. For every two objects in  $\mathbb{C}$ , a collection of morphisms between those two objects. This is often called the hom-set, and we denote it by  $\mathbb{C}(A, B)$ .
- 3. For every object an identity morphism:  $\forall A \in \mathbb{C} : id_A \in \mathbb{C}(A, A)$
- 4. For every two morphisms their composition:  $\forall f \in \mathbb{C}(A,A), g \in \mathbb{C}(B,C): f \circ g \in \mathbb{C}(A,C)$

Furthermore, two properties should be satisfied:

1. Associativity of composition.

$$\forall A, B, C, D \in \mathbb{C} : \forall f \in \mathbb{C}(A, B), g \in \mathbb{C}(B, C), h \in \mathbb{C}(C, D) : (f \circ g) \circ h \equiv f \circ (g \circ h)$$

П

2. Left unit, right unit of composition.

$$\forall A, B \in \mathbb{C} : \forall f \in \mathbb{C}(A, B) : id_B \circ f \equiv f \equiv f \circ id_A$$

**Definition 2 (Homomorphism).** A homomorphism is a morphism that preserves the algebraic structure of the objects.

**Definition 3 (Initial Object).** The initial object of a category  $\mathbb{C}$  is an object in  $\mathbb{C}$  such that for all objects A in  $\mathbb{C}$  there exists a unique morphism from that initial object to A.

**Definition 4 (Functor).** A functor  $F : \mathbb{C} \to \mathbb{D}$  is a structure-preserving mapping between two categories  $\mathbb{C}$  and  $\mathbb{D}$ . It maps both the objects and the hom-set of category  $\mathbb{C}$  into category  $\mathbb{D}$ , respecting identities and composition:  $F : id_A = id_{FA}$  and  $F : (f \circ g) = F : f \circ F : g$ .

**Definition 5 (Endofunctor).** An endofunctor  $F: \mathbb{C} \to \mathbb{C}$  is a functor from a category to itself. The category of endofunctors on  $\mathbb{C}$  is denoted by  $\mathbb{C}^{\mathbb{C}}$ .  $\square$ 

Definition 6 (Pointed Endofunctor). An endofunctor P:C → C is pointed if it is equipped with a designated natural transformation from the identity functor η P : Id → P . We denote the category of pointed endofunctors by P. 

Definition 7 (Adjunction). An adjunction L ⊣ R is a relation between two functors L : C → D and R : D → C, with C and D categories, so that there exists a natural isomorphism between their hom-sets:

$$\psi : \mathbb{C}(LA, B) \cong \mathbb{D}(A, RB) : \psi^{-1}$$

Here, ψ and ψ <sup>−</sup><sup>1</sup> are two natural transformations witnessing the isomorphism, which should satisfy the requisite roundtrip properties (ψ ◦ ψ <sup>−</sup><sup>1</sup> = id = ψ <sup>−</sup><sup>1</sup> ◦ ψ).

Often, an adjunction is denoted by a diagram and L and R are called the left adjoint and right adjoint, respectively.

$$\mathbb{D} \xrightarrow{L \atop L \atop R} \mathbb{C}$$

An adjunction gives rise to a monad R ◦ L in C, that is equipped with a unit operator and a sequencing operator.

$$\begin{array}{ll} \eta &: A \rightarrow R \; (L \; A) \\ \mathsf{join} : (R \; \circ \; L \; \circ \; R \; \circ \; L) \; A \rightarrow R \; (L \; A) \end{array}$$

Adjunctions can be combined: we can compose L<sup>1</sup> ⊣ R<sup>1</sup> and L<sup>2</sup> ⊣ R2, composing their functors such that L<sup>2</sup> ◦ L<sup>1</sup> ⊣ R<sup>1</sup> ◦ R2.

$$\mathbb{C}_1 \xrightarrow{L_2} \mathbb{C}_2 \xrightarrow{L_1} \mathbb{C}_3 \cong \mathbb{C}_1 \xrightarrow{L_2 \circ L_1} \mathbb{C}_3$$

Furthermore, we can define the product of adjunctions L<sup>1</sup> ⊣ R<sup>1</sup> and L<sup>2</sup> ⊣ R2, acting between their product categories and taking the product of the adjoints.

$$\mathbb{C}_{1} \xrightarrow{L_{1}} \mathbb{C}_{2} \text{ and } \mathbb{C}_{3} \xrightarrow{L_{2}} \mathbb{C}_{4} \qquad \mathbb{C}_{1} \times \mathbb{C}_{3} \xrightarrow{L_{1} \times L_{2}} \mathbb{C}_{2} \times \mathbb{C}_{4}$$
then

<span id="page-36-0"></span>Definition 8 (Free-forgetful Adjunction). In general, a free-forgetful adjunction consists of a free functor Free, left adjoint of a forgetful functor U , which forgets some structure.

$$\Sigma - Alg(\mathbb{C}) \xrightarrow{Free} \mathbb{C}$$

Here, we consider an endofunctor  $\Sigma : \mathbb{C} \to \mathbb{C}$  in category  $\mathbb{C}$ . The category on the left is the category of  $\Sigma$ -algebras over  $\mathbb{C}$ , with as objects pairs  $\langle A, alg \rangle$ , where A is called the carrier of the algebra and  $alg : \Sigma A \to A$  is the action. Homomorphisms (Figure 8)  $f : A \to B$  in  $\Sigma - Alg(\mathbb{C})$  map the carriers.

$$\begin{array}{ccc}
\Sigma & A & \xrightarrow{\Sigma f} & \Sigma & B \\
& & \downarrow alg_B \\
A & \xrightarrow{f} & B
\end{array}$$
Fig. 8. Actions are

structure-preserving.

Now, category  $\Sigma - Alg(\mathbb{C})$  also has an initial object. Following Lambek's theorem, the action of the initial object is an isomorphism ( $\Sigma$   $i \cong i$  with i the initial object). This means that the initial object is a fixed point of  $\Sigma$ . Therefore, we consider the algebra for which  $\Sigma^*$  A is the carrier; it has an action  $Op: \Sigma$  ( $\Sigma^*$  A)  $\to \Sigma^*$  A. Furthermore, the definition of initial objects states that there must be a unique homomorphism from the initial object to any other  $\Sigma$ -algebra. We call this unique homomorphism a fold and describe the uniqueness by the following two diagrams, which must commute.

$$\begin{array}{cccccccccccccccccccccccccccccccccccc$$

This uniqueness is called the universal property of fold. This fold is determined in terms of the generator  $gen:A\to B$ , which is a morphism in the category of  $\Sigma$ -algebras, and the action of the target  $\Sigma$ -algebra. The free-forgetful adjunction gives rise to the free monad in  $\mathbb{C}$ , generated by  $\Sigma$ ; this free monad is often denoted by  $\Sigma^*$ . An alternative notation for a fold with generator gen and algebra alg is  $\{gen, alg\}$ . Notice the similarity between this adjunction and our free monad definition in Section 2.1, where we denote  $\Sigma^*$  as  $Free\ \sigma$ , we use Var as the return of the monad, Op as the action of the initial object, and  $fold_{Alg}\ gen\ alg$  as the structural recursion scheme to interpret  $\Sigma^*\ A$  into B, with the implementation matching the above commuting diagrams.

The model of algebraic effects & handlers revolves around the free monad definition (effects) and its interpretation in terms of a fold-style recursion scheme (handlers). Operations are captured by an endofunctor  $\Sigma: \mathbb{C} \to \mathbb{C}$  on the base category  $\mathbb{C}$ . This endofunctor is exactly the functor we have described in the above free-forgetful adjunction. Furthermore, it represents

the effect signature and determines the shapes of programs that call Σoperations, and the shapes of handlers that interpret them.

# <span id="page-38-0"></span>Appendix B. Two Ways of Modifying the Log with censor

We can write censor in terms of pass. The difference between these two operations is that censor gets the modifying function separately, whereas in pass, it is part of the computation result. Thus, we can easily define censor in terms of pass as follows:

```
censor :: (w → w) → m a → m a
censor f k = pass $ do x ← k; return (x , f )
```

From this definition, it follows that we can rewrite our reset example in terms of censor.

```
reset = censor (const ǫ) (return ())
```

The result remains the same

```
>>> hWrite (tell "post" >> reset >> tell "pre")
((), "post")
```

Alternatively, we can think of this function as the dual of local for reading from an environment, where local first modifies the environment and then executes a computation. Dually, censor executes a computation and then modifies the output. Both local and censor can be modeled as a scoped computation. For example, we can extend the above handler with scoped effect Censor w.

```
data Censor w a = Censor (w → w) a
```

Furthermore, we extend our handler accordingly:

```
hCensor :: (Functor σ, Functor γ, Monoid w, Functor ϕ)
  ⇒ F reeH (KAlg (Tell w + σ) ⊕ KSc (Censor w + γ)
                                ⊕ KWrite (Listen w + Pass w + ϕ)) a
  → F reeH (KAlg σ ⊕ KSc γ ⊕ KWrite ϕ) (a, w)
hCensor = fold gen (algAlg # algSc # algWrite) where
  algSc (Enter sc) = (algCensor # fwdCensor) sc where
    algCensor (Censor f k) = do (mx , ) ← k; (x , w) ← mx ; return (x , f w)
    fwdCensor = OpH . Enter . fmap (fmap fst)
  ...
```

The example computation gives the same result as before.

>>> 
$$h_{\text{Censor}}$$
 (tell "post"  $\gg reset \gg \text{tell}$  "pre") ((), "post")

### <span id="page-39-0"></span>Appendix C. Isomorphisms

Appendix C.1. Algebraic Effects & Handlers First, we define the isomorphisms:

```
iso1 :: Functor σ ⇒ Free σ a → F reeH (KAlg σ) a
iso1 (Var x ) = V arH x
iso1 (Op op) = OpH (Op (fmap iso1 op))
iso2 :: Functor σ ⇒ F reeH (KAlg σ) a → Free σ a
iso2 (V arH x ) = Var x
iso2 (OpH (Op op)) = Op (fmap iso2 op)
```

And next, we show that the requisite roundtrip properties hold, i.e., iso<sup>1</sup> . iso<sup>2</sup> = id = iso<sup>2</sup> . iso2.

```
(iso1 . iso2) (V arH x )
   ≡ iso1 (Var x )
   ≡ V arH x
(iso1 . iso2) (OpH (Op op))
   ≡ iso1 (Op (fmap iso2 op))
   ≡ OpH (Op (fmap iso1 (fmap iso2 op)))
   ≡ OpH (Op (fmap (iso1 . iso2) op))
   ≡ OpH (Op op)
                                       (iso2 . iso1) (Var x )
                                          ≡ iso2 (V arH x )
                                          ≡ Var x
                                       (iso2 . iso1) (Op op)
                                          ≡ iso2 (OpH (Op (fmap iso1 op)))
                                          ≡ Op (fmap iso2 (fmap iso1 op))
                                          ≡ Op (fmap (iso2 . iso1) op)
                                          ≡ Op op
```

Furthermore, the handlers for these two recursive datatypes satisfy the following equivalence: foldAlg gen alg = hAlg gen (λ(Op op) → alg op). iso1.

```
hAlg gen (λ(Op op) → alg op) (iso1 (Var x ))
  ≡ hAlg gen (λ(Op op) → alg op) (V arH x )
  ≡ gen x
  ≡ foldAlg gen alg (Var x )
hAlg gen (λ(Op op) → alg op) (iso1 (Op x ))
  ≡ hAlg gen (λ(Op op) → alg op) (OpH (Op (fmap iso1 x )))
```

```
≡ (λ(Op op) → alg op)
 (hmap fold2 (fmap (hAlg gen (λ(Op op) → alg op)) (Op (fmap iso1 x ))))
≡ (λ(Op op) → alg op)
 (hmap fold2 (Op (fmap (hAlg gen (λ(Op op) → alg op) (fmap iso1 x )))))
≡ (λ(Op op) → alg op)
 (Op (fmap (hAlg gen (λ(Op op) → alg op)) (fmap iso1 x ))))
≡ alg (fmap (hAlg gen (λ(Op op) → alg op)) (fmap iso1 x )))
≡ alg (fmap (hAlg gen (λ(Op op) → alg op). iso1) x ))
≡ alg (fmap (foldAlg gen alg) x ))
≡ foldAlg gen alg (Op x )
```

Appendix C.2. Scoped Effects & Handlers

First, we define the isomorphisms:

```
iso1 :: Functor γ ⇒ F reeSc γ a → F reeH (KSc γ) a
iso1 (V ar x ) = V arH x
iso1 (Enter sc) = OpH (Enter (fmap (iso1 . fmap iso1) sc))
iso2 :: Functor γ ⇒ F reeH (KSc γ) a → F reeSc γ a
iso2 (V arH x ) = V ar x
iso2 (OpH (Enter sc)) = Enter (fmap (iso2 . fmap iso2) sc)
```

And next, we show that the requisite roundtrip properties hold, i.e., iso<sup>1</sup> . iso<sup>2</sup> = id = iso<sup>2</sup> . iso2.

```
(iso1 . iso2) (V arH x )
   ≡ iso1 (V ar x )
   ≡ V arH x
(iso1 . iso2) (OpH (Enter sc))
   ≡ iso1 (Enter (fmap (iso2 . fmap iso2) sc))
   ≡ OpH (Enter (fmap (iso1 . fmap iso1)) (fmap (iso2 . fmap iso2) sc))
   ≡ OpH (Enter (fmap (iso1 . fmap iso1 . iso2 . fmap iso2) sc))
   ≡ OpH (Enter (fmap (iso1 . iso2 . fmap iso1 . fmap iso2) sc))
   ≡ OpH (Enter (fmap (iso1 . iso2 . fmap (iso1 . iso2)) sc))
   ≡ OpH (Enter sc)
(iso2 . iso1) (V ar x )
   ≡ iso2 (V arH x )
   ≡ V ar x
```

```
(iso2 . iso1) (Enter sc)
   ≡ iso2 (OpH (Enter (fmap (iso1 . fmap iso1) sc)))
   ≡ Enter (fmap (iso2 . fmap iso2) (fmap (iso1 . fmap iso1) sc))
   ≡ Enter (fmap (iso2 . fmap iso2 . iso1 . fmap iso1) sc)
   ≡ Enter (fmap (iso2 . iso1 . fmap iso2 . fmap iso1) sc)
   ≡ Enter (fmap (iso2 . iso1 . fmap (iso2 . iso1)) sc)
   ≡ Enter sc
```

Furthermore, the handlers for these two recursive datatypes satisfy the following equivalence: foldSc gen alg<sup>E</sup> alg<sup>E</sup> = hSc gen (λ(Enter sc) → enter<sup>E</sup> alg<sup>E</sup> sc). iso<sup>1</sup> with return<sup>E</sup> alg<sup>E</sup> = η.

```
hSc gen (λ(Enter sc) → enterE algE sc) (iso1 (V ar x ))
   ≡ hSc gen (λ(Enter sc) → enterE algE sc) (V arH x )
   ≡ gen x
   ≡ foldSc gen algE algE (V ar x )
hSc gen (λ(Enter sc) → enterE algE sc) (iso1 (Enter sc))
   ≡ hSc gen (λ(Enter sc) → enterE algE sc)
             (OpH (Enter (fmap (iso1 . fmap iso1) sc)))
   ≡ (λ(Enter sc) → enterE algE sc)
                     (hmap fold2 (fmap (hSc gen (λ(Enter sc) → enterE algE sc))
                                        (Enter (fmap (iso1 . fmap iso1) sc))))
   ≡ (λ(Enter sc) → enterE algE sc)
                     (hmap fold2 (Enter (fmap (fmap (hSc gen
                          (λ(Enter sc) → enterE algE sc))))
                          (fmap (iso1 . fmap iso1) sc)))
   ≡ (λ(Enter sc) → enterE algE sc)
                     (hmap fold2 (Enter (fmap
                       (fmap (hSc gen (λ(Enter sc) → enterE algE sc)).
                          iso1 . fmap iso1) sc)))
   ≡ (λ(Enter sc) → enterE algE sc)
                     (Enter (fmap fold2
                       (fmap (fmap (hSc gen (λ(Enter sc) → enterE algE sc)).
                          iso1 . fmap iso1) sc)))
   ≡ enterE algE (fmap fold2 (fmap (fmap (hSc gen (λ(Enter sc) → enterE algE sc)).
                          iso1 . fmap iso1) sc))
   ≡ enterE algE (fmap (fold2 . fmap (hSc gen (λ(Enter sc) → enterE algE sc)).
                          iso1 . fmap iso1) sc))
   ≡ enterE algE (fmap (fold2 . fmap (hSc gen (λ(Enter sc) → enterE algE sc)).
                          fmap iso1 . iso1) sc))
```

```
≡ enterE algE (fmap (fold2 . fmap (hSc gen (λ(Enter sc) → enterE algE sc).
                       iso1). iso1) sc))
≡ enterE algE (fmap (fold2 . fmap (foldSc gen algE algE). iso1) sc))
≡ enterE algE (fmap (fold2 . iso1 . fmap (foldSc gen algE algE)) sc))
≡ enterE algE (fmap (hcata algE . fmap (foldSc gen algE algE)) sc))
≡ foldSc gen algE algE (Enter sc)
```

We need a helper lemma that states that hcata alg<sup>E</sup> = fold<sup>2</sup> . iso<sup>1</sup> with return<sup>E</sup> alg<sup>E</sup> = η.

```
hcata algE (V ar x )
   ≡ returnE algE x
   ≡ η x
   ≡ fold2 (V arH x )
   ≡ fold2 (iso1 (V ar x ))
hcata algE (Enter sc)
   ≡ (enterE algE . fmap (hcata algE . fmap (hcata algE))) sc
   ≡ (enterE algE . fmap (hcata algE . fmap (hcata algE))) sc
   ≡ (alg . Enter . fmap (hcata algE . fmap (hcata algE))) sc
   ≡ alg (Enter (fmap (hcata algE . fmap (hcata algE)) sc))
   ≡ alg (Enter (fmap (fold2 . iso1 . fmap (hcata algE)) sc))
   ≡ alg (Enter (fmap (fold2 . fmap (hcata algE). iso1) sc))
   ≡ alg (Enter (fmap fold2 (fmap (fmap (hcata algE). iso1) sc)))
   ≡ alg (hmap fold2 (Enter (fmap (fmap (hcata algE). iso1) sc)))
   ≡ alg (hmap fold2 (Enter (fmap (fmap (fold2 . iso1). iso1) sc)))
   ≡ alg (hmap fold2 (Enter (fmap (fmap fold2 . iso1 . fmap iso1) sc)))
   ≡ alg (hmap fold2 (Enter (fmap (fmap fold2) (fmap (iso1 . fmap iso1) sc))))
   ≡ alg (hmap fold2 (fmap fold2 (Enter (fmap (iso1 . fmap iso1) sc))))
   ≡ fold2 (OpH (Enter (fmap (iso1 . fmap iso1) sc)))
   ≡ fold2 (iso1 (Enter sc))
```

Appendix C.3. Parallel Effects & Handlers

First, we define the isomorphisms:

```
iso1 :: Functor ρ ⇒ F reePar ρ a → F reeH (KPar ρ) a
iso1 (V ar x ) = V arH x
iso1 (For iters k) = OpH (For (fmap iso1 iters) (fmap iso1 k))
iso2 :: Functor ρ ⇒ F reeH (KPar ρ) a → F reePar ρ a
iso2 (V arH x ) = V ar x
iso2 (OpH (For iters k)) = For (fmap iso2 iters) (fmap iso2 k)
```

And next, we show that the requisite roundtrip properties hold, i.e., iso<sup>1</sup> . iso<sup>2</sup> = id = iso<sup>2</sup> . iso2.

```
(iso1 . iso2) (V arH x )
   ≡ iso1 (V ar x )
   ≡ V arH x
(iso1 . iso2) (OpH (For iters k))
   ≡ iso1 (For (fmap iso2 iters) (fmap iso2 k))
   ≡ OpH (For (fmap iso1 (fmap iso2 iters)) (fmap iso1 (fmap iso2 k)))
   ≡ OpH (For (fmap (iso1 . iso2) iters) (fmap (iso1 . iso2) k))
   ≡ OpH (For iters k)
(iso2 . iso1) (V ar x )
   ≡ iso2 (V arH x )
   ≡ V ar x
(iso2 . iso1) (For iters k)
   ≡ iso2 (OpH (For (fmap iso1 iters) (fmap iso1 k)))
   ≡ For (fmap iso2 (fmap iso1 iters)) (fmap iso2 (fmap iso1 k))
   ≡ For (fmap (iso2 . iso1) iters) (fmap (iso2 . iso1) k)
   ≡ For iters k
```

We define a handler for F reePar ρ a as follows:

```
data AlgPar ρ f = AlgPar {hVar :: ∀a . a → f a,
                           hFor :: ∀a b . ρ (f b) → (ρ b → f a) → f a }
foldPar :: (Functor ρ, Pointed f ) ⇒ (a → f b) → AlgPar ρ f → F reePar ρ a → f b
foldPar gen alg (V ar x ) = gen x
foldPar gen alg (For iters k) = hFor alg (fmap (foldPar (hVar alg) alg) iters)
                                        (foldPar gen alg . k)
```

Furthermore, we can prove that there is an isomorphism between the handlers hPar and foldPar: foldPar gen alg = hPar gen (λ(For iters k) → hFor alg iters k). iso1.

```
hPar gen (λ(For iters k) → hFor alg iters k) (iso1 (V ar x ))
   ≡ hPar gen (λ(For iters k) → hFor alg iters k) (V arH x )
   ≡ gen (V arH x )
   ≡ foldPar gen alg (V ar x )
```

```
hPar gen (λ(For iters k) → hFor alg iters k) (iso1 (For iters k))
     ≡ hPar gen (λ(For iters k) → hFor alg iters k)
                 (OpH (For (fmap iso1 iters) (iso1 . k)))
     ≡ (λ(For iters k) → hFor alg iters k)
       (hmap fold2 (fmap (fold gen (λ(For iters k) → hFor alg iters k))
                           (For (fmap iso1 iters) (iso1 . k))))
     ≡ (λ(For iters k) → hFor alg iters k)
       (hmap fold2 (For (fmap iso1 iters)
                           (fold gen (λ(For iters k) → hFor alg iters k). iso1 . k)))
     ≡ (λ(For iters k) → hFor alg iters k)
       (For (fmap fold2 (fmap iso1 iters))
            (fold gen (λ(For iters k) → hFor alg iters k). iso1 . k))
     ≡ hFor alg (fmap fold2 (fmap iso1 iters))
                 (fold gen (λ(For iters k) → hFor alg iters k). iso1 . k)
     ≡ hFor alg (fmap (fold2 . iso1) iters)
                 (fold gen (λ(For iters k) → hFor alg iters k). iso1 . k)
     ≡ hFor alg (fmap (foldPar (hVar alg) alg) iters)
                 (fold gen (λ(For iters k) → hFor alg iters k). iso1 . k)
     ≡ hFor alg (fmap (foldPar (hVar alg) alg) iters)
                 (foldPar gen alg . k)
     ≡ foldPar gen alg (For iters k)
We need a helper lemma that states that foldPar (hVar alg) alg = fold2 . iso1.
  fold2 (iso1 (V ar x ))
     ≡ fold2 (V arH x )
     ≡ η x
  fold2 (iso1 (For iters k))
     ≡ fold2 (OpH (For (fmap iso1 iters) (fmap iso1 k)))
     ≡ (λ(For iters k) → hFor alg iters k)
       (hmap fold2 (fmap fold2 (For (fmap iso1 iters) (iso1 . k))))
     ≡ (λ(For iters k) → hFor alg iters k)
       (hmap fold2 (For (fmap iso1 iters) (fold2 . iso1 . k)))
     ≡ (λ(For iters k) → hFor alg iters k)
       (For (fmap fold2 (fmap iso1 iters)) (fold2 . iso1 . k))
     ≡ hFor alg (fmap fold2 (fmap iso1 iters)) (fold2 . iso1 . k)
     ≡ hFor alg (fmap (fold2 . iso1) iters) (fold2 . iso1 . k)
     ≡ hFor alg (fmap (foldPar (hVar alg) alg) iters) (foldPar (hVar alg) alg . k)
     ≡ foldPar (hVar alg) alg (For iters k)
```

```
Appendix C.4. Writer Effect & Handler
```

First, we define the isomorphisms:

```
iso1 :: Functor ϕ ⇒ F reeWrite ϕ a → F reeH (KWrite ϕ) a
iso1 (V ar x ) = V arH x
iso1 (Exec op) = OpH (Exec ((iso1 . fmap (fmap iso1)) op))
iso2 :: Functor ϕ ⇒ F reeH (KWrite ϕ) a → F reeWrite ϕ a
iso2 (V arH x ) = V ar x
iso2 (OpH (Exec op)) = Exec ((iso2 . fmap (fmap iso2)) op)
```

And next, we show that the requisite roundtrip properties hold, i.e., iso<sup>1</sup> . iso<sup>2</sup> = id = iso<sup>2</sup> . iso2.

```
(iso1 . iso2) (V arH x )
   ≡ iso1 (V ar x )
   ≡ V arH x
(iso1 . iso2) (OpH (Exec op))
   ≡ iso1 (Exec ((iso2 . fmap (fmap iso2)) op))
   ≡ OpH (Exec ((iso1 . fmap (fmap iso1)) ((iso2 . fmap (fmap iso2)) op)))
   ≡ OpH (Exec ((iso1 . fmap (fmap iso1). iso2 . fmap (fmap iso2)) op))
   ≡ OpH (Exec ((iso1 . iso2 . fmap (fmap iso1 . fmap iso2)) op))
   ≡ OpH (Exec ((iso1 . iso2 . fmap (fmap (iso1 . iso2))) op))
   ≡ OpH (Exec op)
(iso2 . iso1) (V ar x )
   ≡ iso2 (V arH x )
   ≡ V ar x
(iso2 . iso1) (Exec op)
   ≡ iso2 (OpH (Exec ((iso1 . fmap (fmap iso1)) op)))
   ≡ Exec ((iso2 . fmap (fmap iso2)) (iso1 . fmap (fmap iso1)) op)
   ≡ Exec ((iso2 . fmap (fmap iso2). iso1 . fmap (fmap iso1)) op)
   ≡ Exec ((iso2 . iso1 . fmap (fmap iso2 . fmap iso1)) op)
   ≡ Exec ((iso2 . iso1 . fmap (fmap (iso2 . iso1))) op)
   ≡ Exec op
```

```
Appendix C.5. Latent Effects & Handlers
   First, we define the isomorphisms:
     iso1 :: F reeLat ζ ℓ a → F reeH (KLat ζ ℓ) a
     iso1 (Leaf x ) = V arH x
     iso1 (Node op l sub k) = OpH (Node op l (fmap (fmap iso1) sub) (fmap iso1 k))
     iso2 :: F reeH (KLat ζ ℓ) a → F reeLat ζ ℓ a
     iso2 (V arH x ) = Leaf x
     iso2 (OpH (Node op l sub k)) = Node op l (fmap (fmap iso2) sub) (fmap iso2 k)
And next, we show that the requisite roundtrip properties hold, i.e., iso1 . iso2 =
id = iso2 . iso2.
     (iso1 . iso2) (V arH x )
        ≡ iso1 (Leaf x )
        ≡ V arH x
     (iso1 . iso2) (OpH (Node op l sub k))
        ≡ iso1 (Node op l (fmap (fmap iso2) sub) (fmap iso2 k))
        ≡ OpH (Node op l (fmap (fmap iso1) (fmap (fmap iso2) sub)) (fmap iso1 (fmap iso2 k)))
        ≡ OpH (Node op l (fmap (fmap iso1 . iso2) sub) (fmap (iso1 . iso2) k))
        ≡ OpH (Node op l sub k)
     (iso2 . iso1) (Leaf x )
        ≡ iso2 (V arH x )
        ≡ Leaf x
     (iso2 . iso1) (Node op l sub k)
        ≡ iso2 (OpH (Node op l (fmap (fmap iso1) sub) (fmap iso1 k)))
        ≡ Node op l (fmap (fmap iso2) (fmap (fmap iso1) sub)) (fmap iso2 (fmap iso1 k))
        ≡ Node op l (fmap (fmap (iso2 . iso1)) sub) (fmap (iso2 . iso1) k)
        ≡ Node op l sub k
Appendix C.6. Bracketing Effect & Handler
   First, we define the isomorphisms:
     iso1 :: F reeRes a → F reeH KRes a
```

iso<sup>1</sup> (Bracket res) = Op<sup>H</sup> (Bracket (iso<sup>1</sup> (fmap (λ(x , y) → (iso<sup>1</sup> x , return (iso<sup>1</sup> y))) res)))

iso<sup>1</sup> (V ar x ) = V ar<sup>H</sup> x

```
iso2 (V arH x ) = V ar x
      iso2 (OpH (Bracket res)) = Bracket (iso2 (fmap (λ(x , y) → (iso2 x , iso2 (join y))) res))
And next, we show that the requisite roundtrip properties hold, i.e., iso1 . iso2 =
id = iso2 . iso2.
      (iso1 . iso2) (V arH x )
         ≡ iso1 (V ar x )
         ≡ V arH x
      (iso1 . iso2) (OpH (Bracket res))
         ≡ iso1 (Bracket (iso2 (fmap (λ(x , y) → (iso2 x , iso2 (join y))) res)))
         ≡ OpH (Bracket (iso1 (fmap (λ(x , y) → (iso1 x , return (iso1 y)))
                                        (iso2 (fmap (λ(x , y) → (iso2 x , iso2 (join y))) res)))))
         ≡ OpH (Bracket ((iso1 . fmap (λ(x , y) → (iso1 x , return (iso1 y))).
                             iso2 . fmap (λ(x , y) → (iso2 x , iso2 (join y)))) res))
         ≡ OpH (Bracket ((iso1 . iso2 .
                             fmap (λ(x , y) → ((iso1 . iso2) x ,(return . iso1 . iso2 . join) y))))
                             res))
         ≡ OpH (Bracket ((fmap (λ(x , y) → (x ,(return . join) y)))) res))
         ≡ OpH (Bracket (fmap (λ(x , y) → (x , y))) res))
         ≡ OpH (Bracket res)
      (iso2 . iso1) (V ar x )
         ≡ iso2 (V arH x )
         ≡ V ar x
      (iso2 . iso1) (Bracket res)
         ≡ iso2 (OpH (Bracket (iso1 (fmap (λ(x , y) → (iso1 x , return (iso1 y))) res))))
         ≡ Bracket (iso2 (fmap (λ(x , y) → (iso2 x , iso2 (join y)))
                     (iso1 (fmap (λ(x , y) → (iso1 x , return (iso1 y))) res))))
         ≡ Bracket ((iso2 . fmap (λ(x , y) → (iso2 x , iso2 (join y))).
                       iso1 . fmap (λ(x , y) → (iso1 x , return (iso1 y)))) res)
         ≡ Bracket ((iso2 . iso1 .
                       fmap (λ(x , y) → ((iso2 . iso1) x ,(iso2 . join . return . iso1) y)))
                       res)
         ≡ Bracket ((fmap (λ(x , y) → (x ,(iso2 . iso1) y))) res)
         ≡ Bracket (fmap (λ(x , y) → (x , y)) res)
```

iso<sup>2</sup> :: F ree<sup>H</sup> KRes a → F reeRes a

≡ Bracket res