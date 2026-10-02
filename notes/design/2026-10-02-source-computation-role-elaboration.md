# Source elaboration: computation roles and unknown constructors

Date: 2026-10-02
Status: Draft; scoped role theorems, source map and obstruction package reviewed; full source elaboration remains open; not implementation authority
Scope: computation/value role separation, source-template generation, and the remaining finite symbolic bridge
Approved-by: none for the elaboration candidate; charter §§11–15 govern selected source behavior
Drafted-by: primary with bounded architect construction and counterexample audit
Reviewed-by: compiler_referee and spec_auditor, 2026-10-02; no blocking/major findings; two minor scope/priority clarifications closed by primary
Role-candidate-review: compiler_referee and spec_auditor, 2026-10-02; §§6–9 clean after one minor role-versus-adaptation clarification; immutable source locators mapped by explorer, not independently audited by these reviewers
Supersedes: none; the fixed-shape value-adapter theorem keeps its original scope

## 1. Milestone target and existing inputs

The reviewed decorated machine derives request observation from executing
typed view positions before handler filtering. It still takes those positions,
original profile slots and monomorphic type endpoints as input. The next
source theorem must construct them and close their symbolic queries; renaming
that input to a new `Route` or consumer oracle would not do so.

This package establishes a constraint on that construction: executing a
computation and adapting its result value cannot be identified by their
resolved constructor pair. It also refutes a proposed finite-source-producer
shortcut. Neither result is a class-3 non-finiteness proof, and no accepted
source envelope is narrowed. Soundness/principality and the final-acceptance
target remain unchanged.

Shallow handling is primitive, with selection, matching and arms outside.
Deep behavior expands to explicit shallow reapplication to resumed
computation. The expansion requires no extra primitive in this elaboration.
The new ordinary-computation §5 expansion law is independent of the unknown
source-shape construction discussed here.

## 2. A computation result may itself be latent

After its identity-first equivalence test fails, the typed-boundary
value-adapter kernel has the clause

```text
Adapt(Thunk(E,A), Thunk(F,B), t)
  = Return(Delay(Force(t) >>= Adapt(A,B)))
    when Thunk(E,A) ≉g Thunk(F,B)
```

Consider a consumer whose intended operation is to execute a computation
represented by `t : Thunk(E,A)` and obtain its result **as a value of A**.
If `A=Unit`, the pair `(Thunk(E,A),A)` follows the force-to-value branch.
If `A=Thunk(F,B)` and the pair fails that identity test, it instead follows
the displayed thunk-to-thunk branch:

```text
Adapt(Thunk(E,Thunk(F,B)), Thunk(F,B), t)
  = Return(Delay(Force(t) >>= Adapt(Thunk(F,B),B)))
```

Choose distinct effect families `E,F`, an outer computation that emits `E`
then returns a latent `F` thunk, and non-thunk `B=Unit`. The intended execution
emits `E` now and returns that latent value. The constructor-pair adaptation
emits nothing now; a subsequent force emits `E` and then forces the inner
`F` computation. An `F`-only target contract cannot validate that delayed
`E+F` behavior. The existing adapter theorem already requires validation of
the whole delayed computation, so this does not refute that theorem.

This argument uses an actual computation with the stated requests. It does
not infer emission merely from a row upper bound: the same execution rule
must also handle an `E`-bounded computation that returns without a request.
Nor does it claim that both raw Yulang spellings have been accepted by an
as-yet undefined source typing judgment. It proves that a computation
consumer with this meaning cannot be implemented by the value-adapter pair
alone, including in the presence of a latent result.

In particular, choosing `NonThunk(A)` for every result would exclude the
latent values whose typed result paths the user explicitly wants to retain.
Strict data elimination, such as scrutinizing a value with a pattern, is a
different use of the common relation from executing a computation that
returns an arbitrary `A`.

## 3. One computation/value relation with role-preserving execution

Use `Comp(E,A)` to name the already existing computation interface: executing
it produces a value of `A` with requests bounded by `E` and their full
resumption/family relation. This is a mathematical judgment role, not a new
surface type constructor, selector, linear resource or extra capture right.
`Thunk(E,A)` is the latent value holding such a computation.

For an explicitly identified computation role the elimination equation is:

```text
Execute(Comp(E,A), t) = Force(t)
Complete(Comp(E,A), T, t) = Execute(Comp(E,A),t) >>= ValueAdapt(A,T)
```

`Force` and bind have their existing ordinary semantics. The result value
does not execute merely because its type `A` is a thunk. `ValueAdapt` is the
existing value-conversion relation when that conversion is admitted; it
retains its own identity/force/delay/function clauses and proof boundary.
In the no-result-conversion instance, completion is
`Force(t) >>= Return`, for every result type `A`.

**Role-preservation theorem for `Execute`.** Once the source judgment
identifies the outer computation role, `Execute` (equivalently completion
without result conversion) preserves its complete execution and returns its
result as a value without adding a demand on that returned value's descendant
latent positions. This holds uniformly in `A`, including a thunk, function,
recursive value graph or a symbolic endpoint later assigned one of those
shapes. General `Complete` then performs its separately admitted `ValueAdapt`,
which may legitimately force the result; the theorem does not remove those
additional adapter effects.

Proof is the common computation relation, not a row equation. If forcing
returns `(a,C)`, bind's return equation returns that same value and live
state. If it yields `Request(q,C,k)`, bind retains that exact event, origin,
typed payload and symbolic `K,D`, with continuation `k >>= Return`.
Induction over finite resumed prefixes gives the same result after every
admissible raw resumption. The algorithm does not inspect `A`'s outer tag,
so substituting a different result shape cannot change this execution step.
This is uniformity of this operation under preserved typing premises, not
the unproved solver/generalization/intrusion substitution theorem.

Executing the rule inside a declared complete `View` supplies its current
emission-context observation. Typed result transport carries only the result
positions when `a` is returned. Thus a later execution of latent `a` uses its
own view and original result-path profile, without copying the executed
outer computation's annotation. If a shallow handler surrounds the execution,
its image sees the requests actually emitted there; if the execution is
outside it, the image does not. These conclusions follow from the existing
context projection and handler composition, independently of the tag of `A`.
No new grant, origin test or per-source-site effect rule is needed.

This theorem does not choose whether a raw expression denotes a computation
to execute or a latent value to transport. Deriving that role from source
typing is still essential. It identifies what the derivation must preserve
and rejects constructor-only recovery of the role after solving.

## 4. Source-template generation versus solved executable positions

A proposed common elaboration separates synthesis, checking against a
consumer type, and rigid value elimination. Expression syntax generates
producer/consumer constraints and code by the same state-threaded bind:

```text
checking a produced value:     Run(e) >>= ValueAdapt(S,T)
executing an identified Comp:  Run(e) >>= Execute(Comp(E,A))
then checking its result:      ... >>= ValueAdapt(A,T)
```

Application has a function consumer and argument/result checks; a pattern
scrutinee has the value shape required by its patterns; lambda/delay
construction stores body code and does not run it. Annotations retain their
original occurrence identities, separated from inferred row support. A
handler surrounds the chosen body computation, with selector and arm code
outside; a body that intentionally returns a latent value does not
unconditionally execute that value. These are requirements for a candidate
judgment, not a finished inference-rule set or an approved change to source
acceptance.

For a finite syntax graph, collecting lexical producer sites, consumer sites,
lambda/delay bodies, operation lookup sites, handler arms and explicit
annotation occurrences is finite. Structural traversal allocates at most a
fixed number of such templates per syntax constructor and follows recursive
bindings by references. Induction on finite syntax establishes this count;
runtime allocation or resumption reuses those sites. An original annotation
slot can retain `(boundary introduction site, annotation occurrence)` rather
than an inferred family name.

This proves only finite syntax templates. It does not yet assign every
annotation its computation/result role, generate omitted-protection profiles,
derive all expected consumer types, or prove a finite solved constructor graph.
In particular, counts of annotation syntax alone do not account for inferred
signature positions. The source-role judgment must supply those facts without
copying annotations across unrelated result paths.

## 5. Why initial source producers do not close the unknown-shape gate

For source-created values, associating each allocation site with a constructor
and symbolic child endpoints is a useful invariant: repeated allocation need
not create another static type endpoint. That does not cover values created
by adaptation itself. The existing equations include:

```text
Adapt(Unit, α, ())
ν(α) = Thunk(E₁, Thunk(E₂, ... Thunk(Eₙ, Unit)...))
```

For every finite `n`, the non-thunk-to-thunk branch creates a delayed wrapper;
its future force executes the remaining adaptation and creates the next
wrapper. There was no source thunk producer in this boundary command.
Consequently the initial source producer inventory does not contain every
constructor position inspected or constructed by these equations. The dual
`Adapt(α,Unit)` family already recorded in typed-boundary §5 needs arbitrarily
many payload positions and forces.

These are exact families of the candidate boundary equations. Their raw-source
admissibility and any constraints restricting `α` remain unproved. They refute
the unconditional producer-only shortcut, not finite presentations in general.
In particular "extra assignment shapes are uninhabited" is insufficient:
adaptation can construct their inhabitants. Normalizing such assignments
away requires preservation of the principal observable relation and accepted
conversions, not just a count of lexical constructors.

One recursive adapter instruction can represent all these finite unfoldings
as code. Its changing type-position cursor and any generated symbolic queries
are not thereby elements of the fixed finite `T/PΩ` basis. Conversely, failure
of that particular basis does not establish a class-3 obstruction. The
possible regular/parametric presentation is still to be constructed and proved.

## 6. Source evidence: a computation slot is not a runtime constructor

The following is characterization at frozen commit `a58eefc3`, not semantic
authority. It constrains any claim of source coverage by a replacement
judgment. The paths below are relative to that immutable revision.

| Source position | Characterized representation | Locator |
|---|---|---|
| `() -> [E] A` | Function with separate `ret_eff=E` and result `A` | `crates/infer/src/annotation/builder.rs:123–143,409–413` |
| `[E] A` parameter | Separate parameter computation effect and value constraints | `crates/infer/src/annotation/constraints.rs:251–284` |
| `[E] A` expression/binding annotation | Separate outer computation effect and value constraints | same file, `223–248` |
| Explicit latent function result `() -> [E] (() -> [F] A)` | Nested Function keeps its own call-effect slot | builder `123–143,268–273`; structural derivation, not an executed fixture |
| Nested effectful result `[E] ([F] A)` | Builder retains nested `Effectful`, but value-bound lowering recursively strips its row | constraints `334`; nesting is not evidence for a preserved latent contract |
| `\() -> body` and `f()` | Explicit unit Function construction and ordinary invocation | `crates/infer/src/lowering/expr/tail.rs:455–476`; `lib/std/text/parse.yu:252–257` |

There is no dedicated source `Force`, `Delay`, `Perform`, or pure `Return`
in the inspected parser/poly-expression map. Surface `return` is a standard
`sub` operation (`lib/std/control/flow.yu:1–5`), not the mathematical return
constructor. The downstream runtime `Type::Thunk` is formed from an
effect/value pair (`crates/specialize/src/types/mod.rs:419–433`). It must not
be identified with either the explicit unit Function or an arbitrary source
value-type constructor without a representation proof.

Ordinary local binding completes the RHS and stores its result. Lowering
contributes `body.effect` to the statement and generalizes `body.value`
(`crates/infer/src/lowering/expr/block_local.rs:545–590`); the bound local
gets `effect: None` (`1225–1263`) and lookup has pure effect
(`crates/infer/src/lowering/name_ref.rs:146–186`). Specialization demands
the RHS result value (`crates/specialize/src/solve/expr_solver/control.rs:
232–268`), and runtime `Let` evaluates then binds it
(`crates/mono-runtime/src/runtime/eval.rs:620–639`); local lookup reads the
stored value (`12–18`). `BindingFetch` controls generalization/value
restriction (`crates/infer/src/lowering/expr/tail.rs:944–989`), not replay or
memoization of a deferred computation. A returned value may still have its
own latent behavior.

Computation-bearing parameters are different. The existing source
`examples/10_effect_handler.yu:13–17` passes `add_and_say()` to
`listen(x: [_] _, log: str)`, whose body is `catch x`. No unit closure wraps
the argument. The effectful parameter boundary retains its computation
carrier (`crates/specialize/src/solve/expr_solver.rs:363–372`); `catch`
demands its result inside the handler (`control.rs:37–39`). Runtime applies
an operation by constructing `Thunk::Effect`
(`crates/mono-runtime/src/runtime/flow.rs:29–32`) and emits the request when
forcing it (`runtime/thunk.rs:124–125`). Consequently a judgment that eagerly
completes **every** argument before receiver entry cannot claim to preserve
this computation-passing capability.

These facts support deriving roles at typed source positions. They neither
approve reproducing every frozen conversion nor establish a source rule for
arbitrary nested effectful results. That rule cannot be justified by the AST
builder alone when its later constraint lowering discards the inner row.

## 7. Why a disjunction of lifting and exposure is not enough

Consider these possible checking rules, not selected successor rules:

```text
e : A             ==> e : Comp(empty,A) via Return(e)
e : Thunk(E,A)    ==> e : Comp(E,A)     via Force(e)
Comp(E0,A), E0<=E ==> Comp(E,A)        via effect weakening
```

In the regular candidate value kernel let `A = Thunk(E,A)` and let a finite
recursive producer be

```text
make() = Delay(emit E >>= lambda _. make())
t = make()
```

Each force emits one `E` and returns another delayed value of `A`. At the
**same assignment**, checking `t` against `Comp(E,A)` can use pure lifting
and weakening to return `t` without a request, or exposure to emit `E` and
return a latent value of `A`. The row is an upper bound permitting both
behaviors. It does not require emission. Retaining both constraint solutions
does not choose a coherent elaboration of one source expression: the two
programs have observably different current effects.

This is a finite regular counterexample to deriving execution roles solely
from solved value types plus those overlapping rules. It is not a proved
well-typed raw Yulang program, a class-3 non-finiteness result, or a
counterexample to a role-separated source judgment. In particular the runtime
`Thunk` equation cannot silently be assumed to be a source value equation.
The result says that a role derivation must precede this representation
collapse, and that principal constraint solutions alone do not prove
elaboration coherence.

## 8. A sorted elaboration candidate

Separate source value endpoints from computation interfaces before choosing
their runtime representation:

```text
V ::= base | Fun(P, Comp(E,V)) | structural values | alpha_value
P ::= Value(V) | Computation(E,V)
Gamma |- e => Comp(E,A) ~> c
```

These are mathematical sorts and binding/parameter descriptors, not proposed
surface keywords. `c` denotes executable computation code. The internal
runtime `Thunk` implements a retained computation; it is not assumed to be
an arbitrary constructor of `V`. Parameter roles include computation-bearing
parameters rather than forcing all arguments before receiver entry.

The following rules define a candidate for a role-annotated ordinary
fragment. They are not yet a total elaboration of raw Yulang syntax:

| Form / role | Computation code |
|---|---|
| Literal | `Return(literal)` |
| Variable bound as `Value(A)` | `Return(stored value)` |
| Variable bound as `Computation(E,A)` | `Force(stored carrier)` |
| Ordinary local `my x = e; body` | `c_e >>= lambda v. c_body[x := Value(v)]` |
| Lambda with parameter role `P` | `Return(Closure(body code, environment))` |
| Application | `c_callee >>= lambda f. Prepare_P(argument) >>= lambda x. Call(f,x)` |

`Call` is the existing call/body/result composition inside its derived typed
view, including any admitted argument/result adapters. For an operation it
constructs the existing request carrier and executes that identified
computation. Construction and emission remain separate kernel steps. These
rules do not recover the computation/value role by inspecting a result value's
solved constructor. Separately admitted `ValueAdapt` remains constructor
sensitive and may force a latent result, with its own resulting requests.
All sequencing uses the common state-threaded bind.

Two candidate preparation equations make the role distinction explicit:

```text
Prepare_Value(A)(e) = c_e >>= ValueAdapt(A_e,A)
Prepare_Computation(E,A)(e)
  = Return(Delay(c_e >>= ValueAdapt(A_e,A)))
```

The second requires inclusion of the complete delayed interface in the
parameter contract, not just inclusion of immediate row support. Both
equations retain the original typed packets and adapter correspondences.
Inclusion and admission of `ValueAdapt` remain proof premises. In particular,
the second equation is a **candidate scheduling choice**, not a demonstrated
simulation of the frozen argument boundary: it delays all of `c_e`.
Frozen execution evaluates an argument carrier before receiver entry, and
that construction may diverge or execute earlier computation. A representation
proof must either factor the same construction before retention or justify
the scheduling difference from independent source semantics. Effect purity
alone cannot justify moving divergence or stateful computation. No scheduling
change is approved by this document.

Explicit computation parameter annotations supply a `Computation` role;
ordinary value annotations supply a `Value` role. A function's immediate
return annotation supplies its result computation contract. Each original
annotation slot retains
`(boundary site, annotation occurrence, role projection)`. An annotated
returned Function has its own corresponding call-effect slot, not a copy of
the outer call annotation. Inferred parameter roles and omitted-protection
positions still require derivation; they cannot be recovered from family
support or selected arbitrarily to fit a runtime fixture. Nested effectful
value annotations and the characterized deferred polymorphic local need
coverage/normalization rules before claiming full source acceptance.

**Conditional role-coherence and template theorem.** For a finite ordinary
syntax graph with fixed parameter/binding roles and fixed admitted adapter
descriptors, these rules generate a finite computation skeleton with unique
choices of value lookup, computation execution and argument retention.
These choices are invariant under assignments to the value endpoints that
preserve the roles. This is uniqueness of the role-directed control skeleton,
not uniqueness of arbitrary adapters, effect solutions or source execution.

Proof is structural induction. A literal or lookup adds one command, with
lookup selected by its environment descriptor. A lambda records its finite
body without executing it. A local binding composes the two subderivations
and installs the result as a value. An application composes its callee and
argument with the one preparation selected by its fixed parameter descriptor.
Recursive references return to existing syntax sites. Explicit annotation
occurrences add finitely many original slots; assignments do not add syntax
occurrences or convert a value endpoint into a computation role. Consequently
regular value equality cannot reproduce §7's overlapping lookup rules.
Runtime occurrences can still be unbounded, and none of this bounds newly
generated solved constructor positions or proves a finite query closure.

Within that decorated fragment, an imported computation lookup inside a
callback is `Force(t)` in its current complete view. A direct operation
application executes its identified request carrier in that same view.
The existing visibility relation therefore treats exposed requests equally
under the same concrete contract; their different origins, event identities
and symbolic `K,D` remain intact. This consequence assumes the view and typed
path correspondence supplied by the derivation. It is not a proof that every
raw callback expression has such an elaboration. Arbitrary returned values
are preserved by §3; later latent Function calls use their own typed paths.
Shallow selection, patterns/guards and arms use the outside relation; deep
handling continues to expand into explicit shallow reapplication.

The conceptual benefit over untyped constructor-driven adaptation is one
computation/value distinction for local completion, argument retention and
callback execution. Its cost is an explicit source-role and scheduling
derivation. It avoids introducing per-site handler rules. Its principality,
source coverage and representation simulation remain unproved. In particular,
the runtime thunk-tower family in §5 does not automatically refute a sorted
source representation; eliminating it requires the missing normalization and
acceptance bridge, not merely restricting the spelling of `alpha_value`.

## 9. Next construction and decision boundary

The economical candidates are:

| Candidate | Exact missing theorem |
|---|---|
| Principal normalization of constructor/consumer constraints into finite regular solved graphs | Every retained assignment/behavior has a solution-complete normalized representative; no relevant adaptation or family constraint is lost |
| Parametric recursive adapter presentation retaining unknown shapes | Type-position traversal, contract slots and symbolic predicates have a finite representation with effective principal solving and joint family transport |

Both reuse the computation/value relation and typed path transport. Neither
is selected or proved here. Eager unfolding and treating unknown endpoints as
rigid atoms fail the existing boundary families. Forcing every nested thunk
fails the computation-result theorem. Choosing one merely because it mirrors
the frozen implementation is not justified.

The next source package must complete the producer/consumer typing rules,
inferred annotation-role derivation, scheduling/representation simulation and
admitted conversions, then prove one of these representation routes. Section
8 constructs a role-annotated candidate; it does not discharge its missing
raw-source premises. The characterized strict case behavior is a reasonable
compatibility candidate; it is not independent authority for all consumers.
Potentially removing `≈` as an operational choice by proving identity/η
coherence is a separate simplification, not an established result: equal
undecorated shapes alone do not prove preservation of view/receipt evidence.

There is no user decision requested by this document. The completed judgment
and its alternatives should be reviewed as a whole source-semantics gate,
instead of asking for a new site-specific rule at each gap. Full source
soundness/principality, modular client coverage, lifecycle and implementation
remain open; this package must not be used to declare Milestone 3 complete.
