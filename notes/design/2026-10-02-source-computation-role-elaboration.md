# Source elaboration: computation roles and unknown constructors

Date: 2026-10-02
Status: Draft; scoped role theorems, corrected active source map, obstruction and invocation-entry package reviewed; full source elaboration remains open; not implementation authority
Scope: computation/value role separation, source-template generation, and the remaining finite symbolic bridge
Approved-by: none for the elaboration candidate; charter §§11–17 govern the source reference and selected behavior
Drafted-by: primary with bounded architect construction and counterexample audit
Reviewed-by: compiler_referee and spec_auditor, 2026-10-02; no blocking/major findings; two minor scope/priority clarifications closed by primary
Historical role-candidate review (de7bfd0a7): compiler_referee and spec_auditor, 2026-10-02; former §§6–9 clean after one minor role-versus-adaptation clarification; immutable source locators mapped by explorer, not independently audited in that round
Production/entry-review: compiler_referee and spec_auditor, 2026-10-02; corrected active code paths and placement obstruction checked; new-user-premise entry delta reviewed; operation-payload gap repaired and closed by independent compiler_referee; prior §8 skeleton is historical
Introduction/elimination review: independent compiler_referee and spec_auditor, 2026-10-02; no findings in §§3/10–12 and their source-law/exact-interface dependencies; raw-source elaboration and finite principality remain open
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

For an explicitly identified **source consumer of a computation**, the
elimination equation is:

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

Charter §17 fixes the introduction/elimination distinction: these equations
describe an already justified consumer. Merely holding a `Comp`/`Thunk`
interface, looking up a computation-valued name or returning computation data
does not invoke `Execute` or `Complete`. Representation metadata and result
shape cannot supply a missing source elimination. Admitted adapters likewise
need a source consumer derivation, not only a matching constructor pair.

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

Ordinary local binding completes the RHS and stores its result **when its
containing computation executes**. Lowering
contributes `body.effect` to the statement and generalizes `body.value`
(`crates/infer/src/lowering/expr/block_local.rs:545–590`); the bound local
gets `effect: None` (`1225–1263`) and lookup has pure effect
(`crates/infer/src/lowering/name_ref.rs:146–186`). Runtime `Let` evaluates
then binds its RHS
(`crates/mono-runtime/src/runtime/eval.rs:620–639`); local lookup reads the
stored value (`12–18`). `BindingFetch` controls generalization/value
restriction (`crates/infer/src/lowering/expr/tail.rs:944–989`), not replay or
memoization of a deferred computation. An enclosing effectful block can be
delayed as a whole, including that local binding. A returned value may still
have its own latent behavior.

Computation-bearing parameters are different. The existing source
`examples/10_effect_handler.yu:13–17` passes `add_and_say()` to
`listen(x: [_] _, log: str)`, whose body is `catch x`. No unit closure wraps
the argument. Production argument preparation distinguishes value consumption
from computation passage (`crates/specialize/src/specialize2/task_solver.rs:
492–513`), and emission attaches the argument boundary before application
(`specialize2/emit.rs:248–266`). Runtime applies
an operation by constructing `Thunk::Effect`
(`crates/mono-runtime/src/runtime/flow.rs:29–32`) and emits the request when
forcing it (`runtime/thunk.rs:124–125`). Consequently a judgment that eagerly
completes **every** argument before receiver entry cannot claim to preserve
this computation-passing capability.

These facts support deriving roles at typed source positions. They neither
approve reproducing every frozen conversion nor establish a source rule for
arbitrary nested effectful results. That rule cannot be justified by the AST
builder alone when its later constraint lowering discards the inner row.

**Active-path correction.** The public specialization entry delegates to
`specialize2` (`crates/specialize/src/lib.rs:77–81`). Earlier versions of this
section cited `solve/expr_solver` and `lib_support` for production scheduling;
those paths are retained alternate machinery. The infer and runtime facts
above remain applicable, but they do not determine where production emission
inserts the enclosing thunk. Section 9 gives the corrected active path. The
inference field `Computation.evaluation` is expansiveness/value-restriction
information, not a third effect phase (`crates/infer/src/typing.rs:12–23,
58–66`). No new semantic stage follows from that field's name.

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

## 8. Prior sorted elaboration candidate (invocation replaced by §10)

This section retains the fixed-role construction as an audit of the earlier
candidate. The user's subsequent source-reference clarification in charter
§16 places value-parameter force/rebinding at invocation entry. Its pre-call
`Prepare_Value` rule is therefore not the source baseline. Section 10 replaces
that part with one computation-receiving invocation; §9 also withdraws its
uniform-retention scheduling as a general preservation law.

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

The initial candidate used these preparation equations to expose the role
distinction. Their uniform-retention scheduling is not adopted; §9 supplies
a concrete kernel counterexample to using it as a general lowering law:

```text
Prepare_Value(A)(e) = c_e >>= ValueAdapt(A_e,A)
Prepare_Computation(E,A)(e)
  = Return(Delay(c_e >>= ValueAdapt(A_e,A)))
```

The second requires inclusion of the complete delayed interface in the
parameter contract, not just inclusion of immediate row support. Both
equations retain the original typed packets and adapter correspondences.
Inclusion and admission of `ValueAdapt` remain proof premises. In particular,
the second equation delays all of `c_e`. This loses the construction position
of an already carrier-producing expression. Conversely, evaluating every
producer before retention fails to reproduce the active pure-to-thunk lifting
branch. A representation proof must derive the placement of producer code
and adapters, or justify a difference from independent source semantics.
Effect purity alone cannot justify moving divergence or stateful computation.
No scheduling change is approved by this document.

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

**Historical conditional skeleton theorem.** For a finite ordinary
syntax graph with fixed parameter/binding roles and fixed admitted adapter
descriptors, these rules generate a finite computation skeleton with unique
choices of value lookup, computation execution and argument retention.
These choices are invariant under assignments to the value endpoints that
preserve the roles. This is uniqueness of the role-directed control skeleton,
not uniqueness of arbitrary adapters, effect solutions or source execution.
It concerns the illustrative skeleton with its preparation equations fixed;
it does not certify those equations as intended source scheduling. In
particular it supplies no current argument-retention or force-placement
theorem after the source-reference correction in §10.

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

## 9. Producer construction and retention are not interchangeable

### Active production evidence

All locators in this subsection refer to frozen `a58eefc3`. They characterize
evaluation placement, not Oracle weight routing or source semantic authority.

An effectful block becomes an executable raw computation in
`crates/specialize/src/specialize2/task_solver/control.rs:191–264`.
`specialize2/emit.rs:363–367,765–782` attaches its computation shape without
yet allocating a thunk. At a function result boundary,
`emit.rs:723–749` checks it against the runtime return shape, constructed
from the function's effect/value pair (`runtime_shape.rs:64–74`). When that
shape is `Thunk(E,A)`, `emit.rs:865–880` and
`runtime_shape.rs:823–842` put the **whole emitted block** in `MakeThunk`.

For example, `lib/std/io/net.yu:38–40` has the body shape

```text
serve(port) =
  my listener = listen port
  server::accept listener
```

Its emitted body returns the block carrier on closure application. Runtime
`MakeThunk` retains code/environment without evaluating the block
(`crates/mono-runtime/src/runtime/eval.rs:36–40`); forcing it enters the body
(`runtime/thunk.rs:122`), where the local binding then completes before the
tail. This is a structural trace of the mapped production path, not a newly
executed fixture. Strict runtime `Let` does not imply an eager source block
prelude at closure application.
These runtime carrier-building stages must not be identified with source
invocation entry without the representation mapping; §10 states the user's
source reference independently of that emitted placement.

Ordinary runtime application evaluates its callee, then its argument, then
applies the value (`runtime/eval.rs:84–94`). Source application whose
preparation has effects may itself become a raw computation
(`specialize2/task_solver.rs:562–567`), so an enclosing boundary can delay
that whole application. Direct operation application is a different producer:
the operation branch consumes its payload as a value and does not mark the
application raw (`task_solver.rs:572–588`); its emitted value already has the
carrier shape (`runtime_shape.rs:558–559`). With an equivalent target carrier,
the boundary leaves the expression in place (`emit.rs:865–867`). Its payload
is evaluated before runtime constructs `Thunk::Effect`.

Pure-expression lifting supplies the converse discriminator. For an emitted
`g():Unit` checked against the specified target `Thunk(E,Unit)`, the same
boundary checks the expression against the result `Unit`, leaves that code
unchanged, and places it directly in `MakeThunk.body`
(`emit.rs:865–880,911–924`; `runtime_shape.rs:837–840`). It does not first
evaluate `g()` and wrap its returned value. `EmittedExpr::pure` still has a
`ComputationShape(pure,value)`; the optional shape is not a raw-versus-carrier
tag (`specialize2/mod.rs:139–165`). These are expression-level code placements,
not the value-adapter equations of typed-boundary §4 applied after evaluation.

This last statement is conditional on that boundary's supplied target. It
does not establish a well-typed raw-source instance fixing a nonpure target
for pure `g()`: the consumer effect is constrained from the actual expression
(`specialize2/task_solver.rs:335–341`) and may normalize to pure. Nor has this
audit established two accepted same-annotation expressions that emit outward
requests at different construction phases. Those stronger claims are not
needed for the following kernel non-equivalence.

### A code-placement obstruction, independent of routing

Let `p` be a computation that **produces a carrier**, and let `d` be its
admitted result adapter. The following expression-level compositions differ:

```text
retain after construction:
  p >>= lambda t. Return(Delay(Force(t) >>= d))

delay construction too:
  Return(Delay(p >>= lambda t. Force(t) >>= d))
```

Choose `p = Run(g()) >>= lambda a. Return(MakeRequestThunk(op,a))` in the
carrier-construction kernel, with a pure diverging `g` of the payload type.
The internal constructor takes the acquired typed payload; it is not a public
operation invocation taking a computation argument. Choose an operation whose
result type is `Unit` and identity `d`. The first expression diverges during construction;
the second returns a delayed carrier immediately. A continuation that discards
the produced carrier and returns `Unit` distinguishes them. The operation
need not emit any request for this distinction. Source effect bounds do not
imply termination, so a pure construction row cannot justify the rewrite.

This is a concrete kernel counterexample, supported by the direct-operation
production recipe. It is not claimed to be an executed/accepted Yulang
program, a counterexample to every sorted elaboration, or a class-3
non-finiteness result. The same counterexample distinguishes an existing
carrier producer `p` from §8's uniform `Delay(Execute(e))` retention. The
pure-to-thunk branch above separately rules out treating evaluate-then-wrap
as the characterized behavior for every source producer.

The exact conceptual boundary is **code adaptation versus value adaptation**.
The fixed-shape adapter theorem takes an already produced value. Inserting
that theorem around an arbitrary expression additionally requires proving
where its producer executes. Equality of type endpoints, finite role tags,
or the existence of an adapter descriptor does not discharge that requirement.
In particular, a thunk-to-thunk nonidentity adapter cannot automatically be
assumed to evaluate its producer first; the surrounding expression boundary
also has to be derived.

### Consequence for the successor construction

Keep producer code, bind positions and delay positions in the same ordinary
computation graph. Derive their placement from one source elaboration relation;
do not recover it from a runtime carrier tag after solving. Retained code
keeps its lexical references and typed value-path packets, not a snapshot of
the live store or active handlers. When executed, its existing view/owner
delimiters and raw-resumption rule determine current visibility. Delaying or
advancing that code across a receiver/handler boundary needs a preservation
theorem for the complete relation, including divergence and future uses.

A runtime `Ready/Susp` split was considered during construction, but adds no
missing source-placement proof: evaluating every `Build(e)` before retention
already chooses a schedule and disagrees with the characterized pure lift.
It is not adopted as a new successor construct. A static producer distinction
may be useful bookkeeping, but no whole-source lowering or principality
theorem follows merely from assigning that distinction a name. The corrected
active production map replaces the earlier scheduling premise; source
normalization and representation simulation remain the genuine open gate.

## 10. One invocation relation: receive, entry, body

The user clarified the intended Oracle semantics: **every function is a
handler; an ordinary pure function forces and rebinds its input at the very
start of activation**. Charter §16 records this source reference. It removes
the need for separate source call mechanisms for value and computation
parameters. The pre-call value-force rule in §8 is superseded as a source
candidate by the following entry expansion.

After inert whole-argument reification has produced carrier `t`, invoke the
function under the current caller configuration:

```text
Invoke(f,t,C) =
  enter invocation u in current C;
  establish its source boundary instances;
  Receive(u,parameter,t,typed correspondence);
  Run(entry_f; body_f) >>= ReturnFromInvocation
```

An input retained as a computation remains bound to `t`. An ordinary value
parameter `x:A` abbreviates the entry program

```text
View(t,parameter-computation-port,Force(t))
  >>= lambda (v,C1).
      RebindResultPath(u,t,x,v,C1);
      Run(body_f,environment[x := v],C1)
```

This is the **same invocation**, not an extra wrapper call. `RebindResultPath`
is notation for the existing typed relational image and receipt rule. It
transports only matching result/value paths, with the same assignment and
symbolic `K,D`. It neither copies an outer effect annotation to unrelated
latent positions nor creates a contract. The complete call view encloses
entry, body and the admitted result adaptation. All states are current live
states; receiving or rebinding an input takes no handler/store snapshot.

The common function-as-handler boundary does not fabricate operation arms.
Actual shallow operation coverage and capture authority still require the
source handlers, contracts and typed paths already specified. In particular,
entry `Force` cannot invent permission from origin, family equality, `[_]`,
or handler ownership. A later body handler is not already installed during
the entry force. Keeping a computation parameter permits its body to execute
it under a handler explicitly introduced there.

Operation values are instances of this same invocation relation:

```text
ApplyValue(Operation(op,decl),t,C) =
  Invoke(entry_from_decl; native_body,t,C)
native_body(a) = Return(MakeRequestThunk(op,a))
```

The declaration supplies the payload role and typed correspondence. For a
value payload `a:A`, entry executes `Force(t)` and the matching typed rebind
before constructing the latent request from `a`. Thus `Unit → Unit` supplied
with `Delay(Return Unit)` records a `Unit` payload, not a thunk as `Unit`.
A computation-valued declared payload retains its carrier according to that
declaration. `MakeRequestThunk` is an internal constructor, not a public
callable: it introduces no wrapper activation or recursive invocation entry,
and emits no request. The invocation returns the thunk normally; only a later
demanded `Force` exposes its request. This instantiation preserves source
origins, operation-instance endpoints, symbolic `K,D` and corresponding
payload/result incidences without inventing arms or capture grants.

**Entry expansion theorem.** A value-parameter invocation and its expansion
into receipt, entry force, result rebinding and original body have the same
complete source relation, for every admissible input carrier/configuration
and every finite future-use and raw-resumption history. This is an expansion
law of the candidate source machine under the user's reference, not a proof
of frozen lowering or arbitrary-source type soundness.

Relate the two configurations after entering the same invocation `u`, with
identical boundary instances, receipt edges, live store and executing views.
If force returns `(v,C1)`, both sides use the same result-path image, bind the
same value and enter the same body. No part of this step inspects `A` to
force latent descendants of `v`. If force yields a request, the ordinary bind
equation retains its exact event, origin and symbolic `K,D`, appending the
same rebinding/body/return suffix to its continuation. Emission-context
projection and ordered search therefore see the same current typed paths,
handlers and candidate eligibility.

On a shallow capture, both sides save the same crossed view/owner delimiters.
Raw resumption uses the current response and store. The existing owner
protocol borrows a still-live owner or installs a fresh execution occurrence
after expiry; it does not rename the original boundary receiver, replay entry
receipt, or restore a consumed shallow handler. The suffix proceeds from the
saved point through rebind/body. Induction on each finite interaction history
preserves these configurations after every resumed prefix, including repeated
resumption. Thus expiry and future latent uses remain governed by the same
typed-value transport relation. This proof reuses the common bind/control
theorem rather than adding a special callback rule.

For an operation invocation, the same proof takes the original body to be
`Return(MakeRequestThunk(op,a))`. A returning entry force supplies the typed
payload to that constructor; a requesting entry force retains the exact
rebinding/native-body/return suffix on raw resumption. Normal return and later
latent request exposure therefore use the same owner and typed-transport
rules as other invocations. This is conditional on declaration-role and
typed-correspondence elaboration; it proves neither Oracle lowering nor the
remaining whole-source typing/acceptance bridge.

The typing consequence is relational composition: the complete invocation
includes the input computation's execution and then its value-consuming body.
A pure body alone cannot establish a pure invocation or discharge the input's
symbolic constraints. An incoming effect is propagated by the force/bind
image, subject to actual surrounding handlers; it must not be rejected or
erased solely because `x` is used as a value after rebinding. Determining the
source annotation bounds and the principal expressible approximation of that
image remains a typing theorem, not an assumed row-subtraction rule.

Frozen production can instead place `ForceThunk` in the argument expression
before invocation (`specialize2/task_solver.rs:498–505`,
`emit.rs:248–266,935–952`, `runtime_shape.rs:794–813`, followed by runtime
`eval.rs:84–94`). This is a **placement difference requiring proof**, not by
itself evidence of unsoundness. Any optimization moving force out of entry
must preserve activation/receipt/view behavior as well as ordinary effects
and divergence. Such a theorem has not been established here. Likewise, the
entry expansion begins after inert introduction. Section 17 of the charter
now settles the earlier source scheduling question; §9 remains frozen
characterization and a counterexample to blanket prefix hoisting. No runtime
tag or new source construct is introduced to conceal the remaining proof.

## 11. Next construction and decision boundary

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
10 fixes common invocation and its entry expansion. Section 8's prior
role-annotated skeleton does not discharge the remaining raw-source premises.
The characterized strict case behavior is a reasonable
compatibility candidate; it is not independent authority for all consumers.
Potentially removing `≈` as an operational choice by proving identity/η
coherence is a separate simplification, not an established result: equal
undecorated shapes alone do not prove preservation of view/receipt evidence.

The user closed the scheduling question with A in
`2026-10-02-source-call-scheduling-choice.md`: computations are first-class
data, introduction is inert, and execution requires receiver elimination.
Charter §§16–17 govern the same-activation entry rule and whole-argument
reification. The complete frozen discriminator is still not certified as an
accepted Oracle source program; source authority comes from the user's
clarification. Section 12 packages the introduction/elimination simulation
with invocation and future use. Full source
soundness/principality, modular client coverage, lifecycle and implementation
remain open; this package must not be used to declare Milestone 3 complete.

## 12. First-class computation introduction and elimination package

The constructive refinement is
`2026-10-02-typed-computation-core-elaboration.md`: for its finite declarative
core, code is generated rather than supplied. The `Call` equation below is
the kernel producer application. A source computational call uses the
declared execution view constructed there; copying a native operation
producer alone into `ArgumentCode` fails its result-port typing.

### Source law and representation boundary

A computation value denotes code with lexical typed-value references.
Writing `⟨c,η,L⟩` for that source value and `Delay(c,η,L)` for its kernel
representation introduces no new surface construct. Both are inert. Only
the explicit consumer executes the represented code:

```text
Introduce(c,η,L,C) = Return(Delay(c,η,L),C)
Eliminate(Delay(c,η,L),Cnow) = Run(c,η,Cnow;L)

Call(e1,e2,η,C) =
  Run(e1,η,C) >>= lambda (f,C1).
  let t = Delay(ArgumentCode(e2,η),η,L) in
  ApplyValue(f,t,C1)
```

`ArgumentCode` identifies the entire represented computation; deriving its
code, consumers and corresponding typed positions from arbitrary source is
still a premise. `η` contains immutable bindings and references to mutable
locations, not frozen location contents. `L` retains required lineage and
typed boundary references, not saved handler activity. The same current
configuration is used on each side of an elimination, including its executing
typed view. The equation does not erase that view or move elimination across
an invocation return delimiter.

For a computation-valued binding `x=t`, value lookup is `Return(t)`.
Receiving, storing or returning that value does not call `Eliminate`.
For example, eliminating `Delay(Return(t))` yields `t` as data, with no
recursive elimination. If source handling or another declared consumer
demands execution of `t`, that consumer supplies a distinct elimination.
This leaves the source derivation of an annotated expression's consumer open;
it does not decide that all occurrences in annotated function bodies are
mere value lookup.

For operation values, the existing native invocation in §10 still obtains
its declared payload and returns `MakeRequestThunk(op,a)` normally. There is
no added `CompleteResult` force after that return. An operation carrier's
explicit use is required to emit its request. No representation flag, effect
annotation copied without a consumer derivation, or latent result shape can
justify an extra elimination. The kernel's construction/emission distinction
therefore keeps its existing invocation lifetime.

### Conditional realization theorem

Fix `ν`, corresponding typed code and environments, and the previously
defined view/owner/receipt relation. Suppose the represented code and all
its explicit consumers have the ordinary source-to-kernel simulation; this
premise must be discharged by source elaboration, not by choosing a runtime
shape. Then inert introduction, explicit elimination and common invocation
preserve that simulation for every finite execution prefix and every
admissible finite future-use/resumption history. Computation-valued results
remain related as values. This is a closure theorem for the chosen source
constructors, not an arbitrary raw-source typing or principality theorem.

**Initial relation.** Extend related environments/stores by relating
`⟨c,η,L⟩` to `Delay(c',η',L')` when code, lexical references and transported
typed evidence correspond. Require the same shared assignment `ν` and joint
`K,D` incidence; do not materialize family arguments. Source introduction
and kernel allocation return that related pair without executing code,
changing source store contents, allocating a request event, observing a
request or creating a capture grant. Administrative carrier allocation has
no source-visible effect. Existing boundary references remain references;
live authority is recomputed from actual receipt and activity at use.

**Primitive execution and calls.** Explicit elimination unfolds the related
code at the current live state under the corresponding executing view, so
its forward step follows the code-simulation premise. In a call, the callee
computations are related by that same premise. A callee request preserves the
still-unexecuted argument introduction and invocation in its continuation.
On callee return, introduction produces the related carrier pair and both
sides enter the corresponding receiver. Receipt and boundary entry precede
the declared demand. A computation parameter retains the related pair; a
value parameter uses elimination followed by the same typed result rebind
and body. This is §10's common entry expansion, with no extra invocation.
The body receives the returned value without inspecting its shape to force
descendants. An unused computation parameter never invokes the code premise
for its argument and hence never executes that argument.

**Requests and resumption.** State-threaded bind appends the same pending
rebind/body/return suffix. The matched request preserves operation instance,
origin, dynamic event correspondence and every symbolic `K,D` incidence.
Current-view projection supplies identical `Observe`; corresponding `Flow`
and `Receive` give the same active `Inc_C`. Ordered handler search and
`OpCompat` consequently use the same premises. On shallow capture, both save
the same crossed view/owner contexts. Resume uses the current response/store
and the existing borrow-or-fresh-owner protocol; it neither repeats receipt
nor revives original expired boundary authority. Matching, guards and arms
remain outside the selected shallow handler. The saved suffix continues from
its suspension point, rather than restarting argument execution.

**Future values and conclusion.** Environment/store/result transport keeps
the same typed-path relational image on the related computation values.
Each later explicit elimination is again the primitive execution case in its
then-current state. Expired receiver/handler references confer no authority;
latent effects, origins and joint symbolic constraints remain present.
Induction on finite interaction histories, with the existing bind and
saved-context simulation, closes these clauses, including repeated raw
resumption. Diverging code has matching finite prefixes under the code
premise; introduction itself cannot introduce source divergence. This proves
the closure theorem and the candidate exact-interface image for these
constructors without a new selector or source-site rule.

### What remains for the milestone

The source scheduling and inertness choices are closed. Still required are
raw-source derivations of `ArgumentCode`, known-interface demand, explicit
consumer positions and annotation/path correspondence; admitted adapter
coherence; and the finite regular/parametric symbolic presentation, abstract
identity correlation, uniform clients and acceptance bridge of §11. A finite
syntax inventory does not discharge those obligations. No new runtime tag,
eager result completion or supported-envelope restriction is adopted here.
