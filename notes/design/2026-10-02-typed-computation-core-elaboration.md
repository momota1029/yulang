# Typed computation ports: constructive core elaboration

Date: 2026-10-02
Status: Draft; no implementation authority; full raw-source elaboration remains open
Scope: finite derivation-indexed ordinary core, executable-code construction and simulation
Approved-by: none for this construction; charter §§13–21 govern its source premises
Drafted-by: primary with bounded architect construction and independent semantic attack
Reviewed-by: independent compiler_referee and spec_auditor, 2026-10-02; no blocking/major findings; minor handler-subcode construction clarification closed by primary
Source-synthesis review: independent compiler_referee and spec_auditor, 2026-10-02; no findings in §6 result/consumer construction, source-role coherence and scoped substitution theorem
Parameter-role review: independent compiler_referee and spec_auditor, 2026-10-03; no findings in charter §21's syntax-directed role and entry-skeleton construction
Checking review: independent compiler_referee and spec_auditor, 2026-10-02; no findings in §7 proof-label erasure, actual receiver contract obligations and conditional adapter-obstruction scope
Certificate-comparison review: independent compiler_referee and spec_auditor, 2026-10-02; no findings in §8 fixed-domain construction, routing preservation and scoped future-use theorem
Invocation-port review: M3 compiler_referee/spec_auditor package review; operation-consumer omission repaired and closed by independent compiler_referee delta review, 2026-10-02
Supersedes: no source authority; refines the executable-code premise of source-computation-role §12

Provenance: inert computation introduction, typed consumption and shallow
handler scope are user-selected **Yulang extensions**, not Simple-sub-original
rules. The finite derivation-core translation is a **new successor candidate**
with the scoped realization proof below. Its total raw-source elaboration and
principal-inference application remain conjectural. Frozen code and fixtures
are characterization evidence only.

## 1. Problem and exact advance

Source computation introduction is inert. Executing its designated interface
`Comp(E,A)` must yield `A`, including when `A` itself has latent behavior.
These two facts do not justify copying carrier-producing kernel code into
every source argument.

For example, let `op : Unit -> Comp(E,Int)` and let `id` have a value
parameter `Int`. The existing native operation invocation returns a request
carrier. Thus the proposed translation

```text
Force(Delay(ApplyValue(Operation(op), Delay(Return Unit))))
```

returns that request carrier, not an `Int`. No request has yet been emitted.
It cannot implement `id`'s specified argument computation and typed rebind.
This is a counterexample to a particular proposed elaboration, not to inert
introduction or the conditional simulation in source-computation-role §12.

The repair is to derive **execution of the designated computation port**.
An explicit consumer may execute the native request carrier after its native
invocation returns. That force is justified by the source computation being
consumed, not by the returned value's runtime shape. The consumer is part of
the delayed argument code and therefore runs only within `id`'s entry force.

This document constructs executable code for an entire finite typed core
derivation. It no longer takes arbitrary corresponding executable argument
code as an input. It still takes the source's introduction/elimination and
typed-path derivations as inputs. Deriving those uniquely from arbitrary
raw annotations and inference constraints is not proved by this construction.

## 2. Declarative input, without executable schedules

Use the existing two judgments:

```text
Gamma |- d : Value(A)
Gamma |- c : Comp(E,A)
```

`Value(A)` includes first-class computation data, functions and ordinary
data. A separate source elimination derivation identifies a computation
value's exposed interface `Comp(E,A)`. This is a typed path correspondence,
not an equation saying that every `Value(A)` whose solved shape is a thunk
must run. `Comp` here is a judgment; no new surface type syntax is proposed.

The input is a finite source derivation graph, with recursive definitions
referenced by binders. It contains:

- source literal/name/closure/operation/binding/call/handler nodes;
- parameter roles (value or retained computation), result ports and their
  original annotation positions;
- explicit introduction or elimination at the corresponding typed path;
- the existing `Flow`/receipt correspondence, handler declarations, symbolic
  family formulas `K` and dependency incidence `D` under one assignment `ν`.

It contains **no executable argument code, force schedule, runtime shape
dispatch, or selected handler**. An elimination witness identifies which
computation interface is consumed; it does not contain its implementation.
Inferred role variables are not resolved by guessing in this theorem. Section
6 derives roles directly for charter §21's ordinary parameter forms; other
annotation/role resolution remains outside this derivation-indexed input.

The following proof notation displays the constructors of that derivation:

```text
d ::= literal | name | lambda(P,c) | operation(decl) | reify(c)
c ::= result(d) | eliminate_p(d) | call(c_f,c_a)
    | bind(x,c_1,c_2) | handle(H,c)
```

`result` observes/constructs data, even when that data is a computation.
`eliminate_p` consumes the interface identified by its typed source path `p`.
These are names for derivation rules, not proposed user keywords. They do
not claim that a raw occurrence already tells us which rule applies.
For example, ordinary data lookup of `t` is `result(name t)`, while a source
consumer of its computation is `eliminate_p(name t)`. No lookup rule forces.

Each closure body has its declared result computation port; returning a
latent `A` uses `result(d)` at that port. Handler bodies use the designated
computation derivation. Ordinary binding consumes its selected RHS computation
and binds its **result value**; inertly storing computation data instead uses
`result(reify(c))` or data lookup. This records different source derivations
without selecting between them from final type equality.

The first construction needs no general value-conversion node. Arbitrary
implicit conversions and unknown-shape adapter generation remain an extension
gate; the proof does not declare programs needing them ill typed. Handler
patterns/guards/arms use their previously defined outside relation and typed
subderivations; their general pattern elaboration is not newly proved here.

## 3. One structural translation

Let `V[d]` be a data descriptor and `X[c]` executable computation code.
Descriptors capture lexical value/cell references and typed evidence. Reading
a descriptor and creating a closure/delay execute none of its represented
code. All execution below threads the current store and active context.

```text
V[literal]           = literal
V[name x]            = lookup(x)
V[lambda(P,c)]       = Closure(entry_P; X[c], lexical references)
V[operation(decl)]   = Operation with declaration execution entry
V[reify(c)]          = Delay(X[c], lexical references)

X[result(d)]        = Return(V[d])
X[eliminate_p(d)]   = Execute_p(V[d])
X[bind(x,c1,c2)]    = X[c1] >>= lambda v. X[c2] in environment[x := v]
X[handle(H,c)]     = shallow_image_(H^X)(X[c])
X[call(cf,ca)]     = X[cf] >>= lambda f.
                       let t = Delay(X[ca], lexical references) in
                       ExecuteCallable(f,t)
```

`Execute_p(t)` is the existing one-layer execution of the designated
`Comp(E,A)` in its corresponding typed view. It is `Force(t)` under that
view, not recursive force-until-nonthunk. In particular `Execute_p` returning
latent `A` introduces no elimination of `A`. Any separately justified
consumer of `A` is another derivation node.

`H^X` retains the declarative handler's operation coverage and pattern
descriptors and translates its guard/default/arm computation subderivations
with the same `V/X` recursion. These descriptors are constructed, not supplied
as executable code. Their execution still occurs outside the selected
shallow handler. The existing pattern-binding primitive supplies the declared
pattern mechanics; this translation does not prove a new raw pattern elaborator.

`ExecuteCallable` is the executable view of the **declared result computation
port**, within the common complete `CallView`. It is not data observation
followed by unconditional result completion. Every callable producer exports
this same interface, including through function variables:

```text
closure execution = Invoke(entry_P; X[body], t)

operation execution =
  Invoke(entry_decl; Return(MakeRequestThunk(op,payload)), t)
    >>= lambda request_value. Execute_decl_result(request_value)
```

`Invoke` establishes one receiver activation, boundaries and receipt before
entry. Value entry forces its received argument computation and rebinds its
result; retained-computation entry stores the argument. The operation's
explicit result consumer is derived from this computational application
judgment and its declaration. It is not an added source wrapper invocation,
a tag on an arbitrary result, or an operation-family visibility exception.
A function variable retains the callable's executable definition; callers
do not inspect the returned value to discover which implementation it used.

The native operation invocation returns before this distinct result consumer
force, retaining the current candidate's native return delimiter. The
surrounding complete consumer view remains present. No claim is made that
moving the force into the native body or before receiver receipt is equivalent.
The pure carrier-producing `ApplyValue` remains a kernel operation; identifying
it with every completed source call was the failed shortcut in §1.

For the §1 example, `ca` is computational application of `op` to `result Unit`.
Its translated code includes the declaration's explicit result elimination.
`id` receives `Delay(X[ca])`; entry executes it, exposes `E`, and receives the
`Int` response. For a stored computation the corresponding argument code is
`Execute_p(lookup t)` instead. Both use the same receiving contract and common
executing-view relation. This asserts no equality of their origins, events
or symbolic `K,D`, and no equality of traces from different computations.

## 4. Constructive realization theorem

For every finite derivation graph of §2 with well-formed declared interfaces
and the existing source typed-path/owner premises, §3 constructs a finite
code graph. Its execution simulates the derivation's ordinary computation
relation, preserving initial relatedness, every finite prefix, and every
admissible finite future-use/raw-resumption history under the same `ν`.
This is a theorem for the displayed derivation core, not for arbitrary
inferred Yulang source. The source relation interprets data inertly,
elimination by its identified computation, calls by the same declared
invocation and computation port, and handlers by the primitive shallow image.

**Construction.** Allocate a code/descriptor label for each derivation node
before visiting its children. A recursive definition reference targets its
existing label. Every translation clause emits a bounded command template
and references only immediate child labels or fixed invocation/handler
primitives. Consequently construction terminates on a finite derivation
graph; it never unfolds recursion or inspects a result's assigned shape to
choose more eliminations. This supplies the previously abstract
`ArgumentCode` as `X[ca]` for this core.

**Initial relation and data.** Relate each source literal, lexical binding,
closure and reified computation to its descriptor, with corresponding
environments/cell references and the same typed evidence. Recursively
referenced closures use the graph relation, not infinite expansion.
Introduction returns related data with unchanged source store/activity;
administrative descriptor allocation creates neither a request nor a grant.
There is no source-visible allocation failure in this semantic theorem;
compiler/runtime resource policies are separate obligations.

**Forward execution.** Structural induction on a derivation step gives the
result and explicit-elimination cases from descriptor relatedness and the
ordinary `Force` equation. For bind, apply the state-threaded bind lifting
theorem to the related RHS and its result-binding suffix. For call, first
apply the induction hypothesis to the callee. Its return triggers inert
construction of the whole argument and the corresponding invocation; a
callee request instead retains that entire unfinished suffix. Receipt precedes
entry in both machines. Value entry eliminates the related argument and
rebinds the related result; retained entry leaves the code unexecuted.

Closure execution reduces to the body induction hypothesis. Operation
execution obtains its declared payload with the same entry, constructs the
same operation-instance carrier, returns across the same delimiter and
executes the explicitly selected declaration result port. Its request and
response therefore have the correct result type; no latent descendant of
that response is forced. Handler execution is the existing shallow-image
simulation, with matching/guards/arms outside and actual ordered selection.
These cases exhaust this core; an unspecified adapter or source construct
is not silently handled by an oracle primitive.

**Evidence and future interaction.** At every case, descriptors and bind
retain original source origins and the same joint `K,D` under `ν`.
Corresponding typed views supply the same emission-context `Observe` before
search. With corresponding `Flow`, receipts and live owners, `Inc_C` and
ordered eligibility agree. Shallow capture saves matching crossed contexts;
raw resumption uses the current state and existing borrow-or-fresh-owner
protocol without replaying receipt or reviving expired authority. Its suffix
includes any unfinished entry, explicit result consumer and return binding
in their original order. Induction over finite interaction histories closes
future function calls, computation elimination and repeated resumption.
Latent result paths keep their own boundary references after a complete view
ends; activity still determines authority. This reuses the common control
theorem rather than introducing separate callback rules.

Composing this simulation with the exact-interface embedding supplies
source-to-complete-interface adequacy for this derivation core. It does not
establish type preservation of an inference algorithm that has not yet
generated the derivation.

## 5. Finiteness, source evidence and remaining gates

If `n` is the number of distinct derivation constructors and `m` the supplied
typed profile/correspondence data size, code and descriptor templates occupy
`O(n+m)` space under fixed primitive templates. Variable-length handler arms
and lexical reference entries are counted in `n+m`. This counts static code,
not dynamic heap states, solved types, instantiated schemes or adapter queries.
Recursive bindings share labels. It is neither a finite principal-interface
theorem nor a class-3 obstruction; all earlier regular-quotient obligations
remain.

Frozen `a58eefc3` evidence is characterization, not authority:

| Source evidence | What it establishes and does not establish |
|---|---|
| `web/docs/reference/type-theory.md:20–42`; `functions.md:126–141` | Documents `[E] A` as computation value and `() -> [E] A` as obtaining `A` with effects; not a unique elaboration rule |
| `crates/yulang/src/source/tests/case_01.rs:146–163` | Contains the accepted-fixture assertion for `id(out::read(()))`, with `id : int -> int`; frozen force-before-call placement is not source authority |
| `tests/yulang/regressions/effect/effectful_parameter_forwarding.yu`; `case_02.rs:2712–2730` | Forwarded computation parameter retains result effects in inference output; no runtime timing assertion |
| `case_01.rs:1248–1274` | Ordinary local operation binding is expected to execute before a later handler; this is not evidence that any local binding automatically stores computation data |

These existing assertions were inspected, not executed in this work. No
accepted fixture was located pairing a directly effectful callback with a
captured computation-returning callback; their common visibility requirement
comes from the user's typed contract decision.

The exact next source obligation is a **coherent derivation of the input
ports**, including inferred roles, nested annotation/result paths and admitted
conversions. Full annotations are not automatically enough: the regular
`A = Thunk(E,A)` witness in source-computation-role §7 demonstrates that
type equality and row inclusion can permit distinct pure-lift and exposure
derivations. A source occurrence/path rule must decide those roles before
representation collapse, and must remain stable under permitted substitution.
This construction gives no ad hoc priority to either derivation.

Charter §18 now selects forwarding in synthesis. Section 6 constructs those
result/consumer derivations for the ordinary source constructors, rather than
leaving this specific choice as input. General checking/conversion coherence
and the remaining symbolic presentation obligations are still separate.

Next close that source derivation/coherence gate together with the regular
or parametric symbolic query presentation, uniform clients and acceptance
bridge. Generalization/fresh instantiation/intrusion then preserve the chosen
presentation; implementation feasibility and implementation follow their
existing gates. No acceptance restriction or representation language is
approved merely because this core has finite executable templates.

## 6. Source result synthesis under user-selected forwarding

### Source interface and one normalization

Charter §18 selects two disjoint source interface forms:

```text
I ::= Value(A) | Computation(E,A)
Result(Value(A))         = Comp(empty,A)
Result(Computation(E,A)) = Comp(E,A)
```

These distinguish the source interface being forwarded, not two runtime
shapes. `A` may denote first-class computation data, a function or a recursive
value without changing the `Value` tag. An empty `E` does not change a
`Computation` tag. There is no result-interpretation type variable.

Synthesis constructs `(I,d,n)`: a source interface, an inert data derivation
and the computation derivation for **explicit consumption of Result(I)**.
Constructing `n` is not executing it. Normalize by the original interface:

```text
Normalize(Value(A),d)         = result(d)
Normalize(Computation(E,A),d) = eliminate_p(d)
```

In the second clause, `p` is the corresponding known source computation port,
retaining its original profile and symbolic `K,D`. The clause is not selected
by comparing the solved representation of `A` with `Thunk(E,A)`.

### Source parameter-role generation before body synthesis

Charter §21 fixes these syntax-directed rules for ordinary parameter names:

| Parameter syntax | Generated `P` | Body binding `Gamma(x)` |
|---|---|---|
| `x` | `Value(A)` with fresh inferred value endpoint `A` | `Value(A)` after entry rebind |
| `x:A`, ordinary value annotation | `Value(A)` | `Value(A)` after entry rebind |
| `x:[_] A`, explicit outer computation annotation | `Computation(E,A)` | `Computation(E,A)` retained |
| `x:[E] A`, explicit outer computation annotation | `Computation(E,A)` | `Computation(E,A)` retained |

For the wildcard, retain the symbolic effect endpoint with its existing
source meaning; no new quantification rule is assumed. Annotated endpoints
use the admitted annotation derivation. This table determines their outer
role, not all nested annotation checking or constraint satisfiability.

Generate `P` and its entry skeleton before synthesizing the body. Receipt
path references retain the admitted annotation/typed-flow premises; this does
not solve all nested paths from the outer role alone. Every application still
delays the whole argument inertly. Value entry
establishes the actual receiver/receipt, forces the designated argument view
once and rebinds its result before executing the body. Retained entry binds
the same carrier without executing it. Body uses generate ordinary endpoint
and contract constraints; they cannot revise the source role or remove entry
execution. Substitution making `A` latent introduces no recursive force;
substitution making `E` empty does not change retention.

For example, `ignore x = ()` executes the argument before its constant body,
including effects or divergence. With an explicit outer computation
annotation, that constant body retains and ignores the carrier. A pure
divergent carrier of empty effect support still distinguishes these entries.
The role rule therefore does not infer entry behavior from effect support.

**Finite generation and coherence.** Each parameter occurrence constructs
one fixed role, a finite binding/receipt/entry skeleton and its endpoint
references. Combine it with the result table below to synthesize a lambda's
body under the generated `Gamma` and its result via `Result(I_b)`. Structural
induction gives one skeleton up to fresh endpoint/label renaming: the four
source forms choose a disjoint outer role and no body-use alternative.
Finite recursive references reuse registered nodes rather than unfolding.

Capture-avoiding renaming transports the generated binder, profiles and
typed paths together. Admissible endpoint substitution preserves the source
tag and entry skeleton, and the existing result/consumer substitution law
then applies to the synthesized body. This proves coherence of these roles
and their structural composition, not principal solving of the endpoint
constraints or invariance under an unproved annotation conversion.

Only the supplied parameter-role premise for these forms is removed. Full
annotation/pattern elaboration, casts/adapters, unknown global interfaces,
Function subtyping and inference remain open; operation declarations retain
their independently declared interfaces. No generalization or implementation
policy follows from this construction.

### Structural rules producing the core derivation

The following rules operate on the ordinary expression constructors using
known lexical/declaration interfaces in `Gamma`. They generate result roles;
they do not take arbitrary result-role derivations or executable code as input.
Parameter entry remains owned by the callable's source interface, generated
above for the stated parameter forms and declared independently otherwise.
Unknown value/effect endpoints remain symbolic constraints.

| Source constructor | Synthesized interface `I` | Inert data derivation `d` |
|---|---|---|
| literal | `Value(type of literal)` | `literal` |
| name `x` | `Gamma(x)` | `name x` |
| function with parameter interface `P` and body `b` | `Value(Fun(P,Result(I_b)))` | `lambda(P,n_b)` |
| operation name | `Value(Fun(P_decl,Comp(E_decl,A_decl)))` | `operation(decl)` |
| application `f a` | `Computation(E_call,A_call)` | `reify(call(n_f,n_a))` |
| ordinary local binding `my x = r; b` | `Computation(E_bind,A_b)` | `reify(bind(x,n_r,n_b))` |
| shallow handling of `b` | `Computation(E_handler,A_handler)` | `reify(handle(H,n_b))` |
| explicit inert introduction of `b` as data | `Value(computation-data(Result(I_b)))` | `reify(n_b)` |

Each row constructs `n=Normalize(I,d)`. For local binding,
`Result(I_r)=Comp(E_r,A_r)` and the body environment binds `x:Value(A_r)`.
This is result binding when the enclosing computation executes. The entire
binding computation is reified without running an RHS construction prefix.

`E_call,A_call`, `E_bind` and `E_handler,A_handler` are symbolic endpoint
names constrained by the existing complete invocation/bind/shallow-image
relations. Complete invocation here means the producer's `ExecuteCallable`
from §3, including an operation's declared result consumer after its native
return; §9 distinguishes that image from the closure body/result skeleton.
They are not invented row unions or solved effect supports. The
callee constraint identifies a Function interface at the result of `n_f`;
the argument constraint relates the **whole** computation `Result(I_a)` to
its parameter interface, with the existing typed path/contract obligations.
The caller always passes a reified argument. It need not guess an unknown
callee's entry mode; the actual callable owns its entry expansion. Failure
to solve a callable or boundary constraint is not repaired by an extra force.

The handler's guards/arms/defaults use the same source synthesis and known
consumer interfaces before §3 constructs their executable descriptors. Their
execution remains outside the selected handler. General raw pattern typing
and arbitrary boundary adapters are not solved by this rule table.

The introduction row denotes the explicit source introduction/lifting
derivation required by the user; it proposes no new surface keyword.
Selecting its surface spelling is not part of this theorem. A type annotation
or a solved shape alone does not silently supply that introduction.

This table gives a complete result-role construction for these expression
forms relative to `Gamma`, callable declarations and the existing handler
typing premises. It does not claim arbitrary raw annotation resolution,
recursive-binding inference or constraint satisfiability is now implemented.
Forward references reuse registered declaration endpoints; solving definition
SCCs remains a later inference/lifecycle obligation.

### Coherence, transport and realization theorem

For a finite ordinary expression graph with those lexical/declaration
interfaces, the rules construct a unique result/consumer skeleton, up to
fresh endpoint/label renaming. They introduce no inference alternative
between returning computation data and executing its known outer interface.
The explicit consumer, not synthesis, determines when execution occurs.

**Uniqueness.** Induct on the expression construction. Literal and name copy
their fixed source interface; a lambda's result is the single `Result(I_b)`
from its inductively determined body; operation declarations fix their
interface. Application, sequencing and handling have a computation result
role, with endpoint constraints rather than role alternatives. Explicit
introduction alone creates a value containing a computation. In every case
the two `Normalize` clauses are disjoint by source tag. Reusing labels for
recursive definition references does not unfold their bodies or change their
registered interface. This proves skeleton coherence, not uniqueness of
type solutions or admissible coercions.

For `Gamma(x)=Computation(E,A)`, synthesis of `h(x)=x` now constructs
`Fun(P,Comp(E,A))`, a data lookup and the explicit known-interface consumer
for its completed result. It cannot construct `Comp(empty,computation-data(E,A))`
without an explicit introduction row. Synthesis of a value-valued result uses
`Comp(empty,A)` and returns the data. Even if recursive type equality later
identifies the erased endpoint shapes, it does not add a second synthesis
derivation: the source tags and introduction occurrences remain distinct.

**Endpoint substitution.** Let `sigma` substitute ordinary value/effect
endpoints and consistently rename typed binders/paths while preserving the
source declaration/interface tags and typing premises. Directly in the two
cases,

```text
Result(sigma(I)) = sigma(Result(I))
Normalize(sigma(I),sigma(d)) = sigma(Normalize(I,d)).
```

Induction through the table gives the same property for the generated
result/consumer skeleton and all corresponding `K,D` payloads. An endpoint
assigned a latent/recursive shape causes no further elimination; assigning
an empty effect row creates no entry force for a retained parameter. This
does not assert that every substitution preserves typing premises, that
arbitrary adapters stay unchanged, or that a source interface may be changed
from `Value` to `Computation` by such substitution. Generalization must
preserve those source positions; the full solver/lifecycle theorem remains
unproved.

**Execution.** Apply the whole-core construction of §§3–4 to the generated
derivation. At an explicit consumer, `n` returns the designated `A` with the
same current view, source origin and joint symbolic constraints. Nested
`eliminate(reify(c))` uses the existing same-context delay/force law; it does
not move execution across a receipt, handler or return delimiter. Retaining
that administrative pair is also valid. The operation's completed execution
view remains distinct from its native carrier producer, as established in
§3. A latent `A` is returned without another force. The existing simulation
then covers initial relatedness, request prefixes, ordered handler visibility,
future use and raw resumption of this generated skeleton. No independent
capture rule or result-interpretation dispatch is added.

**Finite construction.** Per source constructor the table introduces a
bounded number of core nodes and symbolic endpoint names; child derivations
and definition references are shared. The earlier `O(n+m)` static-template
bound therefore applies to source-generated result skeletons as well, where
`m` includes the supplied profile/typed-path descriptors. This establishes
finite generation, not finite solved constraints or principal inference.

The source forwarding blocker is closed. The next obligations are complete
annotation/checking and admitted-conversion coherence, finite regular or
parametric symbolic query solving, modular future clients and acceptance;
then the selected milestone order reaches lifecycle and implementation.

Section 9 makes an important distinction in this table explicit:
`Result(I_body)` describes the body result port. It is not, by itself, a
closed bound on complete invocation of a value receiver with arbitrary
effectful argument carriers. The application row's `E_call` already depends
on the complete source-call relation. Keeping that carrier dependence is
required by the same-activation entry semantics.

## 7. Checking normalization and the scope of the adapter obstruction

### Three different obligations

The source decision determines introduction and consumption independently of
the solved value shape. Consequently three operations must not be identified:

1. constructing/consuming a known source computation, as in §6;
2. proving that the same decorated value or computation meets another
   interface, without executing a conversion;
3. executing an admitted value conversion, for example a registered cast.

This is a decomposition of proof obligations, not a decision to remove (3).
Frozen source accepts ordinary value casts. Nor does this assert that every
Function assignment belongs to (2). A theorem normalizing every required
source conversion to these operations is still required.

For (2), write `VIncl(A,B)` for inclusion of the **same decorated values**,
and `CIncl(J,J')` for inclusion of their complete computation interfaces under
the same symbolic assignment. The decorations include source profiles,
typed-path correspondences, joint `K,D`, and lineage. These names abbreviate
semantic propositions; they are not proposed new solver atoms or opaque
runtime instructions. In particular, ordinary row inclusion alone is not
the definition of `CIncl`.

The representation-preserving checking fragment is:

```text
Check(Value(A),Value(B)):
    establish VIncl(A,B); retain the value and its evidence

Check(Computation(E,A),Computation(F,B)):
    establish CIncl(Comp(E,A),Comp(F,B)); retain its computation
```

Original annotation slots remain identifiable when the existing typed `Flow`
relation carries their views to corresponding paths. A checking proof is
not an additional receipt, boundary introduction, view delimiter or source
execution. Actual source annotations and their receipt/view derivations
remain in the elaboration, including when the representation does not change.
The target contract is not silently replaced with the inferred source row.

The fragment has no rule changing a `Value` tag into a `Computation` tag or
conversely by inspecting a solved `Thunk` shape. Section 6 supplies the
source introduction/consumption derivations when they exist. This restriction
describes this fragment only; it does not establish completeness of checking
or authorize rejecting other source programs.

### Erasure and constraint-retention theorem

Fix a §6 source derivation, its original contracts, and its common typed
transport/receipt derivations. Insert finitely many proof-only checks of
the above form. Define their erasure to remove the proof labels while
retaining their inclusion constraints and all those source decorations.
For assignments satisfying the constraints:

- the erased and annotated derivations generate identical executable
  instruction graphs, up to administrative proof labels;
- they have identical source introduction/consumption positions, receiver
  entry programs, native return delimiters and handler/view order;
- each checked value/interface has the asserted membership; family
  constraints remain symbolic in the same joint assignment.

**Proof.** A value check generates the existing data descriptor unchanged;
a computation check generates its existing code descriptor unchanged. Its
membership assertion follows from the corresponding inclusion premise.
Induct through the derivation constructors: children share the same code
and environment references, so lambda/reification stores the same code;
call passes the same whole carrier to the same entry program; bind uses
the same result continuation; a handler keeps the same selection, guard
and arm programs. None of these cases creates a new dynamic boundary for
a proof label. Typed evidence is retained, not erased with that label.
Thus the two initial decorated states coincide modulo static proof labels.
Every primitive transition has the same operands and current context on
both sides, including request emission and ordered visibility. Its target
states again coincide. Stored code and raw resumptions reuse those same
descriptors and the current store, proving the result for future executions
as well as the initial prefix. Constraint retention, unlike materializing
a concrete type and reconstructing evidence, preserves the shared symbolic
`K,D` throughout this argument.

The theorem compares a derivation **with and without proof labels**, not
programs with different source callback annotations. Replacing a concrete
contract with a wildcard may change handler visibility; that replacement
is not this erasure. Nor is this a proof that arbitrary proposed inclusions
hold. An effective sound/principal presentation of inclusion is still an
open part of Milestone 3; hiding it inside `VIncl/CIncl` would not close it.

### Function contracts and actual receiver entry

All callees receive a computation carrier. The callable retains its own
declared entry, including whether to force/rebind or retain that carrier.
Function checking without executable conversion must therefore establish:

```text
every target-admissible argument satisfies the actual receiver's contract;
the actual complete invocation satisfies the target result contract.
```

Contravariant arguments and covariant results are consequences only where
these premises hold, including the typed boundary/protection obligations.
Even matching parameter roles do not license ignoring these obligations.
For different roles, comparing the payload endpoints alone is insufficient.
A value receiver executes its input at entry; a computation receiver may
ignore it. Passing a pure diverging computation distinguishes those
behaviors even with an empty effect row. The example rules out equality of
entry behavior based on payload/row equality; it does not require termination
precision in effect inference or declare every cross-role assignment invalid.

No wrapper is required merely to convey an already admissible carrier under
this uniform calling convention. Conversely, effectful/numeric/structural
conversions need their own admitted source computation and correct placement.
An inclusion proof cannot stand in for executing such a conversion.

### Old adapter equations are conditional machinery

Typed-boundary §§3–5 proves a finite implementation of its chosen fixed-shape
equations, not source admissibility of those equations. In particular:

```text
Apply(FunctionView(f,da,dr),x) =
    RunD(da,x) >>= (lambda y. Call(f,y)) >>= (lambda z. RunD(dr,z))
```

When `da` executes the argument computation before `Call`, this equation
does not directly realize receipt-before-entry-force. For a receiver that
retains and ignores the carrier, it can introduce execution absent from the
source invocation. For a strict receiver, moving execution across receipt
still requires a context/visibility preservation proof. The equation's
simulation of itself proves neither fact. If an admitted source conversion
requires an executable adapter, its placement must be derived from the
source receiver/consumer relation; a synthetic receiver or a new boundary
cannot be introduced solely to make the equation fit.

In particular, the pure value supplied to a computation parameter is
already represented by the whole-argument code for `Result(Value(A))`.
This does not require `Adapt(A,Thunk(E,A))` on an ordinary value result.
Similarly, `id(op())` executes the designated outer operation computation
inside the received argument's entry force (§1); it does not recursively
force arbitrary latent values until their shape becomes `Int`.

The unbounded `Adapt(Unit,alpha)` thunk-tower family in source-role §5 is
therefore a real obstruction to that **candidate adapter's producer-only
inventory**, not an established obstruction imposed by successor source
checking. In this checking fragment, assigning a thunk-like shape to
`alpha` adds neither constructors nor execution to `Unit <: alpha`.
Whether such an assignment satisfies value inclusion is a typing question;
checking does not manufacture a value of an unrelated type. Recursive type
equalities likewise do not authorize another source elimination.

### Bounded source-acceptance evidence

The following frozen `a58eefc3` assertions were inspected, not executed.
The locators establish only the stated witnesses, not an exhaustive
acceptance characterization.

| Frozen source/test locator | Required capability |
|---|---|
| `crates/specialize/src/tests.rs:1072–1091` | `keep(x:[_]int)=1; keep(out::read(()))`: retain/ignore the outer computation |
| same file, `675–700` | `accept(f:int -> [out]unit)=f 1`: effectful Function callback, no asserted FunctionAdapter requirement |
| `crates/yulang/src/source/tests/case_01.rs:696–718,760–767` | stored `run:() -> [probe]str` with effectful or pure lambda body; inert function construction |
| `crates/specialize/src/tests.rs:933–948` | ordinary result cast inside the function body; explicitly no whole-function cast adapter |
| same file, `952–971` | registered casts on record fields; explicitly no whole-record adaptation |

The Function/thunk adapter assertions at `crates/specialize/src/tests.rs:93–195`
and `260–333` instead manually construct mono types and expressions. The
shape comparison at `crates/specialize/src/specialize2/tests.rs:1432–1463` is also a
manual runtime-shape test. They characterize an implementation mechanism,
without deriving arbitrary nested-thunk conversions from source annotations.
Source Function annotations separate immediate result effect/value
(`crates/infer/src/annotation/builder.rs:123–142,409–413`), while an Effectful
annotation in value bounds is lowered through its result
(`crates/infer/src/annotation/constraints.rs:334`).
Repeated surface annotations are not evidence for arbitrary latent layers.

No inspected source witness requires the arbitrary tower conversion. This
is an evidence gap, not proof of absence. No Oracle acceptance is dropped
by this audit. Registered casts are positively evidenced and must remain
in the acceptance bridge; their method/role/impl resolution belongs to the
mandatory later gate unless the ordinary-effect proof needs it earlier.

### Consequence for finite presentation and the next gate

For a source derivation with `n` constructors and `k` proof-only checking
occurrences, these checks generate no executable constructors or dynamic
type inspection. Static checking labels/constraint roots take `O(k)` space;
§6's executable-template bound remains `O(n+m)`. Shared recursive references
are not unfolded. This is a finite-generation theorem, **not** a bound on
solved type graphs, symbolic query closure, saturation or principal inference.

Milestone 3 must now derive an effective relational presentation for the
actual source contracts and required conversions. It need not first solve
an unadopted arbitrary runtime-shape conversion calculus. Its acceptance
bridge must show which required conversions normalize to source
introduction/consumption, evidence-preserving checking or an admitted cast;
cross-role Function assignments and casts cannot be removed by assumption.
The old unknown-shape family remains available if that bridge actually
derives it. Finite unbounded, regular, and genuinely non-finite presentations
remain distinct; this audit supplies no class-3 counterexample and closes
no generalization/intrusion or implementation gate.

## 8. Constructive certificate comparison with fixed admissible interactions

The first effective checking subcase must distinguish weakening a guarantee
from enlarging the inputs that a callable promises to accept. A finite
support comparison can discharge the former without an opaque `CIncl` leaf.
It does not by itself discharge the latter. This section constructs that
subcase and gives the exact remaining invocation obligation.

### Why uniform support widening is not Function inclusion

Take a receiver whose body invokes a supplied callback `g`. Its original
interface admits `g : () -> [] Unit` and guarantees a pure result. Changing
only the callback's admitted support to `[E]` while retaining the receiver's
pure result is not sound: the newly admitted callback can perform `E` when
invoked. The caller passes its argument inertly; the request occurs when
the body actually invokes `g`, so no scheduling or extra-force convention
is involved. This is a semantic counterexample to a proposed uniformly
covariant comparison, not an Oracle acceptance claim or a new source rule.

Even if all actual executable instructions are unchanged, the set of
admissible future executions has changed. Thus equality of executions for
one fixed argument cannot prove Function inclusion. Entry-role agreement
and equal payload shapes do not remove this quantifier difference.

### Input and finite constraint construction

Fix a source component, its actual entry/consumer code and a finite regular
complete-interface descriptor graph. The graph distinguishes:

- admissible external challenges, including supplied arguments and raw
  continuation responses;
- guaranteed observations/results and their future latent interfaces;
- original source boundary profiles, receipts and typed correspondences;
- captured/shared writable views and their symbolic dependency references.

These classifications must come from the complete interface semantics.
The source result-synthesis theorem alone does not classify all latent,
stored and shared paths. This is an explicit remaining elaboration premise,
not an annotation that may be guessed by the checking algorithm.

Compare two descriptions of that same component by traversing paired graph
nodes, allocating pairs before following recursive edges. Require the same
value constructors, entry/result roles, source operations, ordinary type
endpoints and labeled typed correspondences, modulo one consistent renaming.
Keep original profile/receipt identities and binder aliasing; a bisimulation
of erased shapes cannot merge distinct source slots or captured variables.
This is checking metadata: it does not replace any source annotation,
introduce an adapter, or change the component's executable graph.

On the finite paired graph propagate two bits, `A` and `G`, recording
assumptions and guarantees:

1. Mark the roots of all external challenges `A`, and propagate `A` through
   their entire reachable descriptor, including nested callable interfaces.
2. Mark guaranteed observation roots `G`. Traverse output/result/latent
   edges with `G`; a guaranteed returned callable's argument edge seeds `A`.
   Its completed result continues with `G`.
3. Treat routing-profile and shared writable/dependent fields as invariant.
   Any field with both bits is invariant. Unclassified fields are retained
   unchanged; they do not become guarantees by default.

In particular, crossing another Function input beneath an assumption does
not turn it into a weakenable guarantee. This construction fixes the entire
challenge domain; it is deliberately not double-contravariant subtyping.
Capture into an environment is not inherently a mutable operation, but its
already-shared imported interface is part of the fixed challenge/environment
premises, not a newly solved local witness.

Each node gains at most two bits, so the propagation terminates on recursive
graphs. For each corresponding **genuine support upper-bound field**, emit

```text
G only:                 forall u. M_actual(u) implies M_checked(u)
A, both, or invariant:  forall u. M_actual(u) iff M_checked(u).
```

All non-support fields remain unchanged. In particular, complete request
instances, response types, latent value structure, original `K,D`, and live
origin/lineage references are not weakened by the support rule. A shared
field used as both assumption and guarantee acquires both bits. Equal row
denotations at different typed positions do not identify those positions.

Routing-profile presence, receiver/slot ownership and original typed paths
are retained. A differently written presentation of an admission row must
have equal membership for **all** request points, as well as the same exact
operation coverage and profile presence. Empty admission does not imply
absent protection. When an admission predicate is outside the membership
grammar, this subcase requires that predicate to be retained identically;
it does not invent an effective equality solver for it. If one compared
field is also a capture contract, it must meet both its support and invariant
routing requirements. A widened outward support bound never authorizes a
change of capture contract.

The open-row membership construction compiles the displayed constraints
into finite Boolean circuits under one `nu`. The paired-graph inventory is
at most the product of the two descriptor sizes; graph representation size
includes edges and profile entries. No recursive signature is unfolded.
Eligible residual row variables can subsequently use the pointwise or
counting-aware projection theorem, with all of their dependency premises.
Underlying endpoint/global predicate solving remains a separate obligation.

### Source preservation theorem

Let `Challenges` be the unchanged set of admissible finite interactions,
including future calls/forces, supplied responses, stored values and repeated
raw resumptions in compatible current stores. Suppose the component has an
original certificate covering all such executions. If the structural and
generated row constraints above hold, the checked description certifies the
same executions, with its possibly weaker guarantee bounds.

**Domain preservation.** Every assumption descriptor and imported/shared
premise is retained. Latent exported callables keep their admitted argument
interfaces; responses supplied to resumptions keep their complete types and
dependencies. Therefore the new certificate requires no execution on an
input outside `Challenges`. This is where the uniform-widening proposal
failed. No new source restriction on permissible challenges is adopted;
the theorem compares two certificates for this fixed domain.

**Routing preservation.** Relate executable states by identity modulo the
metadata renaming. Whole-argument construction, receipt-before-entry,
explicit consumers and native return delimiters are unchanged. Typed
transport composes the same source witness paths and retains the same
profile presence and exact owner/handler identities. Hence `Path` and
`Inc_C` agree at each actual search configuration. Admission equality gives
the same `Grant`; equal profile presence gives the same `Protected`, even
when no grant exists. Thus `Visible` and the ordered selection derivation
agree. Matching, guards and arms execute in the same outside context.
Selected-operation compatibility, including local witnesses and `K,D`, is
the original obligation; support weakening neither filters it nor solves it.

**Guarantee preservation.** At every designated observation, original
certificate membership plus the generated implication gives membership in
the checked bound. Structural endpoints and complete evidence stay the same.
Induct on the finite interaction history and the intervening source steps.
Returned latent values retain their paired descriptors; store transport and
raw resumption use the same current state and inherited dependencies. The
induction therefore covers later executions, not only the initial return.
Shallow re-entry never reinstalls an expired handler. Divergence is covered
through its finite prefixes; termination equivalence is not newly inferred
from a row bound.

The result is an effective **certificate-weakening judgment** for this
fragment. Its generated constraints describe all assignments satisfying
that judgment, and their eligible projection is exact. This is not a
principal Function-type theorem, a derivation of the original certificate,
or a proof that every sound source conversion lies in the fragment.

### Why outward support cannot weaken routing obligations

The raw-resumption counterexample in typed-boundary §4 already shows that
an event may be relevant to an enclosing executing `CallView` before an
inner handler consumes it. The event need not appear in that view's outward
residual support. Therefore a condition such as

```text
outward_support(u) implies equal_capture_admission(u)
```

does not justify profile replacement. The current checker retains routing
universally. A future support-restricted optimization needs a separately
proved bound on pre-dispatch observations, not an outward row substituted
for that bound. This reuses the existing common-source counterexample; it
does not add a callback-specific semantic rule.

### Next complete invocation gate

What remains is comparing **different admissible interaction domains** and
different value/entry descriptions while preserving actual source contracts.
Such a theorem must quantify over all newly admitted caller arguments and
future responses and show that the actual component meets their complete
invocation obligations. Ordinary variance is a proposed consequence of that
theorem, not a premise supplied by support-row syntax. Finite source sites,
fixed operation/arm maps, or the present certificate checker do not prove
its finite symbolic closure.

No source acceptance is removed by this sufficient fragment. Cross-role
assignments, admitted casts, unknown shape solving, full source principality
and the generalization/instantiation/intrusion gates remain required. The
method/role gate stays downstream unless their concrete dependency appears
earlier. The useful finite construction here removes opaque comparison for
fixed-domain certificate weakening while keeping the actual broader source
obligation explicit.

## 9. Source-derived invocation ports and interaction directions

This section derives the ordinary port directions used by §8 from the
source primitives. It also retains the input computation in the complete
invocation equation. This removes supplied direction labels for a resolved
ordinary interface graph; it does not construct a finite presentation of
every possible caller's behavior.

### Entry is part of the interface, even with a pure body

For a callable `f` distinguish the received carrier and complete call ports,
and, for a closure, its source body/result port:

```text
J_arg       the whole received computation carrier
J_body      closure body Result(I_body), with its received/rebound binding
J_call      the complete invocation observation/interface
```

The parameter mode `P` selects entry, not an eager construction prefix.
It does not by itself describe the effectful behavior of `J_arg`. In
particular, `P=Value(A)` identifies the value obtained by entry demand;
it is not a proof that the incoming carrier is pure.

For a closure, the ordinary source entry rule expands the value case as

```text
enter actual receiver; establish its source boundaries and receipt;
within its complete executing view:
    Force_argument(t) >>= (a,current_state).
    RebindResultPath(t,a,current_state);
    Run(body with x := Value(a)) >>= ReturnFromInvocation
```

For a retained computation parameter, bind the same carrier view as the
declared computation interface and enter the body without entry force.
The body's explicit consumers can still execute it. In particular, the
user-selected forwarding rule for body `x` may generate that consumer;
retaining a parameter does not imply that its body ignores it.

These equations use one actual receiver activation, current state and the
original complete view. They add no synthetic wrapper or source boundary.
When entry exposes a request, ordinary bind gives

```text
Request(q,C,k_arg) >>= suffix
  = Request(q,C, lambda response. k_arg(response) >>= suffix)

suffix = typed rebind; closure body; return from this invocation.
```

The actual raw continuation takes the current resumed state as before.
It preserves the same operation instance, request origin, response endpoint
and joint `K,D`; resumed entry does not start again. Handler selection and
any transformation of the request occur in the actual source context.
For a closure, this gives the entry/rebind/body image. Generically, `J_call`
is the complete relational image of the actual producer's `ExecuteCallable`
from §3, parameterized by `J_arg`, the environment and current configuration.
It includes the actual entry, body and designated result consumer with all
native return delimiters and the surrounding complete executing view, plus
any separately admitted result adaptation where applicable. It is not
defined by a union of two outward support rows.

In particular, an operation's native body returns `MakeRequestThunk`, not
its declared result computation. For `op: Unit -> [E]Int`, native return
alone exposes neither `E` nor an `Int` response. Its `ExecuteCallable` then
runs the existing `Execute_decl_result` after native invocation return,
within the retained complete consumer view. Entry requests keep that
post-return consumer in the complete pending suffix through ordinary bind.
This is the §3 consumer derived from the operation declaration/application
judgment; it adds no implicit force, cast or wrapper invocation. `J_body`
above names a closure's body result and must not identify an operation's
native-body return with its declared result port.

For example, a value receiver whose body returns its Int parameter has a
pure body result. An admitted carrier that requests `E` before returning
that Int exposes `E` during entry. In an ambient configuration with no
eligible handler, the complete call exposes the request despite the pure
body. Conversely, a retained-computation receiver with constant Unit body
does not execute the carrier at all. These are direct reductions of the
same rule, not source-site exceptions or decisions about Oracle lowering.
The former refutes equating `J_body` with `J_call`; the latter refutes an
exact unconditional addition of all incoming support to call support.

For the resolved ordinary core, construct a carrier port and the actual
producer's entry/bind/body/result-consumer links and return delimiters per
callable, linking each application to its actual argument port.
Recursive references share existing nodes. This takes bounded metadata per
source node plus its supplied typed-profile/path entries; it does not
invent an argument-effect generalization rule or a new surface type binder.
The symbolic complete image remains an inference obligation. The lambda
table in §6 is consequently a source body/result skeleton, not a solved
complete-call scheme.

### Derive directions from the primitive interactions

Choose a component interface root being offered to its context and mark it
`+`. A sign describes the direction of a **typed interface occurrence**:
an offered behavior at `+`, the corresponding supplied behavior at `-`.
It is neither the request's historical origin nor capture authority.
Let `-s` reverse the direction `s`.

| Typed interaction at direction `s` | Derived child direction |
|---|---|
| immutable structural component or returned value | `s` |
| callable receives whole carrier `J_arg` | `-s` |
| callable's complete invocation/result port `J_call` | `s` |
| computation emits its operation payload | `s` |
| computation receives its operation response | `-s` |
| exported raw continuation | callable at `s`, response input at `-s`, raw suffix completion at `s` |
| exposed cell read | `s` |
| exposed cell write | `-s` |

Computation introduction exposes no execution event. Explicit force opens
the corresponding computation interaction at its existing direction; it
does not recursively force a latent returned value. Whole carriers therefore
retain both their latent structure and the way their execution can later
contribute to an enclosing invocation.

**Primitive derivation.** Invocation receives the carrier from the side
opposite the offered callable and returns observations to that side.
`Request(q,C,k)` supplies its payload and suspends until a response is
supplied back. Applying the raw continuation is exactly that response input
followed by its existing suffix. Reading produces stored data; writing
consumes replacement data. These are the directions in the table. Replacing
the root side reverses each transfer, so the rules compose through nested
callables. A handler consuming an externally supplied computation has the
Function-input reversal: it receives that computation's payloads and supplies
responses. No additional handler-specific direction rule is needed.

Induction on a finite interaction derivation proves the classification for
every revealed typed path. A nested callback applies the same two call edges;
two reversals restore the original direction. Latent return, storage and
repeated resumption preserve the already-typed path correspondence and use
the same primitive clauses when activated. Shallow handler expiry changes
eligibility, not who supplies a payload or response at that typed port.

Entry/bind also links challenges to guaranteed observations. An entry
request may contribute to the complete invocation; the same dependency
can therefore occur at both an input and an output position. This is a
relational dependency, **not** equality of their outward rows. Actual
observation, routing, response and body constraints still determine the
complete image. Role bits alone cannot compute it.

### Finite classification, sharing and §8's stronger freeze

Build the direction-preserving/reversing edges from these constructors of
the resolved finite graph and its source-derived typed correspondences.
Seed exported roots positively and imported roots at their supplied side.
Propagate signs over edges; join the two bits at shared occurrences and
recursive references. Each node receives at most two bits. With a worklist,
classification takes linear work in the graph's nodes and adjacency entries
and terminates without unfolding recursive types or executions.

The construction is least: every propagated bit has a finite root-path
witness, and every root-path sign is propagated by induction on path length.
Hence all finite typed interaction paths are covered, including recursive
ones. Unknown endpoint leaves receive their occurrence signs but are not
decomposed speculatively. Finiteness of classification does not prove
finiteness of subsequently inferred type shapes or runtime alias worlds.

Writable exposure combines read and write constraints on the **same**
content view. It does not solve aliases independently. Family-argument
equality remains invariant; the operation's response occurrence and raw
continuation input retain their shared witness correspondence. Classifying
value occurrences of an operation-local binder does not permit freshening
that binder at resume or imposing family invariance on every local binder.
The original global constraints and `K,D` incidence remain joint. Opposite
signs do not cancel predicates or manufacture an equality of unrelated views.
Boundary profiles, original slots and activation references are retained;
sign propagation neither unions aliases' hygiene profiles nor creates grants.

For §8, generate assumption roots from the supplied/challenge ports and
then take its **whole-descriptor closure**, disregarding later reversals.
That checker intentionally fixes the complete challenge domain. The more
precise structural signs here do not authorize weakening a nested assumption
under §8 merely because two reversals would make it positive. The generated
classification removes that checker's supplied-label premise for this
resolved ordinary graph, while its original-certificate and complete
graph/alias premises remain. It does not extend the checker's acceptance rule.

### One joint law for domain-changing comparison

The semantic comparison can now state the missing quantifiers without a
new source mechanism. At the same `nu`, let `D_i` contain the complete
admissible challenges for description `i`: initial configuration/carrier
and admissible future input histories, with all shared dependencies. Let
`P_i(d)` bound the complete joint observations under challenge `d`.
Interpret an actual callable using its original source entry and contracts.

The sufficient containment law is

```text
D_checked subset D_actual
for every d in D_checked: P_actual(d) subset P_checked(d).
```

If the callable satisfies the actual description, each checked challenge
is an actual admissible challenge, so every actual execution observation
is in `P_actual(d)`, hence in `P_checked(d)`. This proves the semantic
law directly, including finite future/resumption histories. It uses whole
joint relations under one assignment, not separately chosen row, value,
store or family witnesses. The derived port reversals explain argument
contravariance and result covariance where a structural rule can establish
these joint inclusions; they do not establish those inclusions by themselves.

Constructing a finite symbolic presentation of the complete `ExecuteCallable`
image and these higher-order/store challenge relations remains the precise source
gate. This section derives ports/directions and the semantic containment
law. Parametric-component-linking §7 constructs executable linking and joint
recertification for finite supplied resolved interactions using these ports;
it does not generate arbitrary source templates or unknown caller domains.
The containment law remains semantic, not an effective general subtype
algorithm. Existing row and capacity
procedures can solve their stated fragments once generated; they cannot
stand in for the unconstructed interaction relation. No source acceptance
restriction, new generalization policy, lifecycle closure or implementation
approval follows.
