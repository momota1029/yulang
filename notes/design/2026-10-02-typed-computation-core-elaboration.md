# Typed computation ports: constructive core elaboration

Date: 2026-10-02
Status: Draft; no implementation authority; full raw-source elaboration remains open
Scope: finite derivation-indexed ordinary core, executable-code construction and simulation
Approved-by: none for this construction; charter §§13–17 govern its source premises
Drafted-by: primary with bounded architect construction and independent semantic attack
Reviewed-by: independent compiler_referee and spec_auditor, 2026-10-02; no blocking/major findings; minor handler-subcode construction clarification closed by primary
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
Inferred role variables are not resolved by guessing in this theorem.

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

Next close that source derivation/coherence gate together with the regular
or parametric symbolic query presentation, uniform clients and acceptance
bridge. Generalization/fresh instantiation/intrusion then preserve the chosen
presentation; implementation feasibility and implementation follow their
existing gates. No acceptance restriction or representation language is
approved merely because this core has finite executable templates.
