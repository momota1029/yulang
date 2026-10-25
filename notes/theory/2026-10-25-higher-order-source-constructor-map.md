# Higher-order proof core: constructor and native entry correspondence

Date: 2026-10-25
Scope: research representation and structural typing embedding only.
Baseline: `77df594169ad07ff9cb523699485cd0e7146e86f`.
Authority and exact dependencies: `tasks/agent-loop/sprints/higher-order-proof-core-20261025-r1.md`.
Verification and independent-review results belong to that sprint's immutable outcome.
No compiler, runtime, diagnostics, expectations or production architecture changes.

## 1. What the construction supplies

`CallEnvironmentRealization.close_body` consumes actual successful reads plus
`CellsTyped`; its values are `TypedCall.Value`. That grammar cannot contain a
`TypedCall.Function`, and `Original.Ty` cannot express a callable type. Even a
perfect free-variable layout cannot express a closure-valued cell in that model.
The new research core supplies a recursive callable type and ordinary lambda/
wrap values, with extrinsic typing after the mutually defined finite syntax.
The old Function body and adapters are translated structurally. Their existing
typing derivations construct the new value typing derivation.

This is a one-way, all-constructor typing-preserving embedding of the accepted
finite fragments. It is not typing reflection, injectivity of all evidence,
operational equivalence, source elaboration, or a full conservative-extension
proof. In particular, the old `original` wrappers disappear by structural
expansion; an Original literal and its TypedCall wrapper have the same target.

The operational paper `docs/yulang-operational-type-safety-ja.tex:85–98` declares
itself a paper construction/self-check and proposal. Its lambda/wrap/Call rules
at 220–224 and graph discussion at 258–267 are research targets, not independently
approved compiler architecture. The existing complete-Call authority's section1
records the user's authorization to supply legitimate definitions during proof
work. This packet changes no approved source behavior or original A/B claims.

## 2. Complete finite-fragment constructor map

| Existing input | Structural destination and preserved data |
| --- | --- |
| Original types: base, thunk, union, intersection, top, bottom | Same constructor recursively; same Base identity. Callable adds a new research type constructor. |
| Original values: var, unit, bool, int, floatBits, string, bytes, path, char | Same index or full literal payload; no conversion to a common string/number surrogate. |
| Original values: delay, inLeft, inRight, both, top | Same constructor and recursively translated code/value. Both retains the single underlying value and two extrinsic typing derivations. |
| Original computations: ret, force, bind, unionCase, chooseLeft, chooseRight, absurd | Same constructor and ordered children; bind/each union branch extends its own context at de Bruijn index zero. |
| TypedCall values: var, original, delay, view | Same var/delay/view; original expands the entire Original value. View occurrence identity and path are retained. |
| TypedCall computations: original, ret, bind, force, scope, expose, request, fail | Original expands structurally. Scope owner, both expose views, operation instance, saved continuation and failure reason retained. Request's continuation binds the response type at zero. |
| Adapter | Input/output types, entire body, ordered path correspondences and captured views retained. The old `typed` field supplies a new extrinsic proof; no recursive syntax depends on a typing judgment. |
| Function lambda | Mode, receipt, argument/body-result/result types, body and designated result consumer retained. Typed body parameter is A for Value and Thunk A for Computation. |
| Function wrap | Inner callable and ordered argument/result adapters retained. A function a→b becomes c→d using c→a and b→d adapters. |
| PortPath/ViewOccurrence | Structural components, port kind, recursively translated type and occurrence identity retained. |
| PathCorrespondence | Source and target paths retained with translated Prop-valued PathRule evidence. Existing proof fields are not reified into computational data. |
| OperationInstance | Operation identity, complete ordered type-argument list, payload and response types retained. |
| ReceiptTemplate/ReceiptSlot | Ordered profile, designated slot identities and paths retained. |

Context transport is pointwise: each successful old index lookup yields the
translated type at the same new index. This includes the empty-context transport
needed by old `original` terms and closed adapters under a surrounding target
context. It does not shift a free variable silently. Existing old Functions are
closed except for their explicit parameter; embedding them alone does not supply
an encoding of arbitrary native captured environments.

`PathRule` already lives in Prop. A proof of `adapterMap` cannot in general be
eliminated to recover its mappingIdentity as runtime data in Lean. The target
retains corresponding Prop evidence and explicit endpoint data; the claim is
**typing-derivation-free syntax**, not absence of every Prop field or recovery of
erased proof provenance. No new runtime evidence-erasure permission follows.

## 3. Actual source producers and consumers

Paths below are under `tools/inference-playground/src/runtime/` and pinned by the
contract. These are inspected equations, not a Lean model of the whole Rust VM.

### Lambda formation and saved environment

`program.rs:819–850` translates LocalSource Lambda with full parameter identity,
unit/record-pattern data, optional field-default labels, role, root schema,
callback schema and body label. The role is Computation exactly when the
parameter annotation has an effect component, otherwise Value. Generated member
receiver lambdas at 1042–1064 use the same role rule and retain receiver identity,
unit flag, root/callback schema and body; their record pattern is None.

`machine.rs:181–205` stores these fields in `ExecutableValue::Closure` with a
saved environment index. `Instruction::Lambda` at 864–887 creates that closure
with the current environment. `data` at 2690 creates a Value-interface
ReceivedValue with an opaque receiving view. A closure is therefore already a
native value, and introducing a formal callable-as-value representation changes
no native representation.

The formal lambda carries code and typed binders; it does not yet carry a native
label/environment index or all unit/record/root/callback fields. The accepted
native arena/capture supplier explains address lookup and current-cell reads;
source body elaboration, layout coverage and metadata realization must connect
the fields before a native closure typing theorem can be claimed.

### Callee evaluation, whole argument carrier and receiver role

`program.rs:852–857` retains both callee and argument labels in Apply.
`machine.rs:888–900` pushes a Callee frame holding the argument label and caller
environment, then evaluates the callee. When that returns, `Frame::Callee` at
1181–1201 allocates an inert Delay of the entire argument code in the caller
environment, retains its receiving view, then dispatches on the actual returned
executable. Argument execution has not started at this point.

The closure branch at 1224–1329 uses the closure's saved environment; the local
pattern binding shadows the caller-environment variable. It applies the received
dispatch substitution to that environment, establishes an invocation owner and
ReceiverReturn frame, then selects the closure's actual role. ReceiverReturn
contains activation/previous owner fields, not an environment field.

Value role pushes ValueEntry and executes the delayed argument. Computation role
creates any declared root/receipt view, binds the Delay itself as a Computation
parameter in the saved environment, and evaluates the body without forcing the
argument. This supports the formal A versus Thunk A distinction. It does not
prove that root/callback receipts or dispatch metadata realize formal paths.

A new `dynamicCall` has a value callee and a thunk-valued argument. Source Apply
also evaluates a callee computation; its eventual translation needs a preceding
bind and capture-avoiding shifts of the argument code. No all-source Apply
elaboration theorem is claimed by the Function embedding.

Native call dispatch also accepts Primitive, Continuation and operation
providers, with their own entry behavior and suffix ownership. Finite lambda/
wrap syntax is not universal coverage of these providers. Full Call adequacy
still needs those branches and its original independent quantifiers.

### Actual Value entry and patterns

`Frame::ValueEntry` at 1438–1488 first validates and introduces any callback
schema. The schema check can fail on pattern form, owner, parameter identity,
source root or received interface. It then handles record fields, unit validation
or an ordinary full parameter bind. A unit pattern validates Unit and does not
introduce an ordinary parameter cell. Record patterns bind actual fields/default
results one by one; `RecordDefault` at 1489–1498 and `bind_record_parameter` at
2655–2689 preserve the environment extended by earlier fields. Defaults evaluate
in that environment and can suspend/fail/diverge. Computation entry does not
branch on these pattern flags before binding its Delay.

The one-binder formal lambda rule covers its existing abstract body contract.
Source pattern elaboration must separately construct that body and prove the
field/default staging laws; simply ignoring pattern flags is not correspondence.

### Names and current cells

`program.rs:780–805` resolves imported names using retained imported bindings and
supplies parameter NameConsumption from the role table; other names Observe.
Inconsistent supplied consumption evidence is rejected. `machine.rs:781–862`
resolves the full parameter/local/catch identity (or global definition index),
reads the current cell, performs dispatch-name transport, then consumes it.
Uninitialized globals trigger initialization; uninitialized lexical cells fail.
`consume` at 2469–2501 validates receiving metadata, records a receipt, and either
returns the value or executes a Computation-interface value with substitution.
`execute_with_substitution` at 2551–2583 accepts Delay/Request executables and can
fail with ExpectedComputation for other representations.

Therefore a formal variable lookup alone does not prove source Name execution:
layout/address/current-value typing, observation versus execution, dispatch,
receipts and initialization remain separate source obligations. Old represented
capture typing can be transported to the new core because its actual successful
reads are already available; it cannot magically encode native closure graphs.

## 4. Parent consumption and exact remaining inputs

The selected formal endpoint turns each existing `FunctionTyped f a b` into a
value typing derivation of callable(embed a,embed b). Such a value can inhabit a
response binder, serve as a higher-order argument and be stored in the generic
native Store. The old successful capture supplier's per-index typing derivations
can be embedded without replacing its read-success premises by an opaque claim.
This removes the *missing callable value syntax* part of ENV-CALLABLE-1 only.

| Remaining gate | Exact evidence still needed / source owner |
| --- | --- |
| HO-SUBSTITUTION-1 | Capture-avoiding substitution/weakening for the new full syntax, including lambda/adapter binders and callable-valued request continuations. Owner: higher-order proof lane. |
| ENV-LAYOUT-1 | Construct finite free-variable layouts from real body labels/resolved identities, including nested source binders and pattern/default scopes. Owner: program construction plus body elaboration. |
| ENV-CELL-VALUE-1 | Encode actual current ReceivedValue/executable cells at all needed higher-order types, preserving views/interface/dispatch. Owner: machine cell producers and receiving/dispatch representation. |
| ENV-GRAPH-1 | Finite shared and recursive closure/delay graph readback and typing, including preallocated uninitialized cells. Owner: machine local/global initialization and graph proof. |
| ENV-CALLABLE-1 | Close source body using the actual layout/current cells; connect native role, patterns, result consumer and metadata to the new lambda/wrap value. Owner: program Lambda/Apply and machine Callee/ValueEntry. |
| ENV-DISPATCH-1 / RESPONSE-TEMPLATE-1 | Typed metadata/frame interpretation and error exclusion; previously proved address/replay structure is insufficient. Owner: dispatch/receiving/template constructors and consumers. |
| Whole source/Call/Force/inference A/B | All constructors, substitutions, traces, constraints, propagation, levels/generalization and original premises remain at their original owners. |

No runtime defect was demonstrated at Lambda/Callee or Value/Computation entry:
NO_SAFE_CODE_SLICE. No change to source restrictions, runtime behavior, expected
outputs, or compiler acceptance is inferred from the new research typing rules.
