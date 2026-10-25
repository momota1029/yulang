# Higher-order substitution, capture and entry: source map

Date: 2026-10-25
Baseline: `98118c2933694a03fcbf443a4cd638e350f76394`.
Scope: checked research core typing constructions; full source/native adequacy OPEN.
Contract: `tasks/agent-loop/sprints/higher-order-substitution-entry-20261025-r1.md`.
Verification and independent review are recorded in the sprint outcome/receipts.
The previous independently reviewed constructor inventory is
`notes/theory/2026-10-25-higher-order-source-constructor-map.md`; its exact bytes
and all native source dependencies are pinned in this contract.

## 1. New parent application and its limit

The preceding milestone embedded old Functions as genuine HigherOrder.Value
callables. This packet supplies capture-avoiding substitution for the entire
higher-order grammar, then consumes a constructed callable in an actual generic
current-cell read, finite capture realization and body-closing operation. The
selected endpoint must discharge that constructed store's cell typing using
`embedFunction_typed`, rather than assume arbitrary native cells are typed.

The general theorem remains conditional on successful current reads, a correct
finite layout and typing of those represented current values. The concrete
fresh-cell/callable application supplies its read and cell-typing hypotheses.
This is a real instance of the new supplier, not readback of a Rust Closure.
The source-to-layout map, native ReceivedValue interpretation and shared/recursive
closure graph are distinct OPEN premises. A direct cell Reference used for a
fresh generic store address does not assert that a local cell is a source
ModuleDef or belongs to the native preallocated global definition table.

## 2. Exact binder ownership

The immutable accepted HigherOrder typing rules are the authority for these
research algebraic proofs. The syntax contains value-variable binders only;
this packet does not claim type-variable/polymorphic substitution or full Raw
binder coverage. Value substitution leaves types and operation instances intact,
including every ordered type argument, receipt, path and view occurrence.

| Position | Environment used by its typing rule | Transformation |
| --- | --- | --- |
| lambda body, Value mode | extend outer A | Lift through one parameter binder. |
| lambda body, Computation mode | extend outer (Thunk A) | Same index lifting, distinct bound type. |
| lambda result consumer | outer | Transform the Adapter in the outer substitution; no lambda-parameter lift. |
| Adapter body | extend outer input | Adapter itself introduces exactly one input binder. |
| bind body | extend outer first-result | Lift once; first computation uses outer substitution. |
| unionCase branches | extend outer left / extend outer right | Lift each branch separately. |
| request continuation | extend outer response type | Lift once; payload uses outer substitution. |
| wrap inner/input/output | outer | Inner value and both adapters use the same outer substitution; adapter bodies lift themselves. |
| delay, view, scope, expose, dynamicCall | outer | Recurse through their actual value/code children, retaining metadata. |

The critical nested-lambda case has two different index-zero meanings. Index zero
inside the lambda body is its parameter; index zero inside its consumer's body
is the consumer input. The consumer does not capture the lambda parameter. For
example, an outer value referenced by index one in each body is replaced once
in each case; lifting the consumer once for the lambda and again for the adapter
would mistakenly retain or capture the wrong variable.

Closed Original nodes in old TypedCall syntax were protected from old Call
rename/substitution. The new structural embedding exposes their internal terms.
Thus an untyped old `.original (.var 0)` is a concrete counterexample to an
unconditional old/new commuting equation: old Call substitution leaves it intact,
while target substitution changes its image `.var 0`. Old typing excludes that
open Original term through its empty-context premise. No accepted old theorem
is weakened, and no unrestricted commuting theorem is asserted here.

## 3. Native lookup and substitution are different operations

Paths in this section are under `tools/inference-playground/src/runtime/`.
The reviewed NativeClosureEnvironment construction already establishes finite
nearest-binder lookup, old-environment address stability and fresh Store.push
observation. `machine.rs:2585–2638` is the actual lookup/append/bind owner.
Lookup follows immutable parent indices to a full binder identity, returns a
cell address, and the Name consumer at 781–862 reads its CURRENT ReceivedValue.
Cells can be filled after closure formation, including recursive initialization.

The native function named `substitute_environment` at 2606 is not syntactic
value substitution. It composes dictionary dispatch substitutions and optionally
appends a binder-free environment node. It neither rewrites code nor replaces
lexical values. The new de Bruijn substitution is a mathematical interpretation
of successful lexical capture; its native adequacy requires the source layout
and current-cell relation. Conflating these two operations would leave the
central body/environment premise unproved.

`ReceivedValue` at machine.rs:165 contains value handle, interface, receiving
view and optional dispatch. New generic Store cells contain already represented
HigherOrder.Value. A proof about the latter does not erase or validate the former
fields. Their source representation/typing remains ENV-CELL-VALUE-1 and
ENV-DISPATCH-1; finite lexical addresses alone do not solve recursive value graphs.

## 4. Callee-first Apply and entry modes

`program.rs:852–857` retains both callee and argument code labels. Native
`Instruction::Apply` at machine.rs:888–900 evaluates callee after pushing the
argument and caller environment. `Frame::Callee` at 1181–1201 allocates an inert
Delay of the whole argument in the CALLER environment, then selects the actual
returned executable. The closure branch at 1224–1329 enters the SAVED closure
environment after dispatch substitution. The previous inventory covers each field.

The corresponding research computation is structurally

```
bind callee (dynamicCall (var 0) (delay (rename argument Nat.succ)))
```

Here `argument` is a computation typed in the original surrounding context.
The shift places every original free value index beyond the new callee binder;
all binders within argument code lift that shift. This construction retains an
inert delay rather than placing argument execution before the callee bind.
Its theorem proves typing of this actual term. It is not a complete source Apply
elaboration or a proof about native request/suffix traces.

Value entry pushes ValueEntry and executes the delayed argument; when it returns,
ordinary parameter binding at machine.rs:1476 uses that received value. A typed
force/bind composition models this formal body's A parameter. Computation entry
at 1298–1329 binds the carrier itself at Thunk A and immediately evaluates its
body; formal substitution of the UNFORCED carrier models that body entry.
There is no extra force in that construction. A body may later force its formal.

`Frame::ValueEntry:1438–1488` also validates callback schema/owner/identity/interface,
handles unit patterns without an ordinary parameter cell, and delegates record
patterns. `RecordDefault:1489–1498` and `bind_record_parameter:2655–2689` preserve
sequential field/default scope. These cases require source pattern/body elaboration
and metadata evidence before a single-binder formal body applies. The research
proof adds no source restriction and does not silently claim those checks succeed.

## 5. Result consumers and wrap projections

The accepted old formal entry supplier is `CallEntryTypingRepair.lean`;
`CallPeelingTyping.lean` tracks wrap argument delays and ordered result adapters.
The historical failed `CallEntryTyping.lean` is not an accepted proof dependency.
The new higher-order constructions use the actual Adapter body under its own
input binder and preserve the c→a argument / b→d result directions around a→b.
A delayed input-adapter composition must remain under delay; result consumption
follows the invocation body's result. Existing receipt, paths and captured views
remain attached to the retained adapter/entry plan.

Native `ExecutableValue` has Closure/Delay/Request/Continuation/Primitive cases,
not a direct Wrap case. There is no established all-source map from every formal
wrap/result consumer to that native enumeration. `Frame::ReceiverReturn` at
machine.rs:1430–1437 leaves the invocation owner and transports the returned
ReceivedValue; this fact alone does not execute or certify an arbitrary formal
result adapter. Correspondence with actual source-generated adapter plans and
receiving/dispatch transitions remains OPEN.

Accordingly, typed body projections are computations inside the research model,
with full original adapter/receipt data retained by their plan. No body-typing
lemma grants runtime metadata erasure, supplies fresh invocation/receipt identities,
or proves owner retirement, continuation replay or dispatch error exclusion.
The paper remains a proposal; no new production semantics is adopted.

## 6. Remaining gates and next concrete consumers

- HO-SUBSTITUTION-1 can close for the accepted HigherOrder finite grammar only
  after all mutual cases and lifts check and pass independent review.
- The constructed callable-cell/body theorem supplies one genuine instance of
  ENV-CALLABLE-1's body-closing input. Arbitrary native Closure/Delay current-cell
  readback, complete layouts and recursive graphs remain ENV-LAYOUT-1,
  ENV-CELL-VALUE-1 and ENV-GRAPH-1, at program/body/initialization owners.
- Typed force/bind, computation entry, consumer/wrap and source Apply expressions
  are not a full HigherOrder operational machine. Progress/preservation for
  actual transitions and all source/native trace correspondence remain OPEN.
- ENV-DISPATCH-1 and RESPONSE-TEMPLATE-1 still require typed receiving/dispatch/
  frame interpretation and errors exclusion beyond the reviewed structural
  environment/template suppliers. Force and original inference A/B retain their
  original scope and owners.

NO_SAFE_CODE_SLICE: the inspected Callee and ValueEntry/Computation owners expose
no demonstrated runtime defect. No compiler/runtime/expectation/config change or
native test is authorized by this proof packet.
