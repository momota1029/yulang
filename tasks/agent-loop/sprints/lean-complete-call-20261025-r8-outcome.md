# LEAN-COMPLETE-CALL-20261025/r8 outcome

Status: **CHECK_FAILED / UNACCEPTED**. The r8 repair candidate remains a
research-only, unelaborated artifact. It proves no Call theorem, source/native
result, or production claim. The original parent and original inference A/B
claims remain OPEN.

## Exact first-check receipt

After the r8 implementation author stopped and froze handoff revision 1, Luna
ran exactly one pinned module check from `notes/theory/lean`:

```text
timeout 120s lake env lean -j1 -M1024 YulangClosure/CoreSyntax.lean
exit 1; elapsed 3.578s
```

Complete Lean output:

```text
YulangClosure/CoreSyntax.lean:263:44: error(lean.unknownIdentifier): Unknown identifier `Value`
YulangClosure/CoreSyntax.lean:274:23: error(lean.unknownIdentifier): Unknown constant `YulangClosure.Original.Comp.original`

Note: Inferred this name from the expected resulting type of `.original`:
  Original.Comp
YulangClosure/CoreSyntax.lean:280:57: error(lean.unknownIdentifier): Unknown constant `YulangClosure.Original.Comp.scope`

Note: Inferred this name from the expected resulting type of `.scope`:
  Original.Comp
YulangClosure/CoreSyntax.lean:282:23: error(lean.unknownIdentifier): Unknown constant `YulangClosure.Original.Comp.expose`

Note: Inferred this name from the expected resulting type of `.expose`:
  Original.Comp
YulangClosure/CoreSyntax.lean:283:39: error(lean.unknownIdentifier): Unknown identifier `opInstance.payloadType`
YulangClosure/CoreSyntax.lean:284:39: error(lean.unknownIdentifier): Unknown identifier `opInstance.responseType`
YulangClosure/CoreSyntax.lean:285:23: error(lean.unknownIdentifier): Unknown constant `YulangClosure.Original.Comp.request`

Note: Inferred this name from the expected resulting type of `.request`:
  Original.Comp
YulangClosure/CoreSyntax.lean:286:28: error(lean.unknownIdentifier): Unknown constant `YulangClosure.Original.Comp.fail`

Note: Inferred this name from the expected resulting type of `.fail`:
  Original.Comp
YulangClosure/CoreSyntax.lean:293:42: error: Failed to infer universe levels in type of binder `body`
  Comp.{?u.11}
YulangClosure/CoreSyntax.lean:290:10: error: Failed to infer universe levels in type of binder `body`
  Comp.{?u.4}
YulangClosure/CoreSyntax.lean:300:25: error(lean.invalidDottedIdent): Invalid dotted identifier notation: The expected type of `.bind` could not be determined

Hint: Using one of these would be unambiguous:
  [apply] `bind`
  [apply] `EST.bind`
  [apply] `EStateM.bind`
  [apply] `Except.bind`
  [apply] `ExceptT.bind`
  [apply] `Option.bind`
  [apply] `OptionT.bind`
  [apply] `ReaderT.bind`
  [apply] `ST.bind`
  [apply] `StateT.bind`
  [apply] `Task.bind`
  [apply] `Thunk.bind`
  [apply] `Std.Iterators.PostconditionT.bind`
  [apply] `Original.Comp.bind`
  [apply] `Original.CompTyped.bind`
  [apply] `Raw.bind`
  [apply] `Tag.bind`
  [apply] `Comp.bind`
  [apply] `CompTyped.bind`
  [apply] `Original.CompTyped.below.bind`
  [apply] `Comp.below.bind`
  [apply] `CompTyped.below.bind`
YulangClosure/CoreSyntax.lean:302:25: error(lean.invalidDottedIdent): Invalid dotted identifier notation: The expected type of `.scope` could not be determined

Hint: Using one of these would be unambiguous:
  [apply] `Tag.scope`
  [apply] `Comp.scope`
  [apply] `CompTyped.scope`
  [apply] `Comp.below.scope`
  [apply] `CompTyped.below.scope`
YulangClosure/CoreSyntax.lean:305:25: error(lean.invalidDottedIdent): Invalid dotted identifier notation: The expected type of `.expose` could not be determined

Hint: Using one of these would be unambiguous:
  [apply] `Tag.expose`
  [apply] `Comp.expose`
  [apply] `CompTyped.expose`
  [apply] `Comp.below.expose`
  [apply] `CompTyped.below.expose`
YulangClosure/CoreSyntax.lean:308:25: error(lean.invalidDottedIdent): Invalid dotted identifier notation: The expected type of `.adapter` could not be determined
YulangClosure/CoreSyntax.lean:332:66: error: Application type mismatch: The argument
  body
has type
  Comp
of sort `Prop` but is expected to have type
  Original.Comp
of sort `Type` in the application
  CompTyped (extend emptyContext input) body
YulangClosure/CoreSyntax.lean:336:10: error: Constructor field `argumentAdapter` of `YulangClosure.TypedCall.InterfacePlan.mk` contains universe level metavariables at the expression
  {Adapter : Sort ?u.5} → Adapter
in its type
  {Adapter : Sort ?u.5} → Adapter
YulangClosure/CoreSyntax.lean:349:28: error(lean.unknownIdentifier): Unknown identifier `Function`
YulangClosure/CoreSyntax.lean:353:52: error: Application type mismatch: The argument
  body
has type
  Comp
of sort `Prop` but is expected to have type
  Original.Comp
of sort `Type` in the application
  CompTyped (extend emptyContext a) body
YulangClosure/CoreSyntax.lean:354:14: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  resultConsumer
has type `Adapter` which does not have the necessary form.
YulangClosure/CoreSyntax.lean:354:55: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  resultConsumer
has type `Adapter` which does not have the necessary form.
YulangClosure/CoreSyntax.lean:359:61: error: Application type mismatch: The argument
  body
has type
  Comp
of sort `Prop` but is expected to have type
  Original.Comp
of sort `Type` in the application
  CompTyped (extend emptyContext a.thunk) body
YulangClosure/CoreSyntax.lean:360:14: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  resultConsumer
has type `Adapter` which does not have the necessary form.
YulangClosure/CoreSyntax.lean:360:55: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  resultConsumer
has type `Adapter` which does not have the necessary form.
YulangClosure/CoreSyntax.lean:365:14: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  argumentAdapter
has type `Adapter` which does not have the necessary form.
YulangClosure/CoreSyntax.lean:365:50: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  argumentAdapter
has type `Adapter` which does not have the necessary form.
YulangClosure/CoreSyntax.lean:366:14: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  resultAdapter
has type `Adapter` which does not have the necessary form.
YulangClosure/CoreSyntax.lean:366:48: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  resultAdapter
has type `Adapter` which does not have the necessary form.
YulangClosure/CoreSyntax.lean:374:4: error(lean.invalidDottedIdent): Invalid dotted identifier notation: The expected type of `.lambda`
  Function
is not of the form `C ...` or `... → C ...` where C is a constant
YulangClosure/CoreSyntax.lean:378:4: error(lean.invalidDottedIdent): Invalid dotted identifier notation: The expected type of `.lambda`
  Function
is not of the form `C ...` or `... → C ...` where C is a constant
YulangClosure/CoreSyntax.lean:393:15: error: Failed to infer universe levels in type of field `underlying`
  Value.{?u.4}
YulangClosure/CoreSyntax.lean:406:18: error: Function expected at
  FunctionTyped
but this term has type
  ?m.3

Note: Expected a function because this term is being applied to the argument
  function

Hint: The identifier `FunctionTyped` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and `FunctionTyped` is what Lean expects here.
YulangClosure/CoreSyntax.lean:407:20: error(lean.invalidField): Invalid field notation: Type of
  argument
is not known; cannot resolve field `carrierType`
YulangClosure/CoreSyntax.lean:407:43: error(lean.invalidDottedIdent): Invalid dotted identifier notation: The expected type of `.thunk` could not be determined

Hint: Using one of these would be unambiguous:
  [apply] `Ty.thunk`
  [apply] `CallType.thunk`
YulangClosure/CoreSyntax.lean:409:25: error(lean.invalidField): Invalid field notation: Type of
  function
is not known; cannot resolve field `sourceReceipt`

Hint: Consider replacing the field projection with a call to one of the following:
  • `CallView.sourceReceipt`
  • `Function.sourceReceipt`
YulangClosure/CoreSyntax.lean:410:20: error(lean.invalidField): Invalid field notation: Type of
  function
is not known; cannot resolve field `wrapAdapters`

Hint: Consider replacing the field projection `.wrapAdapters` with the function `Function.wrapAdapters`.
YulangClosure/CoreSyntax.lean:411:41: error(lean.invalidField): Type of
  plan
is not known; cannot resolve field `argumentAdapter`
YulangClosure/CoreSyntax.lean:411:63: error(lean.invalidField): Type of
  plan
is not known; cannot resolve field `resultAdapter`
YulangClosure/CoreSyntax.lean:419:18: error(lean.invalidField): Field projection operates on types of the form `C ...` where C is a constant. The expression
  adapter
has type `Adapter` which does not have the necessary form.
YulangClosure/CoreSyntax.lean:419:52: error(lean.invalidField): Field projection operates on types of the form `C ...` where C is a constant. The expression
  adapter
has type `Adapter` which does not have the necessary form.
YulangClosure/CoreSyntax.lean:429:46: error: Application type mismatch: The argument
  activeHole
has type
  Comp
of sort `Prop` but is expected to have type
  Original.Comp
of sort `Type` in the application
  CompTyped emptyContext activeHole
YulangClosure/CoreSyntax.lean:432:17: error: Function expected at
  ContextTyping
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  Original.emptyContext

Hint: The identifier `ContextTyping` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and `ContextTyping` is what Lean expects here.
YulangClosure/CoreSyntax.lean:443:27: error(lean.invalidField): Type of
  bodyResultConsumer
is not known; cannot resolve field `input`
YulangClosure/CoreSyntax.lean:444:26: error(lean.invalidField): Type of
  bodyResultConsumer
is not known; cannot resolve field `output`

Hint: Consider replacing the field projection `.output` with a function call such as `IO.Process.output`.
YulangClosure/CoreSyntax.lean:462:18: error: Application type mismatch: The argument
  savedContinuation
has type
  Comp
of sort `Prop` but is expected to have type
  Original.Comp
of sort `Type` in the application
  CompTyped (extend emptyContext opInstance.responseType) savedContinuation
YulangClosure/CoreSyntax.lean:476:25: error: Function expected at
  Request
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  Suffix

Hint: The identifier `Request` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and `Request` is what Lean expects here.
```

No dependent module check ran. Per contract, verification stopped on this first
failed invocation. This is an elaboration failure, not a proof attempt, semantic
counterexample, or parent refutation.

`python3 tools/agent_sprint.py check` passed as workflow-state validation only.
`git diff --check` passed. No tests, Cargo, native build, proof-hole scan,
independent review, or other Lean module check ran.

## Repair artifact and authorship

R8 implementation assignment `/root/call_implementation_r8` STOPPED; writes
ceased after handoff revision 1. Requested route was Luna/high; observed model
and effort are UNKNOWN. Exact elapsed active time is UNKNOWN; the full 1,200s
implementation cap remains charged. No proof author was launched and no later
stage grant was spent.

| Artifact | SHA-256 |
|---|---|
| `YulangClosure/CoreSyntax.lean` | `c6330ad1cf8a17b0a35f9928af82478830113f4afeb423042f74e84b0ece1916` |
| `YulangClosure/CoreSubstitution.lean` | `fc73d6d60d28f2abb54049a5715751d27df47ad93dbeb8f52966cf98a747bd2f` |
| `YulangClosure/CoreExecution.lean` | `86b4bdbf605046d7648fba803aa31eb9e96264627f123f8d14bf937813b4ef7e` |
| `YulangClosure/ControlSyntax.lean` | `1cff4497661aec68c384871f0eac0e32c34166d9ea489667791d21ce67d988d1` |
| `YulangClosure/ControlTyping.lean` | `e52aaca8baa5c3312a200952ef07fa7e304686d2642c154831de0365646a497f` |
| `YulangClosure/ControlComposition.lean` | `9a48a5f2ef15eb947478757e0fa74457579183ccdbab90f2518886590e33fc40` |
| `YulangClosure/CoreControlBridge.lean` | `30a0007aea313eccc42531bf346891c010dbed7b4b34cea1aebe7043a9a6d99a` |
| implementation handoff r1 | `4b015cdeb47e60f2cbf68537b4c47c249a1e0bbd38f06b34ea2970340c14c585` |

The author reported a semantics-preserving attempt to remove the unused
`DecidableEq`, fix declaration order and reserved identifiers, separate
function syntax from its Prop-valued typing relation, and correct request
payloads to values. Those statements are implementation claims only; the failed
Lean check prevents acceptance. The four other leased representation files are
unchanged at their r7 hashes. All 20 unchanged r8 manifest inputs were
revalidated against the frozen contract; the five edited representation files
match the handoff hashes.

## Actual execution and `Bad` boundary

The dispatcher’s source/formal audit identified an additional, unproved
successor-coverage obstruction in the frozen candidate: `ValueTyped.original`
admits the closed thunk `.original (.delay (.ret .unit))`, and the computation
typing rule admits forcing it, but `CallControlStep.forceDelay` only handles a
TypedCall-level `.force (.delay body)`. No Call successor covers
`.force (.original (.delay body))`; typed View wrappers can also surround
thunks without a matching force transition. These are static missing-successor
observations, not checked executions or semantic refutations. The Call-specific
relation need not be embedded into the existing `ControlStep` if its own
source-derived start/successor coverage and meaningful `Bad` connection are
established; absence of a `bad` constructor alone remains insufficient.

Therefore Proposition P `call_context_plug_typed`, Proposition Q
`call_step_typed_or_handoff` plus unchanged A
`call_context_plug_preservation`, and B
`bounded_call_finite_prefix_safety` remain OPEN and **unissued**. The
implementation-to-proof seam is still blocked. No theorem or reviewer can use
the failed candidate as a checked premise. Full decorated-plan authenticity,
effect hygiene, frontend/source/native correspondence, arbitrary foreign-tail
safety, principality, termination, and the full parent remain OPEN.

## Continuation boundary

R8 is unaccepted. Its implementation cap is charged; its first 3.578s primary
check is recorded; P/Q/B and review grants were gated and not issued. No unused
stage budget is transferred. A fresh versioned contract and exact implementation
lease/resource grant are required to repair the remaining elaboration and
successor-coverage issues. Preserve the original A/B quantifiers and source
domain. Do not use proof budgets to hide an implementation/semantics expansion.

The dispatcher confirmed that a separate Call relation may be acceptable if
its start/successor coverage is independently justified and its `Bad` argument
is substantive. The frozen candidate still misses successors: the admitted
typed value `.original (.delay (.ret .unit))` may be forced, but the Call
relation only handles a TypedCall-level `.force (.delay body)`; it has no rule
for `.force (.original (.delay body))`. Typed View wrappers can also surround
thunks without a corresponding force transition. These are static omissions,
not a checked runtime counterexample or semantic refutation. R8 is therefore
closed CHECK_FAILED/UNACCEPTED; its P/Q/B grants remain unissued and
nontransferable.

At the r8 failure boundary the dispatcher proposed fresh r9, “checked Call
execution adequacy”: repair the remaining elaboration, add the source-required
embedded/View-wrapped thunk steps, and define a raw execution relation that is
independent of typing and typed Call steps and admits genuine malformed-input
`Bad` outcomes. Then prove forward simulation and typed-image successor
coverage, including actual substitution, Req/Fail, metadata, world changes and
the arbitrary literal suffix. Fresh proof lanes S (`call_step_erasure`) and C
(`call_raw_successor_coverage`) may run in parallel only after implementation
freeze and checks. P/Q/B are not dispatched in r9; the original claims remain
OPEN for a later authorized sprint. The existing `Original` raw-simulation and
lifting proofs are method evidence, not assumed results for Call.
