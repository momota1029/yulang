# R336 original source result correspondence — revision 1

Assignment `R336-RESULT`; sole author `/root/r336_result`; supplied baseline
`80b13716b`. Sprint `source-union-realization-r336`, contract SHA-256
`33d3b48f5c251eb56d8ebb4afce251b8e2575c89736121e5ab8c339386dcc830`.
The primary confirms role `astra_prover`, with no model/effort override.
Requested effective model/effort: role default, explicit values UNKNOWN;
observed model/effort UNKNOWN. No descendants.

Outcome class: **source-native-evidence / BLOCKED at the original execution
interpretation**. No new theorem, no parent-edge closure, and no Lean file
created. This is a source-owner investigation, not an impossibility theorem
or a counterexample to authoritative EI/GR3. Exact leases were this handoff,
`notes/theory/lean/YulangClosure/OriginalSourceResultCorrespondenceR336.lean`,
and `/tmp/yulang-r336-result-correspondence`.

## Unchanged parent and exact consumer

EI §§3.1–3.4 and GR3 require the selected R315 outer Call `(make 1) value`
to expose a whole-Call result only at its actual receiver Return, preserving
that result's value/root/provider/live event and the original result address.
Callee Return is an earlier, different object. All original typed responses,
resumed worlds, continuations, pending prefixes, future uses and independent
arms remain quantified. No finite replay replaces those domains. Original
A/B source scope, witness sharing and inference remain unchanged.

The existing semantic elimination target is
`OriginalSourceInterpretation.function_return_result` (lines 786–800).
Its complete source-level argument/conclusion schema is:

```text
(inputs : Inputs s) (row : ValueRow s)
(functionForm : inputs.valueForm row.descriptor = .function)
(valid : Meaning inputs (.value row)) (provider : s.Provider)
(actual : inputs.actual row.value row.root provider)
(challenge : Challenge row) (admitted : CheckedDomain inputs challenge)
(raw : RawObservation s) (executed : inputs.execute provider challenge.input raw)
(interface : s.Interface)
(readout : inputs.checkedObservation challenge raw = checkedTrace raw interface)
(result : ValueRow s)
(form : inputs.traceForm (raw.atInterface interface) = .pureReturn result)
⊢ result.event = raw.event ∧ Meaning inputs (.value result)
```

This is an existing conditional theorem, transcribed from its source, **not a
freshly checked or newly applied R336 result**. The first operational inputs
`executed`, `readout`, and `form` have no constructed selected receiver instance.
Even this theorem's conclusion supplies neither whole-Call result incidence
nor `inputs.actual result.value result.root resultProvider`.

R311 `phaseBody` lines 466–471 accepts `.returned returned result provider raw`
without retaining the preceding receiver challenge/execution. It requires an
authentic `.result` primitive leaf, result-event equality, actual result
provider, world and result membership. Supplying those as a new record would
repeat the missing conclusion. R293 `branchCatalogue` requires full
`Evidence (Meaning inputs) (branchBody ... raw)`. R306
`source_contribution_registered` additionally requires its exact source
catalogue, packet and licensed `DeclContribution` child. None is constructed
by this audit. R159's source children, original admission and Checking remain
independent. R310 `prepare` preserves `originalResult = ⟨call.site,.synthesis⟩`
and the separate generated `.completeResult` key; no native value/view handle
is substituted for either address.

## Actual native constructor and its distinct roles

Read actual `machine.rs`, not only the R335 receipt:

- `new_invocation` (2984–3003) stores `InvocationDescriptor { call, provider,
  active: true }`, where **provider has type `SourceSite`**. It identifies the
  invoked callable's source owner, not an original `s.Provider` witnessing the
  *returned result's* `Inputs.actual` relation.
- `return_value`, `Frame::ReceiverReturn` (2480–2513), constructs `returned`
  with the incoming value/view/dispatch and Value interface. The test-only
  `R335ReceiverReturnObservation` (414–424) records that tuple and the current
  owner **before** the fallible `leave_owner` call. Only after successful exit
  does the machine install `State::Return(returned)`.
- `leave_owner` (3004–3032) checks current owner and active stack, deactivates
  that receiver, and restores `previous`. Therefore pre-exit owner, post-exit
  current owner and later module-completion owner are distinct coordinates.
- `Frame::Root` (2942–2950) caches the exact received value/view/dispatch with
  Value interface. `complete_selected_definition` (3699 onward) reads the
  cached tuple immediately before `RuntimeOutcome::Completed`.
- R335 export validation (5568–5608) joins selected activation/source Call,
  current invocation, source provider site, Return tuple and later selected
  completion. It checks full value/view/interface/dispatch equality, not just
  same-value view compatibility. This is useful finite source evidence.

The authenticated R335 revision-2 artifact at
`/tmp/yulang-r335-native/r335-operation-source-r2.lean` has SHA-256
`6783f166e8da158d2bb8047300999bc6eb60284a8027d3bf236905291306b5e7`.
Its one run has response value/view 14/16 (runtime integer 10), response owner
5; Hole owner 7; selected receiver activation/current owner 8, previous owner
6; selected Return value/view 4/5 (runtime integer 7), step 63; selected cached
completion value/view 4/5 at ModuleRun, step 73. Source Call is relay occurrence
12, invoked provider site is make occurrence 7. These finite IDs are not
joined to another run and are not interpreted as original Event fields.
The immediate post-exit owner is 6 by the successful source branch; ModuleRun
at step 73 is not its substitute. The fixture supplies no original result
provider, logical descriptor, root interpretation or complete live event.

## Original execution/history owners actually inspected

Two distinct construction routes were pursued, then stopped at the same exact
missing readout rather than rephrased as conditional wrappers:

1. **Original semantic/history route.** `OriginalSourceInterpretation.Inputs`
   (324–373) leaves `execute`, `checkedObservation`, `traceForm` and `actual`
   independent. `Sorts.History`, `Configuration`, `Provider`, `Observation`
   are opaque types. `OriginalSourceEnvironment.Outcome` (91–97) is data with
   an arbitrary optional result; no execution constructor sets it.
   `OriginalSourceEvents.Returned` (513–523) is supplied semantic data, not an
   evaluator output. `HistoryStep` (735–740) is an identity record over
   `RawRecord`, not a transition derivation. `ownedEvent` (426–439) transports
   independently supplied assignments and raw Current; it does not reconstruct
   them from native IDs. Hence none establishes Return-versus-pending or the
   Call's result/provider/event incidence.
2. **Native constructor route.** `SourceIdentityWorld.returnOwned` (294–298)
   already computes `Control.leave` followed by `p.asValue`; its `suffixStep`
   distinguishes returning and done states. `identity_suffix` derives the
   exact raw tuple/control change from raw stack/registration facts. This is
   reusable operational algebra, but it has no selected original Call
   observation/IF-result interpreter. `OriginalValueEntryDemand` supplies
   pre-Force entry and a receiverReturn frame, not a whole receiver evaluator.
   `OriginalCalleeArgumentHistoryR312.Development` retains an *external* step
   relation; `pending_does_not_prepare` proves only no argument preparation
   for a pending callee. It proves no whole-Call `traceForm` equation.

A focused search of all original `traceForm` and `execute` constructors found
`OriginalNameForceExtraction.inputs` as the constructive native observation
case: it computes the **argument Name Force** readout from its tagged
observation and event fields, while `other_owners_unchanged` explicitly keeps
`execute = base.execute`. Reusing its `.returned` phase as receiver Return
would collapse Force, receiver and whole Call. R328's extension similarly
transports `base.execute`; `Generated.form` remains supplied data. The two
simple constant Inputs instances in OriginalCheckingAdmission and
OriginalFunctionFuture are countermodel/probe instances, not selected-source
execution suppliers. `NativeExecutionHistory` is an undo-table journal;
`SourceGeneratedInteraction.History` and CallTerminalTyping use their own
research machine sorts and have no selected original/native translation.
None supplies this missing interpretation.

Prior R334 `registered_read_does_not_determine_result` already demonstrates
that result registration alone leaves the result form undetermined. I reused
that boundary rather than delivering a second arbitrary-Generated probe.
R335 authentic callee/primitive source lookup is retained, but authentic syntax
does not supply these operational readouts. R335 exact tuple join is accepted
only as finite evidence; its existing tests were not rerun or recertified.

## Exact next owner and falsifier

Mutual TODO **R336-RESULT-EXECUTION-1**, owner primary/original execution
interpretation lane. Construct the selected Call's original observation
interpreter from actual callee/receiver/Request-resume transitions, under the
existing complete-Call semantics, with:

1. a source-owned observation/Current map for the same selected continuation;
2. exact receiver Return and pending equations for the existing `Inputs.execute`
   and `traceForm`, and the independently checked `checkedObservation` readout;
3. the actual result value/root/provider/current-event map at R310's original
   result endpoint, distinct from callee value and invoked-provider SourceSite;
4. original typed response/current-world and lawful whole-action domains,
   including arbitrary resumed continuations and future event/provider indices.

Apply those constructed equations to `function_return_result`, then use the
same actual result in the authentic R311 `.result` leaf/GR3 incidence and the
complete R293/R306 packet. This requests a constructor from its owner, not
permission to assume the equations or alter semantics. The present lease does
not authorize a new global Inputs instance or editing those owners.

Exact falsifiers: a claimed readout still accepts the callee Return in place
of receiver Return; changes only result view while preserving value; assigns
make's SourceSite as the result's semantic provider without a provider map;
uses owner 8 or later ModuleRun as the immediate post-exit owner 6; installs a
result at a pending/request prefix; fixes response 10 or the step-63 world
instead of preserving all original typed responses/current worlds. No further
production instrumentation is justified before specifying this interpreter;
adding more finite IDs cannot supply its missing semantic equations.

## Checks, resources, paths and cessation

Read the root/base rules, sprint contract, Lean proof/portfolio skills and exact
EI/GR3/IF/complete-Call sources. Read-only native toolchain discovery resolved
`/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`.
`lake --version` and `lake env lean --version` exited 0, reporting Lake
5.0.0-src+eb6cafb / Lean 4.35.0 (commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc).
The project has no external packages and default `-j1 -M1024`; the packet's
isolated `-M2048` allowance was not needed. One read used a repository-relative
path from the project directory and returned missing-file; all cited source
reads used the correct repository paths elsewhere. No mathematical probe failed.

No new Lean declaration was produced, so new theorem types and complete axiom
audits are **N/A**, not empty or passed. No checker/build/cache was started;
the coordinated checker remained available to the Union lane. No Rust build,
test, dependency/config change, Git, production edit or external contact.
Three substantive investigation stages; 2400-second/eight-stage grant not
exhausted; exact active seconds/CPU/RSS were not instrumented (UNKNOWN).

New paths: this handoff and
`/tmp/yulang-r336-result-correspondence/inputs.sha256` only (plus its directory).
The leased Lean path remains absent. The manifest records exact inspected
input bytes, including the native artifact, and is reproduced below. Sole
new author is `/root/r336_result`; prior source authors are preserved unchanged.

**STOPPED; writes stopped after freezing revision 1.** No processes or children
remain. Parent GR3/R311/R306/R159 closure stays OPEN. Independent acceptance,
review routing and any integration belong to Luna. The genuine obstruction is
the stop condition; no continuing background work is claimed.

## Frozen input manifest

```text
33d3b48f5c251eb56d8ebb4afce251b8e2575c89736121e5ab8c339386dcc830  tasks/agent-loop/sprints/source-union-realization-r336.md
2f3a5461b6dacaa29e881ba8b3003120b912e441dd5e4c47fc4ccaa27d3b31a6  notes/design/2026-10-24-computed-call-result-constructor.md
58ab61f7252818e208cc27be29fcc2c7633b35467c47dda0de126fa8bc87544b  notes/theory/2026-10-24-generated-computed-result-correspondence.md
4c83a095dce3636ada842bfc32c18cf0ef598db0e361861fb8e659745b74411e  notes/design/2026-10-07-complete-call-contribution-definition.md
278034197a90eab6e62a073545c09dd14415a0353f58aa3b3cc122a6af945d98  notes/theory/2026-10-08-call-source-interface-construction.md
feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef  notes/theory/lean/YulangClosure/OriginalSourceInterpretation.lean
0e12d33d1b912820324f5140fbe3f16983d0b7ef33137642aaef07faa573f132  notes/theory/lean/YulangClosure/OriginalSourceEnvironment.lean
cfd5f502a1e68a97e27e11a75400fae8789f167c92596aedb08ef7dfbb724342  notes/theory/lean/YulangClosure/OriginalSourceEvents.lean
7d230579d98b9034e62192330f98b2578629635e9810e7a7ff9195a29c813de6  notes/theory/lean/YulangClosure/OriginalComputedCallInterpretationR311.lean
077a114bf3f6f190ce4fc125f6113e411b15ea221f8183c6385e51940595ec38  notes/theory/lean/YulangClosure/ComputedCallTypedFormationR310.lean
50b1ce82dbd81d8c17a99461a78b77a9066094896f38e046d70fb4dd69365543  notes/theory/lean/YulangClosure/ComputedCallUnionRealizationR293.lean
77fa332ef53d272fe67a0c511fdebf9a3def7bf64baebfed84a3eec739ef203e  notes/theory/lean/YulangClosure/ComputedCallPhaseDescriptorR306.lean
7adcf88c1ff98c5c4cf23aa788bf5713ddcb949dd09775fb0bd542fe1e2ac577  notes/theory/lean/YulangClosure/OriginalModuleContextBindingR315.lean
219eecf85e03aae12b71b773497a9506f229832e7a7c7e8c5bf944a84063cc10  notes/theory/lean/YulangClosure/OriginalSourceScopedInterpretationR335.lean
c2e5aef86baa66304c6c575c67dd9b3cfb83f539f796e4832ffe6aa88c05dff8  notes/theory/lean/YulangClosure/OriginalCalleeArgumentHistoryR312.lean
9a171ecfbad7d632b2a15ef1f57d2d2dd46444aa36452de9158f1d1c7cfdae63  notes/theory/lean/YulangClosure/OriginalValueEntryDemand.lean
10ff6a2d4ac8a4a2c386396c495e0edfecc9bd4bb3ae40c8e0ab07e4cb0c7531  notes/theory/lean/YulangClosure/OriginalNameForceExtraction.lean
6019fd9d57cde50183e016bd0c72de2c6eee72009065d85119fb0348dbcf0168  notes/theory/lean/YulangClosure/SourceIdentityWorld.lean
edb82b9ecc62be486e057ee50152e30dad709f9a90196f78cab803838f08fb00  notes/theory/lean/YulangClosure/OriginalWorldReadout.lean
0a61ae8911ea63bd378b7d87c8e507fc10a42a9c01b2d9fdd4b1015d14a35586  notes/theory/lean/YulangClosure/OriginalSelectedEIInterpretationR334.lean
0e3ee88f1ac9c4ad4d31a4b6951b0e4bff70725715a70c96ab80f680b6b60857  notes/theory/lean/YulangClosure/OriginalInterfacePreservationR328.lean
44ad2a6d5b9ac0526ea36adc9180e0ed66e3892e48fa39aa40b20999dc7a1da6  notes/theory/lean/YulangClosure/NativeExecutionHistory.lean
16952fef6ea505cce0d7f8afa6bf39cd3609119626f7857d6beaa88737c5b003  notes/theory/lean/YulangClosure/SourceGeneratedInteraction.lean
319466c8276a638166733a28694881e3d980befd5798006ebc984907a8820a6d  notes/theory/lean/YulangClosure/CallTerminalTyping.lean
3727e1f4f32b9bed251a30224bd63b87a575d9ef84b97564f95e5774800a11c5  tools/inference-playground/src/runtime/machine.rs
b2adf7d36a23f8d366d93fe36bf9d6b21140aa51d817e3b4ca604cdead523090  tasks/agent-loop/inbox/original-receiver-return-native-r335.md
6783f166e8da158d2bb8047300999bc6eb60284a8027d3bf236905291306b5e7  /tmp/yulang-r335-native/r335-operation-source-r2.lean
ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c  notes/theory/lean/lean-toolchain
212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4  notes/theory/lean/lakefile.toml
058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3  notes/theory/lean/lake-manifest.json
```
