# R343 higher-order correspondence — frozen handoff r1

Assignment `R343-CORRESPONDENCE`, worker `/root/r343_correspondence`, baseline
`944dff732`. Contract `tasks/agent-loop/sprints/higher-order-source-correspondence-r343.md`,
SHA-256 `0e069ab7fafbd6b9f62a674ad82e3234b6ebd088a189c2e3513eb9ca68060bfc`.

**Result: checked candidate source projection with the operation request-carrier
Return and forcing consumer in their correct relative order. Actual native/original
simulation and the original R311/R306/R159 parent remain OPEN.** This is a
phase-order improvement over R342, not certification of native correspondence.
Fresh independent review and adoption belong to the primary.

## Parent and source scope

The unchanged whole parent is `SourceProblem.InferenceSoundness`:
`∀ s x d a, supported s → generates s x d → solves d a →
∃ e, sourceJudgment s x e ∧ sameScoped s x e a`.
The immediate parent retains original source Call/EI-All Union, full independent
arms, licensed child/result fields, both R159 checking obligations and one shared
admitted extension. No original Inputs, semantic domain, source judgment or
ordinary inference rule is changed.

Read selected EI `2026-10-24-computed-call-result-constructor.md` §§2–5,
adopted source-Generalize definition §2, and reviewed bounded operation
construction `2026-10-16-operation-primitive-image-contract-construction.md`
§§2–4. The last source retains independent store/typing/profile/admission laws
and expressly grants no semantic adoption. These sources require native
Return(MakeRequestThunk), delimiter, then the declaration consumer; request
resumption preserves the current world and whole ordered suffix.

The canonical source remains R315's decoded initializer
`lambda seed. { tick seed; lambda argument.argument }`. The partial projector
handles the same unannotated integer/Name/primitive/App/Value-lambda/expression
block fragment as R342; other constructors fail explicitly. Only the canonical
R315 initializer is certified. Primitive lookup uses that fixed source inventory,
the original full Key and primitive-use discriminator, then R336's complete
physical declaration/signature resolver. It is not a general source interpreter.

## New construction and actual application

All 11 new theorems are in
`YulangClosure.OriginalHigherOrderCorrespondenceR343`.

`operationCarrierValue receipt op` has body result `thunk op.responseType`:

```text
lambda Value payload.
  Return(Delay(Request(op, payload, Return(response))))
  |> forceAdapter
```

The forcing adapter has input `thunk a`, output `a`, and body `force(var 0)`.
This replaces R342's immediate Request plus post-response identity adapter.
The operation is still represented by an HO lambda entry plan: native operation
provider identity, native invocation return and delimiter metadata are NOT
thereby modeled or certified.

- `force_adapter_typed` and `operation_carrier_value_typed` independently type
  this carrier/consumer for arbitrary context, receipt and operation.
- `actual_source_projection` derives the new projection from the same authentic
  R315 tree, for every source origin, result type and receipt decoration.
- `body_typed`, `make_value_typed`, `program_typed` construct the body, lambda
  and source-call typings without supplied body-safety premises.
- `forcing_consumer_before_request`, for every operation and payload, proves
  `consumeResult (ret (delay (request op payload (ret var0)))) (forceAdapter ...)`
  takes two silent steps to `request op payload (ret var0)`.
  **This lemma is applied inside `actual_prefix`.** It is not an unused side fact.
- `actual_prefix` derives ten HO steps for every `a`, `receipts`, integer `seed`:
  callee bind; make entry; payload force/rebind; tick callee bind; tick entry;
  tick payload force/rebind; request-carrier Return/consumer bind; consumer Force.
  The saved context has only block-discard/final-lambda and make-result consumer.
  There is no pending tick-result identity consumer after the Request.
- `actual_capture_typed` applies `Interaction.capture_typed` to that derived
  prefix and typing, producing `SavedTyped (saved a receipts seed) (callable a a)`.
- `actual_response_return` proves two silent return steps to the original final
  identity lambda for **every HO response value**, without selecting one response.
- `decoded_source_prefix_and_return` starts with R315's native initializer decode,
  derives the new source projection/request identity/prefix, and applies the
  existing `Interaction.saved_resume_typed` consumer to **every closed TypedCall
  typed tick response**, including its whole ordered view wrapper chain. It uses
  the same arbitrary literal outer context, with its independent hypothesis
  `ContextTyped emptyContext suffix (callable a a) result`. It proves resumed
  typing plus the two-step return under that same context.

All complete theorem types and transitive axiom reports are retained in
`/tmp/yulang-r343-correspondence/CorrespondenceAudit.log`; names are in
`theorems.json`. The theorem types contain no native state/world relation and
must not be read as asserting one. Arbitrary receipt decorations remain arbitrary.

## Native source evidence and exact remaining correspondence

Read the actual current `tools/inference-playground/src/runtime/machine.rs`:

- `return_value`, Operation provider branch, lines 2424–2510: reads the resolved
  declaration/signature and authentic provider, opens an invocation, pushes
  `OperationResultConsumer`, `ReceiverReturn`, then strict `OperationPayload`.
- `OperationPayload` at 2118 and `make_request_carrier` at 3736: native body
  returns inert `ExecutableValue::Request { declaration, payload, source }`.
- `OperationResultConsumer` at 2122 executes that carrier after receiver return;
  `execute_with_substitution` request case around 4053 allocates the request event
  and observes the current execution views. Thus the forcing phase precedes
  Request publication. R343's local phase equation matches this relative shape.
- `propagate_request` at 3456 captures the remaining block, owner boundaries,
  outer callee and view frames; `capture_template` at 3148 retains these and
  adds the containing owner. `enter_template` at 3235 resolves live/fresh owners,
  recreates `TemplateNode::View` execution with `receiving.execution`, and only
  then returns the response at Hole. `end_execution_view` at 3417 checks the
  exact view/receipt/occurrence on completion.

R315's embedded Current request event does not export the request suffix or
response-time world. The stronger **separate-run** final R324 artifact was read
and its actual hash revalidated:
`/tmp/yulang-r324-native/r324-operation-source.lean`,
`85e663b65a893b0acd5de46b7b1b59e940098bf5e5a7815cada4736a3e983551`.
It retains full operation identity/signature, payload integer 1, request owner 2,
response integer 10, and saved order
`Block(next1,env3); Owner(2); outer Callee(frame2,env2); Owner(1); RootCompReturn`.
Its template replays inactive owners 1/2 with fresh owners 6/7. These numbers
are local to that artifact; none is identified with the R315 run or semantic
`OriginalSourceInterpretation.Event`. The stored RootCompReturn execution is
historical; the exported artifact does not include the freshly recreated View
execution/store transition. The later CalRet snapshot is not its response world.
No new native run or fresh Lean elaboration of that artifact is claimed.

Consequently the source-qualified relation needed next must account for the
native delimiter, runtime provider, actual receipt/profile, live/fresh owner
transition, View re-execution and exact whole saved suffix. HO `Interaction.State`
contains only current computation, saved arena and phase. R343 does not supply
those missing fields or a relation showing they are legitimately abstracted.
Its synthetic lambdaEntry cannot be renamed an original operation receipt.
A finite native trace cannot establish its laws for all admitted responses/worlds.

At the original outer Call (R315.selectedCall; source sites 1/2/3, distinct from
inner tick App 3/4/5), R311 `primitive_introduction` still requires an authentic
`PrimitiveLeaf`, exact `resolution goal = some leaf`, and
`leaf.entry.before.Holds inputs registry.original` for the original calleeRequest/
calleeResume signature. R343 derives none of these. No R306/R293 Union field,
R159 admission/checking premise or original source judgment is eliminated.

## Prior work and next owning TODO

Reused R342's lexical projection pattern, identity lambda, literal-context
lifting, native initializer decoder, and R336 physical-operation resolver.
Changed the actual operation body/consumer and saved response boundary; the
R342 direct-request/identity-adapter phase placement is not reused. R324/R325's
original predicate obstruction remains valid under its actual premises.
No duplicate source-identity/response wrapper or empty-registry counterexample
was added. The parent's later direction to try the existing HO carrier/forcing
constructors enabled this additional bounded construction before freeze.

`R343-NATIVE-HO-RELATION-1`, owner primary/source-native proof lane: construct an
independent state relation for this exact operation-carrier path, including live
owner/View replay and consumer completion, preserving original source identity,
provider, response/current-world, receipt and suffix. The concrete falsifier is
one admitted response/current-world whose replayed owner or View occurrence,
provider or saved frame order has no matching related transition. Do not assume
that related target state or final membership as a component law.

Provisional implementation evidence TODO (no production edits authorized here):
first inspect existing R335/R338 hooks, then, only under a new primary lease if
needed, export the actual View recreation and completion pre/post receiving state
at `enter_template`/`end_execution_view`, joined to the same request/template and
response. Mutate the recreated occurrence or receipt while preserving the old
captured pair; authentication must reject it. This evidence can authenticate a
sample, not replace the universal relation or original primitive laws.

Original semantic TODO remains the authentic source-to-fixed-Inputs/registry
projection from independent original operation laws, with lawful whole-tuple
restriction and all independent arms. New semantics or broader leases return to
Luna. This packet stops at this boundary.

## Checks, hashes and cessation

Pinned native Lake/Lean 4.35.0 were observed; Lean commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, Lake `5.0.0-src+eb6cafb`.
Copied the previously built R342 isolated project/cache, checked all 91 imported
source files against current repository bytes (identical), and compiled the new
module twice with `LEAN_NUM_THREADS=1`, `-j1 -M2048`; both exited 0. No failure,
new dependency, pin/config change or shared-cache write occurred. The source
cone including R343 has 92 files. This is cache reuse, not a claim of 92 fresh
builds. Complete generated cache hashes are retained.

Used the bundled checker's unchanged `audit_source` and `validate_audit`, with
manual pinned execution at the granted 2048-MiB limit. All 11 theorem-kind/type/
axiom checks passed. The CLI driver was not run: it forces the already known
1024-MiB path. No full/default-root integration, Rust test or independent review
is claimed. The source scan's 20 matches are comments or existing audit rejection
strings, not proof holes, project axioms or checker bypasses.

Axioms: `actual_capture_typed` uses `[propext]`; `actual_source_projection` and
`decoded_source_prefix_and_return` use `[propext, Classical.choice, Quot.sound]`;
the other eight theorems use none. No `sorryAx` or native-evaluation assumption.

Frozen Lean SHA-256:
`5e1863f8a384b603f2cb985b088a9c9cef0a935563cab83ea7438507c267c88f`.
Audit log: `6a95e30ffcda18fa981fb962ee267dbf455b8a519f328ebffb933ee3d7e64e01`.
Dependency-source manifest:
`14edf0602f532bf7493e87e2e1d00b37ddcf8fd2a9c49870301caad8a6af5915`.
Axiom JSON: `b8590e1a20b65b75c0a9c3b14b4d4c3d64c90b65febfc08fda7472a551ca379c`.
Consulted authority/native/history hashes are in `input-hashes.json`;
current native machine hash is
`1832020d095134dd69637bb1eb8f9eea70499037124c0654417190d6dba78803`.

Sole new author: `/root/r343_correspondence`; prior R342 definitions/proof pattern
by `/root/r342_source_prefix`. No descendants. Requested/effective model and
reasoning effort launch metadata were not visible to this leaf: UNKNOWN.
Budget: 3600 seconds/eight stages; five substantive stages completed. Whole-turn
elapsed/peak memory not measured. Individual build/audit timings and commands
are in the two target command JSON files and `audit-command.json`. No process
remains; checker slot was released to the primary.

Only leased repository outputs: the new Lean file and this handoff. All scratch
writes are within `/tmp/yulang-r343-correspondence`: copied `project/` including
cache, `input-hashes.json`, `dependency-hashes.json`, `dependency-cache-hashes.json`,
`r324-inspection.txt`, `versions.txt`, target-1/2 logs and command JSON,
`CorrespondenceAudit.lean/.log`, `audit-command.json`, `theorems.json`,
`axiom-results.json`, `source-audit.txt`, and `final-hashes.json`.
No compiler/tests/root import/shared records/Git writes occurred.
**All writes stopped at this frozen revision; no running processes or descendants.
Candidate proof is ready for independent review, not self-certified or production-ready.**
