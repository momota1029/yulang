# Runtime entry-plan import: source-owner audit

Date: 2026-10-16
Status: frozen static source characterization reviewed CLEAN within bounded
source/authority scope; no theorem closure, architecture selection, compiler
change or production authority.
Baseline: `516cdedd9bb52f4f1d1e28a4f69f388d3c481bee`.
Lease: this note only. Method: trace actual constructor outputs and public
playground argument flow; no executable experiment.

## Governing premise and precise result

The reviewed [callable-view construction](../theory/2026-10-16-runtime-callable-view-construction-and-transport.md)
§§2–8 consumes an original independently valid typed derivation T. Its
Entry/Exec/Return construction preserves the original interfaces, typed maps,
both tagged Return inputs, scopes and unknown dependencies. The
[source export theorem](../theory/2026-10-16-runtime-function-result-source-construction.md)
§§1–6 explicitly does not establish native-to-T supply. The selected
[first-call constructor](../design/2026-10-16-known-function-first-call-profile.md)
§2 and [receiving actions](../design/2026-10-16-receiving-profile-introductions.md)
§2 govern only their stated two-Call component. Typed-core §§2–3,9 and
typed-boundary §6 distinguish full invocation, actual entry, observation and
two-input return transport. None authorizes reconstructing T from a runtime tag.

**Bounded characterization:** the current playground run does not pass T or
an equivalent complete plan from inference into the VM. There is useful
retained native evidence at narrower constructors; it must not be described
as wholly absent. The first executable handoff lacking that plan is
`tools/inference-playground/src/lib.rs::execute` →
`runtime/program.rs::RuntimeProgram::from_hir`.

## Actual public path and evidence classes

1. `lib.rs::prepare` (lines 189–285) parses and lowers with
   `lower_module_with_local_source`, runs `CandidateInference::solve` or
   `solve_scoped_experiment`, checks candidate conflicts, and returns
   `(Arc<HirModule>, CandidateInference)`. A conflict-free private candidate
   is not an independently valid source derivation: `shadow_apply.rs::UNRESOLVED`
   still includes SourceTypingAndAdmission, CompleteInvocationImage,
   CompleteFunctionInterpretation and WholeArgumentProviderCompatibility.
2. `lib.rs::execute` (lines 142–157) binds `(hir, _candidate)` and calls
   `RuntimeProgram::from_hir(hir, RuntimeEvidence::default())`. It neither
   requests a source-call/computation-plan observation nor forwards the solver.
3. `RuntimeEvidence` (`program.rs:55`) contains one occurrence-indexed map,
   `name_consumption`. `from_hir` derives parameter Name consumption from the
   original formal's outer `effects` presence, derives Observe for other
   Names, and rejects supplied entries disagreeing with that choice
   (`program.rs:312–367`). This evidence map is a consistency check for those
   Names, not a typed plan supplier.
4. HIR `LocalSource` retains authentic source forms, occurrence/binder/scope
   identities, original annotations, Apply children, local bindings and Catch
   patterns. `SourceAnnotationType` retains nested Function argument/result
   syntax and effect-row positions. These records supply source identities
   and written contracts; their structures contain no complete typed action
   graph or dependent Return recipe.

Consequently the candidate's acceptance cannot fill the missing plan through
this API: the candidate is discarded at the call edge, and the remaining
inputs retain identities/annotations plus Name modes rather than T's typed
maps and complete action interfaces. This is source inspection of the pinned
path, not an information-theoretic impossibility claim about future exporters.

## First constructors, existing outputs and actual consumers

| Fact | First concrete construction/retention owner | Present consumer and missing plan field |
| --- | --- | --- |
| Original formal and written Function result | `yu-hir/src/module/local_source.rs::form_ordinary` builds named `LocalSourceParameter`/Lambda from admitted syntax and `parse_annotation`; inline Lambda construction records its own parameter. `source_annotation.rs::SourceAnnotationValue::Function` retains nested argument/result types. | `program.rs:382` builds Lambda with formal ID, role, bounded RootComp schema and body label. It retains no complete Function profile, result map or source EntryPlan. HIR remains owned by `RuntimeProgram::_hir`. |
| Native formal root and role | `candidate_source.rs::ConstraintBatch::emit_candidate_source:600` records `FormalRegistrationInput`; `initialize_candidate_source_levels:1202` installs its positive Parameter root and a Comp entry row. `lib.rs::admit_lambda_fact:11317` constructs Function coordinates from the actual argument/body endpoints and records entry/body effect constraints. | `CandidateInference::computation_source_plan` borrows the authentic Comp registration/annotation/root/entry row. This is not a VM input. It does not independently establish Function/AE/FreshUse correspondence. |
| Source Apply and native result | `emit_candidate_source:981` retains the Apply relation; `ApplySourceInput:1040` records original callee/argument, result, application effect, checking occurrence/cause and recipe. `CandidateInference::source_call` exposes source/native operands. | `Instruction::Apply` stores callee/argument labels only. `Frame::Callee` receives the actual callee packet but dispatches on its value handle; no consumed callable view or full Exec/Return plan is saved. `PendingCallSupplier` still names missing whole interface, entry route, Gen-Call-0, whole carrier and complete result/future suppliers. |
| Actual entry | `machine.rs::return_value`, Callee branch (`:651`), allocates the whole inert argument Delay and creates the actual invocation. | Closure Value entry pushes `ValueEntry` and executes Delay; Comp entry optionally calls `Receiving::enter` with RootComp schema then binds Delay. The complete Function view is absent before Force/retention. `direct_formal_root` supplies only its authentic special case. |
| Operation designated result consumer | HIR `SourceOperationDeclaration` retains signature/identity. `candidate_effect.rs::candidate_operation:806` constructs its candidate signature with a shared declaration environment. | Callee operation branch (`machine.rs:743`) selects entry from declared argument, pushes `OperationResultConsumer` below native `ReceiverReturn`, and later calls `execute(received.value)` (`:649`). That ordering preserves the distinct consumer, but its frame stores only source location; the whole returned packet/declared typed recipe is not consumed there. |
| Raw continuation answer coordinate | `emit_candidate_source` CatchArms (`:769`) retains operation response declaration plus original scrutinee endpoint/effect. `candidate_effect.rs::candidate_catch_operation:826` builds continuation argument from declaration response B and result coordinates from `candidate_endpoint(original, ±)`, with provisional conservative full-scrutinee effect bounds. | VM handler selection allocates `ExecutableValue::Continuation(template)` with an opaque view (`machine.rs:1322`). `ResumeArgument:565` validates B from the declaration; `ResumeReturn` forwards completion. No source answer-result interface/recipe is exported into the template. Native result coordinates are existing evidence, not proof of the exact saved-suffix answer interface. |
| Saved context and completion | `capture_template:1002` folds pending frames into immutable Bind/Owner/ForwardHandler/View nodes and retains declaration/event. | `ResumeTemplate` (`continuation.rs:14`) has nodes/root/declaration/event only. `TemplateNode::View` retains root `ExecutionView`; restoration uses its old view/receipt (`machine.rs:1153`). It has no callable port, dependent ReturnSlot/recipe or answer-interface field. |
| Actual Return and storage | `ReceivedValue` retains value/interface/view; Local, ValueEntry and ReceiverReturn preserve the actual returned view in their bounded roles. | RootComp completion (`machine.rs:601`) calls `ground(received.value)` after closing its execution. There is no tagged join of actual-value packet W and retained consumed-view result input V. Saving a local view alone does not supply that second input. |

## Smallest source-owner discriminator

Use the already selected annotated formal `f : Unit -> alpha+` in the
two-Call component. Its outer annotation has `effects = None` and
`value = Function { .. }`. Reading the constructors directly gives:

```text
FormalRegistrationInput.role = Value
observe_computation_source_plan(f) = Ok(None)
RootCompSchema::from_parameter(f) = None
Instruction::Lambda.role = Value
```

The first equality follows from `emit_candidate_source`; the observer returns
None for a consistent Value registration at `candidate_call.rs:219`; the
schema rejects both absent outer effects and nonprimitive Function value at
`receiving.rs:22`. This is a static discriminator for the existing export
surface, not a parser run, source-admission certificate or counterexample to
the reviewed conditional construction. Increasing Comp-root probe counts
cannot touch this Value(Function) premise.

## Existing lawful inputs and exact residual owner

The existing HIR records can lawfully provide original Lambda/formal/annotation,
Apply/Name/binding, operation declaration and handler/control identities.
`CandidateComputationSourcePlan` can provide its checked Comp registration
projection. `CandidateSourceCall`, retained Lambda recipes, candidate graphs,
fresh-use/scoped observations and Catch construction can supply their actual
native coordinates and constructor links, under their stated unresolved
premises. Reuse these outputs where their claims apply; do not convert their
names or successful observation into independently valid T.

The missing **semantic supplier** is the construction/checking owner that
establishes independently valid typed source actions and exports their complete
Entry/Exec/Return fields for this component, including the Value(Function)
formal, two-input Return maps and continuation answer interface. The missing
**executable importer** is the `execute`/`from_hir` seam, followed by the exact
Lambda/Callee/completion/template consumers above. Existing narrow observers
do not implement either complete obligation.

The reviewed source-plan extraction gives a lawful route *conditional on T*;
an independently checked compiler export would instead have to establish its
source premises at those construction owners. This audit chooses neither
route and selects no eager/DAG representation. Annotation parsing and native
graph traversal alone cannot close the semantic supplier premise.

Recommended next action: primary leases a bounded supplier obligation for the
original Value(Function) formal and its two actual Calls, identifying precisely
which independent typing/action premises an import or checked export must
establish before any dependent production implementation.

## Verification, coverage and dependency manifest

Static commands: bounded `rg -n` constructor/call-site searches and line reads;
`git show` baseline reads; Python SHA-256/live-byte comparison for all 18
dependencies below, plus an earlier narrow `git diff --exit-code` check of
`candidate_effect.rs`. All 18 equal baseline. A broad locator
search included nonexistent directory `playground` and exited 2; corrected
reads used `tools/inference-playground`. No search result from that missing
directory is claimed. A search for exact EntryPlan/ExecPlan/ReturnPlan and
SolvedTask/RuntimeEvidenceTask names found no Rust definitions under crates/tools;
the stronger absence conclusion above rests on inspected structs and call flow.

No oracle, seeds, ranges, mutations, tests, builds, runtime probes or network.
This audit shares the reviewed source theorem's selected source rules; it
independently checks current source ownership/argument flow only. It does not
validate those semantic rules, source admission, full native profile adequacy,
foreign laws, general Catch/hygiene, negative visibility or whole-compiler
soundness/principality. At most four concurrent lightweight static-read commands;
20-minute wall cap; elapsed wall time and CPU/RAM uninstrumented. No child or Git
mutation. Primary owns review and executable verification.

| Dependency | SHA-256 |
| --- | --- |
| callable-view construction note | `8a3abd17cd26162c689a592e3f855580663d53bead80e8904ac964a16e1dfcb0` |
| source result/Call export note | `bfec4f6aad05711b580ceac69b242de502342c31bc09fabc701ad17c583c4961` |
| first-call profile design | `b779ba779b66515eddb7e44ba1d0772a6853e69a1aa13a6c4528dbd8ea0852a1` |
| receiving actions design | `401ac9eee69f27a863cd08ea24eea6fbbd3388ada9d5366bd5818ee966d73b6f` |
| typed core design | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| typed boundary design | `1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb` |
| playground `src/lib.rs` | `bace98ef2f11c9bb638b4f1f7536178c668ca8b0448fb0276986fbf0772f524b` |
| runtime `program.rs` | `b9798ac4c5d93e761582d712114615defa913f858d70e91f170471c8b8912748` |
| runtime `machine.rs` | `04024174d88223e252e1d093eaee96c17d9f43d4d32bea5c41631017c9da208c` |
| runtime `receiving.rs` | `8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9` |
| runtime `continuation.rs` | `194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3` |
| HIR `module/local_source.rs` | `ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5` |
| HIR `module/source_annotation.rs` | `b8462b66eac24a48b6fc5e931a3d8b7c38c19bb8b2f1a7cdc4ecd9a8a7a1117f` |
| solver `shadow_apply.rs` | `357b274d0de509931bda3015a99b1a1cf2ac86d75a45d230d62ab456c56740ba` |
| solver `candidate_call.rs` | `cbad9cf51a05343eb7a29ab77aac520891467a8aa4edc3201ea3d91f978984a1` |
| solver `candidate_source.rs` | `efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38` |
| solver `lib.rs` | `2c1fff385e5270ef7b7eb5fc4d9ed5f6edb6a4c01886887b183401212c5f398f` |
| solver `candidate_effect.rs` | `44ee33d077c61c9dea6359299ca49218afc6ca1b5b6807690838309b25c731c9` |

## Commit packet

- Exact leased/changed path: `notes/progress/2026-10-16-runtime-entry-plan-import-owner-audit.md`.
- Baseline: `516cdedd9bb52f4f1d1e28a4f69f388d3c481bee`; changed dependency hashes: none.
- Review status: `spec_auditor` review CLEAN within bounded source/authority
  scope. No independent theorem certification or production promotion.
- Checks: static constructor/consumer trace, 18 pinned dependency byte/hash
  comparisons, local link/whitespace/fence integrity; zero executable checks.
- Proposed checkpoint: `research: map runtime typed-plan supplier and import owners`.
- Shared deltas intentionally left to primary/curator: record the existing
  narrow Comp/native Catch evidence, Value(Function) export gap, and distinct
  semantic supplier/importer owners in current task/theory records. All
  source-supply, runtime import, architecture and production gates stay OPEN.

Writing stops at this frozen handoff; no shared record or question edit.
