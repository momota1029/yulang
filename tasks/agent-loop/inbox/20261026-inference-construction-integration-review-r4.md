# Inference construction integration: independent review r4

Verdict: **ACCEPT for the exact frozen integration scope below.**
No blocking or major findings remain. This accepts the import surface, selected
origin audit, input/evidence identity, reconciliation and stated mathematical
boundaries. It does not establish whole original inference soundness or replace
the component authors' independent mathematical reviews.

Reviewer: `/root/function_future_review_r4`, fresh nonauthor generic proof-role
fallback. The reviewer authored none of the four integration deliverables.
Earlier review of `OriginalFunctionFuture` was review, not authorship. Applicable
`AGENTS.md`, base/proof rules, `yulang-lean-proofs/SKILL.md`, source/execution
references and `.codex/agents/lean-prover.toml` were read. No descendants or model
override were requested; effective model/effort settings are UNKNOWN. `/root`
alone retains adjudication, shared-status changes, Git integration and publication.

The 1200-second review began at 2026-10-26 15:12:40 UTC. The allowance was at most
two focused 120-second checker bundles if a concrete evidence gap required one.
**Zero reviewer Lean/checker invocations were needed.** Complete producer kernel
evidence and independently parsed exact inputs resolved the integration risks.
Only this repository receipt and
`/workspace/scratch/f98087c7ac1a/inference-construction-review-r4/` were written.
No source/core/configuration/import/author metadata/Git/shared-status or shared
cache was changed. No unrelated native test ran.

## Exact reviewed files and final freeze

The producer-supplied published component baseline is
`5428c5e62e31b20f261c76128cf426fdd137cca5`. This review verifies file identity and
does not independently claim a remote-publication operation.

| Reviewed deliverable | SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/InferenceConstruction.lean` | `5a628c85b4afd2648114b0bff1bd585f4fdba8a50519bd73001d416f83b8fa42` |
| `notes/theory/lean/AuditInferenceConstruction.lean` | `b1542b84c2e0e38f6e4a2b9c11d8a14d945e812697d144fe77ad07ed278a241d` |
| `notes/theory/2026-10-26-inference-construction-integration.md` | `5065820adfe67282a910d29d512a22b2a200699416e4fc6619277470dbb9e22c` |
| `tasks/agent-loop/inbox/20261026-inference-construction-integration-r4.md` | `29e777bc764abc231dca49315efe9e31e90ff609c823a9a89823161f40a33fad` |

The initial producer freeze at 15:11:56.181470 UTC is retained as
`final-validation-r4/integration-freeze.json`, SHA-256
`a16a06ef5041e6ca9db7c1d3f6dad5903147cc6819b34574575aa1cc226b494f`.
The final documentation supplement at 15:16:06.735747 UTC is
`final-validation-r4/integration-freeze-namespace-correction.json`, SHA-256
`1623ee7db8b3745d83e38f3babec9cd7b8d3dd934a34562ebb020cdfb579875d`.
All initial 431 and final 432 artifact hashes were independently verified.

The sole supplement change replaces the incorrect documentation identifier
`Contracts.SourceProblem.InferenceSoundness` with the actual fully qualified
`YulangClosure.SourceProblem.InferenceSoundness`. The original note with SHA-256
`d67fcd4dd3691fb67ae142af6e741641879e8328398a433f59c852356536bd6d`
remains preserved as `integration-note-before-namespace-correction.md`.
Exact text comparison confirms that single replacement; the other three
deliverables and all 129 checked inputs remain unchanged. No Lean rerun was
necessary for the documentation correction.

## Input closure, audit implementation and complete records

The actual small import module, complete audit implementation/root array,
integration note, producer receipt, bounded runner, postprocessor, all six
checker receipts and material failure logs were inspected. The independent
recursive import closure includes the configured default globs as well as the
explicit new target and standalone audit: 126 Lean inputs plus the unchanged
`lakefile.toml`, `lean-toolchain` and `lake-manifest.json`, exactly 129 files.
Every hash matches the current repository, producer project and final immutable
snapshot. The input-manifest SHA-256 is
`76907c0ab43ae59e888fa3304e633abc35cf9f7edc7664ce8ec2e9aff2ad8ece`.
The new target is explicit; the configured default globs have not changed.
The disjoint ongoing WorldReadout packet is excluded.
The historical cache provenance was also checked against its actual
`integration-r5/final-source-inputs.json`: all 111 recorded source/configuration
hashes match the historical project. Three historical inputs differ from the
later snapshot01/current inputs: `InferenceProofs.lean`,
`OriginalSourceGeneration.lean` and `lakefile.toml`. Build02 explicitly rebuilt
both changed Lean modules. The other 108 historical inputs match the current
ones; this distinction does not equate cache provenance with current input
identity. All current 129 inputs are checked separately as described above.

`InferenceConstruction.lean` adds imports and explanatory text, with no theorem,
axiom, alternate soundness predicate or proof bypass. The standalone audit
looks up each of 64 selected module indices and enumerates `env.constants` by
actual originating module index. It does not select by namespace prefix.
It collects every `ConstantInfo.thmInfo`, rejects originating project axioms,
rejects duplicate names and empty selected origins, and requires all 1640
distinct roots to belong to the theorem census. Required roots are not accepted
merely because an arbitrary same-spelled declaration exists.

Every selected theorem receives full `#check @...` and `#print axioms` output.
`collectAxioms` rejects dependencies outside `propext`, `Quot.sound` and
`Classical.choice`; no `sorryAx` or reduction bypass is admitted. The full-print
settings, complete output drain, balanced record markers and absence of elision
were inspected. This is an audit of the selected 64 origins, not every origin
reachable in the 126-module input closure.

The reviewer's separate line-state parser independently reconstructed all 9595
complete type/axiom records from the raw final log. It checked every matched
begin/end name, unique theorem name, required root, module ordering/count,
named axiom report, absence of stray diagnostic output and exact retained
record contents. All 1052 private theorem names remain included. Generated
helpers outside their owning module's usual namespace remain included.

| Exact census | Result |
| --- | ---: |
| Selected originating modules | 64 |
| Unique theorem constants | 9595 |
| Distinct required fully qualified roots | 1640 |
| No axiom dependency | 5199 |
| `propext` only | 2396 |
| `Quot.sound` only | 8 |
| `propext` and `Quot.sound` | 1521 |
| All three accepted standard axioms | 471 |

The final raw audit SHA-256 is
`b099631169834f6dc00a380918ff794bc90f81f78c5058675474c97cbbc99e2b`.
The full retained records SHA-256 is
`1024a8aa9eb19d17ca77541e0d27eb894a86482128eaad5732b155217f24ccba`.
The independent parse reproduces every global record, rather than merely
agreeing with the producer's final counts. This remains independent inspection
of existing kernel output, not a claimed new reviewer kernel run.

The protected root `notes/theory/lean/YulangClosure.lean` remains
`3c38da4bb2e017249fa973e0ee28f243d44ba6d52b6f173ac617b605f1fce9e8`;
the quarantined scheduling record remains
`fcf344c8eee94b8b6c2e6188275ac90d1e2a0f22b1274317f43024df8dce125d`.
The latter was not treated as current task authority or updated.

## Generated-origin and warning reconciliation

The reviewer independently compared all 1475 isolated theorem names and
normalized transitive axiom sets in the following eight component inventories
with the complete global census. Full raw reports remain available; different
pretty-print settings are not represented as byte-identical type formatting.
For isolated inventories that list every declaration, the actual origin audit's
`thmInfo` count and the intersection with the global theorem-name inventory agree.

| Isolated component | Isolated theorems | Global own origin | Reconciliation |
| --- | ---: | ---: | --- |
| NativeContextTables | 521 | 520 | `NativeContextReadback.BodyPacket.mk.congr_simp` belongs to NativeContextCompletion |
| NativeRelationInterner | 244 | 243 | `NativeValuePorts.intern.eq_1` belongs to NativeContextTables |
| OriginalEffectHygiene | 24 | 23 | `OriginalSource.Binder.isEvent.eq_1` belongs to OriginalSourceEnvironment |
| OriginalSourceRecordBoundary | 307 | 256 | 46 `sourceRules.eq_*` helpers belong to OriginalSourceInterpretation; five binding/expression helpers belong to SourcePrincipalTransport |
| OriginalRecursivePair | 240 | 237 | Three `statementRulesK.eq_*` helpers belong to SourcePrincipalTransport |
| OriginalCheckingAdmission | 65 | 65 | Every name and axiom set retained |
| OriginalFunctionFuture | 24 | 24 | Every name and axiom set retained |
| NativeInferenceProgress | 50 | 50 | Every name and axiom set retained |

All named helpers remain audited. None was dropped to force the expected sum.
The exact name-to-origin maps and all compared input hashes are retained in
`independent-origin-warning-verification.json`.

The reviewer separately parsed actual warning first-lines in Build02, Build04
and the preceding accepted `integration-r5/check06-final-default.log`. Each has
668; the complete multisets are identical. All nine warning source files match
their historical checked snapshot bytes. Per-file counts are 23,235,96,4,22,2,
276,3,7 for PaperExecutionSyntax, PaperExecutionBinderLaws,
PaperTermSubstitution, PaperCoreStep, PaperTupleSplitExecution,
PaperPerformLetExecution, PaperTypeBetaExecution, ControlComposition and
NativeIntegerComparison respectively. No warning-free claim is made. The old
over-escaped-regex summary with empty counters remains retained and explicitly
superseded by `warnings-reconciliation-through-17.json`.

## Execution evidence and retained unsuccessful attempts

The producer used installed native Lean 4.35.0,
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, and Lake
`5.0.0-src+eb6cafb`, through its absolute installed path. No configuration,
dependency, source or toolchain workaround was introduced. The owned runner
checks input hashes before execution, fixes one CPU/thread, uses its exclusive
cache and temporary directory, monitors process-group RSS and drains output.
Build bounds were 240 seconds and 6144 MiB aggregate with normal `-j1 -M1024`;
the full audit used 120 seconds, 2048 MiB aggregate and a local `-M1536` cap.
All six receipts and their input/log hashes are preserved in the final manifest.

| Attempt | Inspected outcome |
| --- | --- |
| Build01 | Exit 1 before Lean: normal sandbox native-Lake installation detection failed |
| Build02 | Exit 0; 48.300 seconds; peak group RSS 1053712384 bytes |
| Audit03 | Kernel exit 0; 41.429 seconds; peak 1369378816 bytes; initial isolated-count postprocessor rejected 8965 versus actual deduplicated 8963 |
| Build04 | Exit 0; 127 jobs; 19.572692 seconds; peak 1019449344 bytes |
| Audit05 | Exit 1; 24.806 seconds; missing required short Pair root `other_other`; all 69 Pair roots lacked the namespace |
| Audit06 | Exit 0; 40.909217 seconds; peak 1387986944 bytes; all 1640 roots satisfied |

Build04 log SHA-256 is
`7cbb3a1c9c4530974fff12a07c2b876112131b10b48812f7a817879a2289fc3c`.
It ran the actual default target together with the explicit new target.
The Build04 and final input snapshots differ only in the standalone audit
source. Independent text comparison verifies that Audit05-to-Audit06 changed
exactly the 69 Pair root identifiers by adding
`YulangClosure.OriginalRecursivePair.`; every other audit byte is unchanged.
No proof term was edited in either the root-qualification or deduplication repair.

The ordinary sandbox failure was followed by permitted escalation of the same
bounded runner and native tools. It was not converted into a mathematical pass.
The blocked read-only ptrace diagnostic remains a diagnostic failure, not proof
evidence. Previous input snapshots, unsuccessful logs, naive expected counts
and the deficient warning summary remain immutable and visible.

Review-local parser mistakes are also retained: the first closure parser
omitted configured default globs and reported five extra inputs; the second
used an incorrect historical snapshot directory spelling. Reading the actual
configuration and observed directory name corrected those parser assumptions.
Their outputs are `01-parser-failure.log` and `02-parser-path-failure.log`.
A later read-only schema print attempted to slice the freeze's integer input
count as a collection; `03-schema-inspection-failure.log` preserves that error.
The actual input hashes are in the already verified manifest mapping. None of
these diagnostic failures was a Lean attempt or a source repair. The first
final-verification script also made an overstrong assumption that all 111
historical cache hashes equaled the later current snapshot; its script and
failure are preserved as `04-freeze-cache-assumption.py` and
`04-freeze-cache-assumption-failure.log`. The exact three-file historical
difference and actual rebuild evidence above resolve that reviewer assumption.

## Actual parent type and source obligations

The actual `Contracts.lean` definition was read. Under namespace
`YulangClosure`, `SourceProblem.InferenceSoundness` quantifies original supported
source, generation and solved declarations, and requires an elaborated witness
satisfying the source judgment and `sameScoped` for the same solution. Actual
`NativeCorrespondence` takes native success to generation, a native-realizing
solution and solver success. `CoreComposition.native_success_elaborates` remains
conditional on native correspondence, inference soundness and elaboration;
imports do not construct those assumptions. `LocalLaws` retains substantive
typing, preservation, resume, simulation, observation, no-bad-state and progress
fields. No whole SourceProblem or LocalLaws instance is supplied by this packet.

The governing SG §3.3 event telescopes, Call-input realization §§2–4 and the
selected contextual Function-membership design were read, and the newest
component review receipts and actual relevant source definitions were checked.
The integration note respects the following boundaries:

- Future observation uses the actual admitted raw invocation and computed event,
  preserving all ten event coordinates, complete retained prefix and current
  read-out joint witness. Its retained formal subject is `state.goalRow`, not
  a proof that all original source CallOwner registrations exist. Its finite
  event-sensitive example discriminates formal interfaces; it is not an
  original source counterexample or an unsoundness proof. All future-event
  domain/value reading and independently admitted Initial, Response, raw Resume
  and FutureUse coverage remain open.
- Pair `worldInputs` constructs the missing world interpretation from registry
  data. It does not prove equality to a previously fixed arbitrary `Inputs`.
  `canonical_world` covers every installed `Some`, including indices outside
  the count. Positive observations cover post-start Force/suffix states; raw
  initial/receipt witnesses do not establish every original initial `P_F`.
  The holes are exactly the selected value/descriptor/root rows. The actual
  Force-return theorem still needs the full background carrier, exact current
  readout, immediate guards, return/trace and future-hole hypotheses.
- Pair background `B_H.W` is not ordinary completed `Meaning.W`. The conditional
  rebind equation preserves the entire witness map, but does not establish a
  law of actual future events. A future constructor may preserve old Shared
  overlap and supply actual new fields without freezing the entire witness.
  Full phase correspondence, selected recursive Knu closure, replacement and
  general L4 are not established by this integration.
- SG explicitly installs retained initializer/rebind Shared evidence. Actual
  formal `Outcome` currently records raw result/after-state/endpoints/bindings
  without a retained Shared output; actual Lambda generation lacks a dedicated
  rebind `sharedE`. Those are representation/owner obligations, not permission
  to erase the original semantic evidence. Original Event/EventField owners,
  dependency telescopes, view/incidence, guards/captures and every remaining
  source/native supplier stay required.

Consequently whole `KernelSound`, all `sourceCases`, full original record/effect
behavior, complete principality/termination, full supported grammar and native
success correspondence with the same joint scoped witness remain OPEN. The
integration does not narrow the parent grammar to the selected pair, optional
records, successful returns or any smaller implementation subset. This review
does not recertify unrelated foreign mathematics from an import count.

## Review evidence and stopped handoff

Private review evidence includes `source-closure-verification.json`,
`supplement-verification.json`, `inspect_census.py`,
`independent-census-verification.json`, `reconcile_origins_warnings.py` and
`independent-origin-warning-verification.json`, plus all retained parser
failures. The final review `artifact-manifest.json` records this receipt's hash,
every private artifact, all 129 checked inputs, all producer artifact hashes,
external comparison inputs and all six attempt receipts. `stopped.json` is
written after the manifest to avoid a self-referential hash.

At handoff this reviewer has no running checker, descendant or background writer.
All review writes stop after the final manifest/stop receipt. The producer's
integration freeze reports its source/checker writers stopped; the final process
inspection checks this isolated integration/review surface. The separately
active WorldReadout writer is expressly excluded and retains its own leases.
Only `/root` may publish these exact reviewed integration files and this receipt.
