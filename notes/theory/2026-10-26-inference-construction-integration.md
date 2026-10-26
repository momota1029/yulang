# Original inference constructions: checked integration surface

Date: 2026-10-26. Integration author: `/root`.

This checkpoint integrates the reviewed source and native construction work on
`yulang3`. **The full original inference-soundness theorem remains open.** The
integration supplies a reproducible import surface and a complete theorem census
for the selected 64 originating modules. A build or the census does not discharge
the remaining semantic premises.

The two entry points are
[InferenceConstruction.lean](lean/YulangClosure/InferenceConstruction.lean) and
[AuditInferenceConstruction.lean](lean/AuditInferenceConstruction.lean).
They are separate from another worktree's still-reserved `InferenceProofs`
integration paths. The protected root, project configuration, toolchain and
dependency manifest are unchanged.

## Original claim and actual progress

The target remains `YulangClosure.SourceProblem.InferenceSoundness`: for the original
supported source, generation and solution, construct a witness satisfying the
original source judgment with the same source scope. The native-success route
additionally requires the actual native correspondence. Defining that proposition,
assuming `LocalLaws`, or importing a conditional theorem does not supply these
instances. The governing source remains SG's complete source/checking grammar,
original Call observations and event telescopes, and the selected simultaneous
immutable-root interpretation.

The integration retains the following independently reviewed constructions and
their separate scope boundaries. The component notes and review receipts carry
the detailed quantified statements and original-source mappings.

| Construction | Supplied result | Remaining parent connection |
| --- | --- | --- |
| Original syntax and generation | Raw source constructors, generated rule/formula structure and finite judgment correspondence | Concrete complete semantic kernel and original owner registrations |
| Original interpretation | Positive four-component operator, completed meaning and declared-hole background rules | Full original primitive/interface/execution interpretation |
| Environment and finite checking | Retained source scopes, source-derived CallOwner incidence and semantic action from actual finite checking code | Original registry existence and every remaining leaf supplier |
| Goal-indexed admission | Current checking-goal domain, exact raw invocation recovery, current Function application without target-readback assumption | All original future-event domain/value correspondence |
| Actual future observation | Observation-child action at the actual admitted invocation's computed event and full retained prefix | Hereditary domain action and all original event coverage |
| Selected recursive pair | Actual mutual capture knot, opposite Name suffix, all raw prefixes, positive fields and full local background world | Actual decorated readouts, full phase/interface correspondence and final hole replacement |
| Native relation/Value/Context | Physical interning, child routing, callback/readback, work ownership, rollback, tables and carrier/value components | Complete successful native inference to original source judgment |
| Source signature/contribution | Source-owned incidence and dependent packet/provenance construction | Concrete original EventField/retained evidence suppliers |
| Record boundary and metatheory components | Constructed finite adapters, scoped fresh-ID transport, current Context closure and local principality/termination components | Full original record/effect behavior, principality and termination |

The selected pair is a useful nonidentity source construction, not a restriction
of the parent language. Optional records, independent effects/responses, pending
and divergent behavior, full Call, State and shared witness obligations remain
in the original goal.

## Newest accepted component boundaries

`OriginalCheckingAdmission` constructs the current target-domain predicate and
supplies both finite checking children at the actual current event. It retains
the actual provider/callable, complete raw input and the target's own checked
incidences. Its reviewer checked both narrow-to-broad and broad-to-narrow domain
changes, with a common admitted candidate and descriptor-dependent incidences.

`OriginalFunctionFuture` supplies the observation action for an actual admitted
raw invocation, including a later current configuration. The event's ten fields
and complete retained prefix are exposed. The current joint witness comes from
the current readout, not the earlier event. Its finite interface discriminator
shows why current domain truth alone does not imply the required future domain
inclusion. That example is not a source program or a proof that Yulang is unsound.
The retained formal subject is exactly `state.goalRow`; source registration
existence is still an original-construction obligation.

`OriginalRecursivePair` constructs both original Value-entry lambda bodies and
their captured opposite-member Name reads. Carrier requests/responses, pending
states and arbitrary finite divergent prefixes are retained without a successful
Return or desired-value filter. `canonical_world` builds full `PhiW`, including
every installed `Some`, even outside the registry count. At an actual Force
return, the whole background carrier supplies its current world and returned
value, and the local theorem constructs the result-extended `B_H.W`.

Its remaining readout/Return/scope/guard premises are substantive. The positive
observation construction covers post-start Force/suffix states; initial/receipt
raw witnesses do not themselves establish complete original `P_F` correspondence.
Name hygiene is not pairwise site freshness, and the provided-ID freshness
predicate is not a whole native allocator certificate. Neither `B_H.W` nor this
review is promoted to ordinary `Meaning.W` or completed recursive introduction.

## Fixed verification environment

The actual installed native tools were Lean 4.35.0,
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, and Lake
`5.0.0-src+eb6cafb`. The exact existing `lakefile.toml`, `lean-toolchain` and
empty-package `lake-manifest.json` were copied unchanged into an isolated
primary-owned project. No global toolchain selection or dependency update ran.

The accepted foreign cache was copied only after all 111 of its frozen inputs
matched. That cache was then owned exclusively by this integration. The current
recursive import/configuration closure contains **129 exact files**. The previous
124-file snapshot and each failed/repaired audit snapshot remain immutable.

From `notes/theory/lean`, the checked commands are:

```sh
lake --no-cache build +YulangClosure.InferenceConstruction YulangClosure
lake --no-cache env lean -j1 -M1536 AuditInferenceConstruction.lean
```

The first command includes both the explicit new construction surface and the
actual configured default library. The new surface is not silently added to the
default globs. The second command must be run after the imports are built.
The actual runs used the absolute installed native Lake path, one CPU affinity
and `LEAN_NUM_THREADS=1`. Build resources were 240 seconds, per-process
`-j1 -M1024`, and 6144 MiB aggregate RSS. The audit had 120 seconds and 2048 MiB
aggregate RSS, with a local 1536 MiB Lean cap for the large full printed census.

## Results and complete coverage

| Verification | Result |
| --- | --- |
| Build04: explicit surface plus actual default | Exit 0, 127 jobs, 19.573 seconds, peak aggregate RSS 1,019,449,344 bytes |
| Audit06: final fully qualified roots | Exit 0, 40.909 seconds, peak aggregate RSS 1,387,986,944 bytes |
| Origin inventory | 64 selected originating modules, 9,595 unique theorem constants |
| Required authored theorem roots | 1,640 distinct fully qualified roots, all present as theorems |
| Input identity | All 129 exact source/configuration files match the snapshot and worktree |
| Complete type/axiom records | One balanced full record per theorem, no elision or truncated output |
| Protected inputs | Root import and quarantined scheduling record hashes unchanged |

The census visits every theorem constant originating in each selected module,
including private and generated declarations and generated names outside the
module's principal namespace. It checks theorem kind and required roots and
rejects project axioms, `sorryAx` and every axiom outside the three accepted
standard axioms. All complete printed types and transitive axiom sets were
retained. It is not a census of every unrelated origin reachable through the
default project.

| Actual transitive axiom set | Theorem constants |
| --- | ---: |
| None | 5,199 |
| `propext` | 2,396 |
| `Quot.sound` | 8 |
| `propext`, `Quot.sound` | 1,521 |
| `propext`, `Quot.sound`, `Classical.choice` | 471 |

The default build reports **668 pre-existing warning first-lines** in nine
unchanged files. Their full first-line multiset is identical to both the prior
accepted integration and the preceding primary build. No new warning appears.
This is not a claim that the project is warning-free.

### Generated theorem origin reconciliation

Isolated module counts cannot simply be added when a generated equation theorem
was already imported from an earlier origin. The combined census retains every
name and normalizes each transitive axiom set before comparison:

- `NativeContextReadback.BodyPacket.mk.congr_simp` is already in ContextCompletion;
  ContextTables has 520 unique originating theorems in this surface.
- `NativeValuePorts.intern.eq_1` is already in ContextTables; Interner contributes
  243 unique theorems, while all 244 isolated theorem names remain audited.
- `OriginalSource.Binder.isEvent.eq_1` is already in SourceEnvironment;
  EffectHygiene contributes 23 unique theorems, with all 24 isolated names present.
- RecordBoundary's 307 isolated names include 46 `sourceRules.eq_*` helpers in
  SourceInterpretation and five binding/expression helpers in PrincipalTransport.
  All 307 remain present; its additional contribution is 256.
- Pair's 240 isolated names include three `statementRulesK.eq_*` helpers already
  in PrincipalTransport. All 240 remain present; its additional contribution
  is 237.

Admission's 65, Future's 24 and Progress's 50 theorem names are all present.
Some leaf audits print every implicit application explicitly; the combined
audit uses complete nonelided theorem types with its documented print options.
Where print settings differ, the reconciliation claims exact names and axiom
sets, not byte-identical type formatting.

## Failures and repairs retained

Build01 stopped before Lean because the ordinary sandbox could not locate the
native Lake installation. A permitted execution escalation of the same native
toolchain succeeded; no source, toolchain or configuration workaround was used.
The failed log and read-only startup diagnostics remain available. A blocked
ptrace diagnostic was not repeated or treated as mathematical evidence.

Audit03 itself passed, but its first postprocessor rejected an isolated-count
sum of 8,965 because the actual combined count was 8,963. Exact generated-name
and complete type/axiom comparisons explained the two duplicates. Both original
expectation and corrected reconciliation were retained; this was not a Lean
proof repair.

Audit05 correctly failed because the Pair manifest supplied 69 relative root
names and the integration initially used those without their namespace. Audit06
uses their actual fully qualified names. No proof term, origin count or import
changed in that repair. The failed snapshot and log remain immutable.

The first historical warning-summary JSON used an over-escaped path pattern and
recorded empty counters. The corrected receipt explicitly replaces those empty
counters and verifies the exact 668-warning multiset against both old logs and
all nine unchanged source hashes. The deficient receipt remains preserved.

## Concrete next original obligations

The first current construction concerns actual immutable parameter binding.
The full post-bind world must be computed from actual cells/views, saved lexical
environments and original scoped evidence. The convenient conditional equality
`registry_after = registry_before.rebind ...` preserves the entire witness map;
it is not yet a law of actual later events. A direct `canonical_world` application
can instead preserve the older Shared overlap and use the actual new fields.

SG §3.3 explicitly assigns retained initializer/rebind evidence to Shared and
current receipt/response/rebind/body fields to their original Event/EventField
owners. The present formal `Outcome` has raw results and endpoint/binding
updates, but no retained Shared evidence output. The current Lambda rule's lack
of a separate `sharedE` at formal rebind is therefore a representation gap, not
authority to omit that evidence. The new construction must register it at the
actual source-owned event and original dependency telescope.

Beyond that constructor, the full theorem still requires original independently
admitted Initial, Response, raw Resume and FutureUse coverage; coherent domain
and value reading at those events; actual primitive/profile/interface/guard
suppliers; complete recursive phase correspondence and hole replacement; all
original source cases; and successful native inference correspondence with the
same joint scoped witness. No unsupported source form or difficult event is
removed to complete this integration.

## Evidence locations

The producer receipt is
[`20261026-inference-construction-integration-r4.md`](../../tasks/agent-loop/inbox/20261026-inference-construction-integration-r4.md).
Fresh independent integration review is a separate artifact. Component authors
and their existing independent review receipts retain mathematical ownership.
This aggregate audit does not replace those reviews or recertify a foreign
author's result by an import count.

Complete logs, all immutable input snapshots, full type/axiom records and exact
reconciliations are retained under
`/workspace/scratch/f98087c7ac1a/final-validation-r4/`.
The producer receipt records their hashes and the final freeze.
