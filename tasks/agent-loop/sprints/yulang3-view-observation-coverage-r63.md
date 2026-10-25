# Sprint YULANG3-VIEW-OBSERVATION-COVERAGE-20261026/r63

Contract revision: r2.

Status: PRIMARY-AUTHORIZED COUNTEREXAMPLE/coverage candidate. Branch `yulang3`; exact baseline `93d08d5867015741b3588ea3df4c56903b2bbe83`; no source or semantic change authority.

## Original claim and target

Parent: the paper's execution-safety/canonical-forms argument, `docs/yulang-operational-type-safety-ja.tex:998–1005`, read together with value syntax/typing :137–164 and :215–228, machine/value observation :256–270 and :299–327, plus the R62 conditional bridge. The paper explicitly allows a value-shape witness to be either the corresponding constructor **or explicit view evidence**. R62's `PaperHeapObservation.ObservationTrace`, however, reaches only a literal `.delay body` using graph-read, direct type-beta and type-application-function-position steps.

R63 asks whether a closed represented view value can have a typing derivation while the R62 finite observation relation has no path to the literal delay it wraps. This is a falsifier for the *coverage premise*, not a refutation of R62's conditional theorem, not a change to paper semantics, and not a source-qualified claim that the compiler emits this exact closed term.

Fixed candidate terms, using existing constructors:

```lean
.view metadata (.delay (.ret (.literal .unit)))
.force (.view metadata (.delay (.ret (.literal .unit))))
```

Target public theorem surface in `YulangClosure.PaperTypes.PaperObservationCoverage`:

1. `view_operand_force_typed`: for arbitrary `(d : DeclarationTable)` and `metadata : ViewMetadata`, show `PaperComputationTyped d [] []` of the closed force above at `.base .unit`. This uses an arbitrary declaration table because the judgment is indexed by `DeclarationTable`, not by a list; the witness remains closed with empty graph and type environments.
2. `no_observation_step_from_view`: no `ObservationStep heap (.view metadata value) target` exists, for arbitrary heap and metadata.
3. `view_operand_no_literal_delay_trace`: no `ObservationTrace heap (.view metadata (.delay body)) (.delay body)` exists.
4. `connected_executor_view_force_stuck`: the existing `PaperExtendedExecution.controlStep` returns `none` on the represented force of a view-wrapped delay with empty stack, for arbitrary declaration table, binder, metadata and body.

All implicit quantifiers, exact printed types and axiom reports must be retained. If theorem 4 is false under a real existing branch, record the first counterexample rather than tailoring a new premise or changing a relation. No new transition, `expose` rule, metadata-erasure assumption or source restriction is authorized.

## Source and dependency pins

The following are frozen at the exact baseline above; verify every hash before work and at freeze. The 21 Lean sources are the exact current recursive R62 candidate/dependency cone; `PaperObservationCoverage.lean` will add one source only in the isolated workspace. The independently checked R62 review confirms the existing imported-view gap and cleanly separates it from the conditional R62 result.

```text
a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b  docs/yulang-operational-type-safety-ja.tex
b8380f4276279d2853ae1e70b7304b89f45fa3c1c7b737eaf8cf89df3483e23e  notes/theory/lean/YulangClosure.lean
f1463d4dceeab7251b2a65508b23a7ef4ab3a575b2792793be04a858e9191258  notes/theory/lean/YulangClosure/DeclSubst.lean
58661ddec13e1fe4abb6a9b6627597fa824dedbf36f952e56dc15906141314d1  notes/theory/lean/YulangClosure/PaperCombinedExecution.lean
71594dfb24af402f7b4835dc54b5383a46106faba959b687295cc0431361530e  notes/theory/lean/YulangClosure/PaperCoreControl.lean
6357b14217e82421eed87da981cef8e94014dcaea634d746ad0b4bb39bff6144  notes/theory/lean/YulangClosure/PaperCoreStep.lean
568a9a5a1991bb605d85e9b58f33638fb445b1325516e10eed0f076f72346d7a  notes/theory/lean/YulangClosure/PaperExecutionBinderLaws.lean
313a550a550716e235e73690d238f1040838aeebd2cc0cf0b7753979ab6fe38d  notes/theory/lean/YulangClosure/PaperExecutionGraphWeakening.lean
78f23b9e946b0259cdb63797ed226706112f71375a013e0b9cc8745ad5afe8b0  notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean
fae64aa9a5c37572a3f654c403b7fb8ff7eb7adccaa4e3540fff85e61ce84819  notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean
a29c5cc15748e8a91338f2a068e94ff7dc58c2a19adad564ba3f5a6fea337ea7  notes/theory/lean/YulangClosure/PaperExtendedExecution.lean
7cd87b8e5fd43eea0206401de6ed91e817755f3d1ad2c5aeee1caf0dd1732925  notes/theory/lean/YulangClosure/PaperFreshHeapAllocation.lean
46a9e8e76f5745cbaffc40b7bb95ff37064941a84532fa5edc07672ddad3d59f  notes/theory/lean/YulangClosure/PaperHeapExecution.lean
19b54b87b63cdc4175b1b641ca83d0c1e9454e2439c58a0936bf31fa5bc4725f  notes/theory/lean/YulangClosure/PaperHeapObservation.lean
2f0026049554cb870158115b4bab8d42f7cbee8b030ee3f84a904763c328cac0  notes/theory/lean/YulangClosure/PaperPerformLetExecution.lean
5ab59033b0cea347144c50a5323e4dd6cb59cc6bfbdc0bffd063a4808e741935  notes/theory/lean/YulangClosure/PaperResumeExecution.lean
3ead9cf7d0f57d02d5fd8b44da24f133d7859e76dff8ee1d1b17cb233920d792  notes/theory/lean/YulangClosure/PaperTemplateExecution.lean
42d7f46d992e715443a7116066b51ae1748849718f6c4e716d9169ea069059d9  notes/theory/lean/YulangClosure/PaperTermSubstitution.lean
7bc13a41a0333d885b91291a7fbb1ef18302a94c79a34f21469dbae19d76f84d  notes/theory/lean/YulangClosure/PaperTupleSplitExecution.lean
60e095545530bc784487a4bfcc1c7acfc1160b3adf8c1c8dc03ab98806154556  notes/theory/lean/YulangClosure/PaperTypeApplicationPreservation.lean
29c1a85b4d2588224bf1847f78a7b4d94db095488f3bba4937888a3815f39d13  notes/theory/lean/YulangClosure/PaperTypeFormation.lean
02834720f622642dd4c7a27ea51451deb7386877b091fbccc828a66eaa8e4861  notes/theory/lean/YulangClosure/PaperTypeSubstitution.lean
0a1834040a0201c0c472f66138f6501094f7138dd3614f2bc4439a8be0cda1c8  notes/theory/lean/YulangClosure/PaperTypeBetaExecution.lean
ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c  notes/theory/lean/lean-toolchain
2514197994dc47b5e4c6f15ff8c9251f994056b6e32bf2648588ffc10251e194  notes/theory/lean/lakefile.toml
058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3  notes/theory/lean/lake-manifest.json
0a31542efa94f2a6aff13bcbb1ef34b69c442d5027bcca3c0d8c40f8e061ac7a  notes/theory/lean/README.md
9de3e01ef995fef5bc00448e7c90cfdcc0bbd5461894af8bc94f546996832f0b  tasks/agent-loop/sprints/yulang3-heap-execution-bridge-r62.md
5fe3cc2b1696f9ce921c7d4dbcef13fb81078ee7ba3f2cf0e72d752c181f41de  tasks/agent-loop/sprints/yulang3-heap-execution-bridge-r62-outcome.md
7a92d31861f88330b3c35abe2ece225df4f163e04a9185ad209f0754d97abed5  tasks/agent-loop/inbox/paper-heap-execution-r62-review.md
```

## Lanes, exact leases and checks

One registered `lean_prover`, no descendants, owns only these paths in isolated `/tmp/yulang-r63-observation-coverage/proof`:

- `notes/theory/lean/YulangClosure/PaperObservationCoverage.lean`
- `notes/theory/lean/.lake/R63Audit.lean`
- `run_call.py`, `process-manifest.json`, `proof-checks.txt`
- `lake-build` and `call-01.stdout/.stderr` through `call-04.stdout/.stderr`
- one handoff: `tasks/agent-loop/inbox/paper-observation-coverage-r63.md`

Primary owns detached `/tmp/yulang-r63-observation-coverage/primary`, its four-call runner/manifest/cache/captures, and `tasks/agent-loop/inbox/paper-observation-coverage-r63-primary.md`. A fresh non-author `compiler_referee` after primary freeze owns only the returned read-only review receipt at `tasks/agent-loop/inbox/paper-observation-coverage-r63-review.md`.

Sprint envelope: 1800 active seconds total; proof worker 600s / 4 literal calls / 150 checker seconds; primary 1020s / 4 calls / 150 checker seconds; reviewer 180s / 0 checker calls. Four calls per verification owner are exactly resolved Lake `--version`, `lake env lean --version`, one focused build, one complete audit. At most 120 seconds per checker process, `-j1 -M1024`, one heavy build per owner. No retry after the first failed build/audit, cap uncertainty or pin discrepancy. Preserve all call output, including failure. No tests, Cargo, runtime probes, network, `lake update`, full default build, source edits or semantic changes.

Worker verifies the exact baseline and every pin, then constructs the four fixed declarations and complete exact-name/kind/type/axiom audit. Audit every declaration in the candidate module; static scan its complete internal import cone for holes and checker bypasses. Primary independently checks worker cessation, all pins and artifact hashes, runs the exact four primary calls, applies the bundled `validate_audit` to the complete output with independently enumerated names, and checks that the closed typed witness has the stated judgment while the trace and executor results are genuinely absent. Fresh review must assess counterexample validity, theorem quantifiers, source/manuscript scope, exact audit, and whether this refutes only the R62 coverage premise. CLEAN review plus primary adjudication is required before integration or changing any coverage gate.

## Falsifiers and preserved boundaries

Falsifiers: a real `ObservationStep` from `.view`; a constructor/view path to literal delay under the frozen relation; typing fails because of a genuine rule restriction; or the current connected executor has a successful view-force branch. Any such evidence stops the proposed counterexample and preserves source bytes.

Do not add a view transition, erase metadata, change value typing, narrow the original source domain, weaken R62's conditional theorem, or declare a production defect from a represented auxiliary relation. R62 remains a valid conditional theorem if its finite-observation premise is supplied. `R62-FINITE-CONSTRUCTOR-OBSERVATION-1` and R23/source-native/full-language/inference/production gates remain OPEN until evidence at their actual owners resolves them. Preserve eight quarantined identities, external artifacts and both user-withdrawn questions. No safe Rust slice is part of R63.
