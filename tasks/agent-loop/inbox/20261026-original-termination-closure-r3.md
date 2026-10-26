# Original termination closure r3: frozen rewrite-owner component

Revision 1, 2026-10-26. Worker `/root/original_termination_closure_r3`.
Frozen source base: `99f18bdc54df8057f5a6d5d4bec5dc449336c234`.

**Review class:** checked source-native cache projection, with an explicit
finite-prefix history invariant. **Original whole-source inference termination
remains OPEN.** No original `Acc` theorem and no genuine source-reachable
repeatable divergence have been established. This is an early independently
reviewable component requested by the primary, not a closure claim.

## Ownership and authority

Generic `lean_prover` role; inherited model, no worker-side model override.
The worker read the assigned agent configuration, Lean proof skill and its
source/execution references, root/legacy AGENTS guidance, goal-driven sprint
and design-authority rules, and the two original inference/SCC authority notes.
The stale scheduling file was read as instructed and did not replace the
primary's exact assignment.

Exact repository write lease:

- `notes/theory/lean/YulangClosure/OriginalTerminationClosure.lean`
- `notes/theory/2026-10-26-original-termination-closure.md`
- `tasks/agent-loop/inbox/20261026-original-termination-closure-r3.md`

Scratch and isolated checker project:
`/workspace/scratch/e3678bef96db/termination-closure-r3`.
No child agents, Git writes, compiler edits, project/root-import changes,
shared status edits or shared `.lake` writes. Primary remains sole Git writer.
No full root integration build was run by this leaf.

## Concrete result and source correspondence

`recordAdmission_retained` models the exact rewrite coordinate preserved by
`record_typed_pair_admission` at `crates/yu-solver/src/lib.rs:15342–15369`.
`recordRewrite_exact` models the missing/conflicting/same/new cases of
`retain_candidate_value_rewrite` at `15275–15293`. Existing memo diagnostics
may be replaced; an installed retained extrusion target is not cleared.

The module imports the existing `NativeValueStructure.dispatch`, with its
actual duplicate/canonical/retained/body precedence. A candidate-mode request
with a retained raw-pair target cannot enter any body, even if generation,
Context, current-pair completion, canonical map or source demand differs.
The Context-prefix exclusion uses the actual imported `afterContext` result;
it does not move discharge before its callback.

A successful new changed-extrusion publication has an injective charge to
its original raw endpoint pair within the modeled uncancelled history:
`changed_extrusion_parents_nodup`. The retained target also persists, and the
final theorem feeds that invariant back into later native dispatch.

The exact changed-event premises are candidate mode; equality of the observed
retained map with the state projection; the imported dispatch equation
selecting fallback; a changed target; and successful exact retained-write.
The diagnostic admission may occur between dispatch and retained publication,
because its preserved coordinate is proved equal. `ValueMemo D` projects only
rewrite and updated direct-witness/completion payload; native retained child
fields are not asserted to be replaced.

**Limits:** this is a history of successful changed-extrusion publications,
not all physical allocation attempts. Rollback and externally repeated
cancel/retry are outside `RewriteStep`; source-to-history extraction across
native checkpoints remains unproved. `unchanged` is a projection event and
is never used as a global inference transition or accessibility argument.
No finite final row set, future raw-pair supply, terminal drain transcript,
resource cap or source restriction is assumed.

The companion note preserves the second source finding: ordinary Context
callbacks apply an effect or replay with `provenance = None` and enqueue finite
children. Actual nested typed-drain stepping is in retained restoration with
`Some((occurrence, cause))`. Both native paths still need global composition.

## Exact checked authored declarations

The eleven authored roots are listed in companion note §3. Their complete
statements are in the frozen Lean module; `AuditOriginalTerminationClosure.lean`
prints every originating theorem type and transitive axiom list and requires
all eleven roots. Full checker output stays in the scratch evidence, per
`rules/git-concurrency.md` (no committed raw logs).

The central history statements quantify over every `RewriteRun` from the
empty memo, without a finite row/pair universe. A changed step retains the
actual dispatch equation, candidate-mode test, retained-map agreement,
changed-target inequality and successful exact `recordRewrite` equation.
The end result is `Nodup` of the raw source pairs, persistence of all stored
targets, and exclusion of later bodies at those same raw pairs. No `Acc`
claim, rollback rule or whole `inferStep` is hidden in this presentation.

## Complete module-origin census

The origin audit enumerated all **81** constants belonging to this module: 9 constructors, 37 definitions, 5 inductives, 5 recursors, 25 theorems. The 25 theorem constants include all eleven authored roots and fourteen generated theorems.

Every module-origin declaration was printed with its exact type and full transitive axiom list in `check-05-census.log`. The audit rejects axiom declarations and dependencies outside the ordinary Lean axiom whitelist. No custom axiom, `sorryAx`, `Classical.choice`, `native_decide` or kernel-bypass dependency occurs. Among all 81 declarations, 51 use no axioms, 22 use only `propext`, and eight use `propext` plus `Quot.sound`. Among 25 theorems, the respective counts are ten, seven and eight.

| Module-origin declaration (namespace prefix omitted) | Kind | Complete axioms |
|---|---|---|
| `MemoStore` | definition | none |
| `RewriteRun` | inductive | `propext` |
| `RewriteRun.below` | inductive | `propext` |
| `RewriteRun.below.casesOn` | definition | `propext` |
| `RewriteRun.below.nil` | constructor | `propext` |
| `RewriteRun.below.rec` | recursor | `propext` |
| `RewriteRun.below.snoc` | constructor | `propext` |
| `RewriteRun.brecOn` | theorem | `propext` |
| `RewriteRun.casesOn` | definition | `propext` |
| `RewriteRun.nil` | constructor | none |
| `RewriteRun.rec` | recursor | `propext` |
| `RewriteRun.recOn` | definition | `propext` |
| `RewriteRun.snoc` | constructor | `propext` |
| `RewriteState` | inductive | none |
| `RewriteState.Valid` | definition | none |
| `RewriteState.Valid.eq_1` | theorem | none |
| `RewriteState._sizeOf_1` | definition | none |
| `RewriteState._sizeOf_inst` | definition | none |
| `RewriteState.births` | definition | none |
| `RewriteState.births._default` | definition | none |
| `RewriteState.casesOn` | definition | none |
| `RewriteState.ctorIdx` | definition | none |
| `RewriteState.initial` | definition | none |
| `RewriteState.initial.eq_1` | theorem | none |
| `RewriteState.mk` | constructor | none |
| `RewriteState.mk._flat_ctor` | definition | none |
| `RewriteState.mk.inj` | theorem | none |
| `RewriteState.mk.injEq` | theorem | `propext` |
| `RewriteState.mk.noConfusion` | definition | none |
| `RewriteState.mk.sizeOf_spec` | theorem | none |
| `RewriteState.noConfusion` | definition | none |
| `RewriteState.noConfusionType` | definition | none |
| `RewriteState.rec` | recursor | none |
| `RewriteState.recOn` | definition | none |
| `RewriteState.store` | definition | none |
| `RewriteStep` | inductive | `propext` |
| `RewriteStep.admission` | constructor | none |
| `RewriteStep.casesOn` | definition | `propext` |
| `RewriteStep.changed` | constructor | `propext` |
| `RewriteStep.rec` | recursor | `propext` |
| `RewriteStep.recOn` | definition | `propext` |
| `RewriteStep.unchanged` | constructor | none |
| `ValueMemo` | inductive | none |
| `ValueMemo._sizeOf_1` | definition | none |
| `ValueMemo._sizeOf_inst` | definition | none |
| `ValueMemo.casesOn` | definition | none |
| `ValueMemo.ctorIdx` | definition | none |
| `ValueMemo.diagnostic` | definition | none |
| `ValueMemo.mk` | constructor | none |
| `ValueMemo.mk._flat_ctor` | definition | none |
| `ValueMemo.mk.inj` | theorem | none |
| `ValueMemo.mk.injEq` | theorem | `propext` |
| `ValueMemo.mk.noConfusion` | definition | none |
| `ValueMemo.mk.sizeOf_spec` | theorem | none |
| `ValueMemo.noConfusion` | definition | none |
| `ValueMemo.noConfusionType` | definition | none |
| `ValueMemo.rec` | recursor | none |
| `ValueMemo.recOn` | definition | none |
| `ValueMemo.rewrite` | definition | none |
| `changed_extrusion_parents_nodup` | theorem | `propext`, `Quot.sound` |
| `changed_extrusion_targets_persistent` | theorem | `propext`, `Quot.sound` |
| `fallback_requires_unwritten` | theorem | `propext` |
| `prior_changed_extrusion_excludes_later_body` | theorem | `propext`, `Quot.sound` |
| `recordAdmission` | definition | none |
| `recordAdmission.eq_1` | theorem | none |
| `recordAdmission.match_1` | definition | none |
| `recordAdmission_retained` | theorem | `propext`, `Quot.sound` |
| `recordRewrite` | definition | none |
| `recordRewrite.match_1` | definition | none |
| `recordRewrite_exact` | theorem | `propext` |
| `retained` | definition | none |
| `retained.eq_1` | theorem | none |
| `retained_excludes_body` | theorem | `propext` |
| `retained_excludes_context_fallback` | theorem | `propext`, `Quot.sound` |
| `rewrite_initial_valid` | theorem | `propext`, `Quot.sound` |
| `rewrite_run_valid` | theorem | `propext`, `Quot.sound` |
| `rewrite_step_valid` | theorem | `propext`, `Quot.sound` |
| `rewrite_step_valid._simp_1_1` | theorem | `propext` |
| `_private.YulangClosure.OriginalTerminationClosure.0.YulangClosure.OriginalTerminationClosure.recordRewrite.match_1.eq_1` | theorem | none |
| `_private.YulangClosure.OriginalTerminationClosure.0.YulangClosure.OriginalTerminationClosure.recordRewrite.match_1.eq_2` | theorem | none |
| `_private.YulangClosure.OriginalTerminationClosure.0.YulangClosure.OriginalTerminationClosure.recordRewrite.match_1.splitter` | definition | none |

The nine-module import cone was separately inventoried. All seventeen textual
hazard-search matches are ordinary definitions/uses of an operation named
`admit` in `NativeContextExpansion` or `NativeValuePorts`; none is the Lean
admit tactic. The complete origin axiom audit is stronger than this textual
search. Dependency hashes are in the table below.

## Commands, failures and bounded resources

Pinned absolute executable:
`/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake`.
Observed versions: Lake `5.0.0-src+eb6cafb` and Lean `4.35.0`, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, x86_64 Linux Release.
The ordinary sandbox could not resolve the toolchain prefix; exact absolute
commands succeeded with `sandbox_permissions=require_escalated`, as directed
by the primary. No toolchain files, PATH or SYSROOT were modified.

All focused checks used the isolated project, `LEAN_NUM_THREADS=1`, `-j1`,
`-M1024`, and a 120-second per-invocation timeout. The final authored command
was the following with one `--theorem` argument for each of the eleven names
printed above; its exact argument vector is `check-04-authored.json`:

```sh
python3 /workspace/scratch/e3678bef96db/yulang/.agents/skills/yulang-lean-proofs/scripts/check_lean.py --project /workspace/scratch/e3678bef96db/termination-closure-r3/project --lake /workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake --module YulangClosure.OriginalTerminationClosure --timeout 120 --theorem YulangClosure.OriginalTerminationClosure.recordAdmission_retained
```

The helper checked both version strings, performed the qualified module build,
and printed types/axioms in a temporary audit file using the pinned toolchain.
The module-origin command was:

```sh
/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake --no-cache env lean -j1 -M1024 TerminationClosureOriginAudit.lean
```

Both successful audits were ordinary kernel-checked Lean invocations. The
module-origin file uses actual `env.getModuleIdxFor?` ownership, not just a
namespace-prefix heuristic.

| Check | Exit | Seconds | Evidence and repair |
|---|---:|---:|---|
| 01 | 1 | 27.767 | Included the eight-import build. Fixed `after_context_exact` equality orientation and an induction-constructor binder count. |
| 02 | 0 | 2.440 | Module and first named theorem accepted; one unused-simp warning. |
| 03 authored | 1 | 2.291 | Removing the warning also removed a definitional projection reduction before `subst`. |
| 04 authored | 0 | 3.035 | Added explicit `change key = request.pair at same`; all eleven roots accepted, no warning. |
| 05 origin census | 0 | 1.321 | All 81 module-origin declarations audited; all types printed and axiom whitelist satisfied. |

Five focused checks, total 36.853 seconds; longest 27.768 seconds. No checker
timeout. The packet budget was sixteen checks and fifty minutes. Early
nonchecking version-resolution diagnostics are not counted as Lean proof
checks. The isolated project has 177 byte-for-byte frozen baseline inputs,
all reverified against its manifest after final validation.

## Native observations

The primary supplied the unchanged baseline binary
`/workspace/scratch/e3678bef96db/native-principal-r3/target/debug/yu-playground`.
SHA-256: `e31bfadd06c2aa0a23168116f79ed71af80797e14bca21ec0d138cdb96c1fa46`.
Primary's 409-file build source manifest is
`/workspace/scratch/e3678bef96db/native-principal-r3/source-manifest.json`.
This leaf did not change or rebuild the compiler.

All six authorized probes were consumed, each with 20-second wall/CPU and
1-GiB address-space limits, inference only, and bounded inspector output.
All returned exit 0; total measured time 5.497 seconds, maximum 1.245 seconds.
No timeout or displayed resource cap is used as semantic evidence.

| Case | Seconds | Output bytes | Scope |
|---|---:|---:|---|
| nested-recursion | 0.850 | 4,273 | Ordinary inference and intrusion observation |
| nested-tuple | 0.841 | 4,656 | Ordinary inference and intrusion observation |
| self-application | 0.881 | 2,970 | Ordinary inference and intrusion observation |
| recursive-helper | 0.943 | 7,013 | Ordinary inference and intrusion observation |
| effect-bridge | 1.245 | 26,554 | Original annotated higher-order source fixture |
| effect-bridge-scoped | 0.737 | 338,790 | Same source, native scoped experiment |

`native-probes.json` contains exact argument vectors, source/output hashes,
exit status, timeout flags and durations. Full inputs and outputs remain in
the owned scratch directory. The apparent EffectView-freshening cycle was
rejected after following actual signature construction and the low-level
EffectRow reuse guard; no source-reachable cycle is claimed.

## Frozen hashes and source integrity

SHA-256 hashes of reviewable repository files:

| Path | SHA-256 |
|---|---|
| `notes/theory/lean/YulangClosure/OriginalTerminationClosure.lean` | `f3b1373effdd99b5ef610f30ce3903ce119d66a4e16f9cf71ce09dee80ee00a6` |
| `notes/theory/2026-10-26-original-termination-closure.md` | `4199bac6f6a1d2d54178fcd5ed5924e24e8d4e39510d25efef073078bc453698` |

All thirteen live native/authority inputs below were verified equal to the frozen base bytes.

| Native/authority source | SHA-256 |
|---|---|
| `crates/yu-solver/src/lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |
| `crates/yu-solver/src/candidate_context.rs` | `57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61` |
| `crates/yu-solver/src/candidate_effect.rs` | `70c42056a1041d54f88f16d7712875e3acf9ef7649b99a34bc990ff19f04936f` |
| `crates/yu-solver/src/candidate_scheme.rs` | `02349de1a2d69289eb348f7ff807a9e36faa2e2028cf61d10c1af9cd364409c5` |
| `crates/yu-solver/src/candidate_source.rs` | `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a` |
| `crates/yu-solver/src/candidate_scope.rs` | `9fdb36b4bbd66d702fbd3fcfaf593bfbc5dce0c52ff3252442aeb998bbb52c2a` |
| `tools/inference-playground/src/lib.rs` | `45bf78af436efa50e02ca97ba3b639c11f7dd88272d87c47f2822643786653d4` |
| `tools/inference-playground/src/main.rs` | `39b0dc40148fa87468b44e7406ea0b9a08269043fe2379c553c486930b63cece` |
| `crates/yu-solver/src/candidate_context_tests.rs` | `0aec86b787796e4024e3d0d04fd755c7160d0cd76811ed49395230ea1fb64422` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| `notes/design/2026-10-24-birth-level-scc-intrusion.md` | `ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae` |

| Lean dependency (under `notes/theory/lean`) | SHA-256 |
|---|---|
| `YulangClosure/NativeContextExpansion.lean` | `9887bef34e51678cead77eaf84a2f9b47916987ea9cffaad5d4ef74d53de2ea8` |
| `YulangClosure/NativeMergeExpansion.lean` | `f14bd35e8f7a6b9f326dadf003797c63f4a48fd0d0c0c9d68891c579560baf6e` |
| `YulangClosure/NativeRecordPlan.lean` | `3cf43fdb754748b83a6816791d640752dda491b87f7e2513a27548a950b27d43` |
| `YulangClosure/NativeReplayCoverage.lean` | `e65d925ab5222fd6bbc4bf63e756701aaba1273fff677ceb052d7f66e6450b7e` |
| `YulangClosure/NativeReplayCurrent.lean` | `fdd7dfa32f944f09b2cfc7440caeff95edcfad1fd5c839094f186d27168d9088` |
| `YulangClosure/NativeValuePorts.lean` | `f49bf12537633c65b4dbdcb4e739df5de5eee76cfb5ad845c8dba50cef4101fa` |
| `YulangClosure/NativeValueStructure.lean` | `81060e17ad37f2e4a47edb7ed2829bea6820438bf3d4db0e4de8d113fd9497fc` |
| `YulangClosure/OriginalTerminationClosure.lean` | `f3b1373effdd99b5ef610f30ce3903ce119d66a4e16f9cf71ce09dee80ee00a6` |
| `YulangClosure/RecordBoundaryPreservation.lean` | `1bde9224c1b0d568d5cc73d84a5ccc5f1157452c87ea2ff428096c1dbd50d056` |

Scratch receipts below are relative to `/workspace/scratch/e3678bef96db/termination-closure-r3`.

| Receipt | SHA-256 |
|---|---|
| `check-01.log` | `8806d5b5580d5aef25cbacc711fd308c9ba953ea383e804f00fb1654a19b2688` |
| `check-02.log` | `9b9f9069fbc9fadeb50673bf1a84d0185fbea621ca59571438e2b967b5aa37ba` |
| `check-03-authored.log` | `d03950738b5869667719d70b9c3b7c1363deda2c01558f98bef6fdcc5cac8005` |
| `check-04-authored.log` | `a7b58be7cf929e8826e97d26a2119ce09b7edeb6d4bc764ae6db7e2d9b7d76d4` |
| `check-05-census.log` | `b6cb0e633370664113d950598d35595755dbaef7fa20c79dd8b641bc33b301f4` |
| `check-01.json` | `584f942032f5be2e86165b893fb320bf40f09cb851e08a5314a305fb3c89100f` |
| `check-02.json` | `06f70fd2e6234da3e08b31c5ffbd93891bf5ebb68bee8c8c9f72dab5451f8948` |
| `check-03-authored.json` | `987f877db8811a3df4b7ae78be0ba280e9680cc8c3d834b4b9ef5feaeab7e674` |
| `check-04-authored.json` | `4c6e3308aa16c98270723bfe66a2a4864525d4e9e4538c486890f9ac79ac5d3d` |
| `check-05-census.json` | `1ceb1122490186e1dab11d5353598a305f14ed90a20c46e544b5efaea6144f34` |
| `origin-census.json` | `5306521447182e75c2b66e83f7eed228cfa4a277ede13abeefc9a7c826e6e3cc` |
| `declaration-census.json` | `e50af5a41698905a5a4c2e153e7b1958211bc44f70d80b729fb39d43a4ff5611` |
| `dependency-cone.json` | `c04f551c9856b9771b2a1145d0f7d23fbd1a3d5ddc6ba307c355047d98639f1f` |
| `source-dependencies.json` | `fca6bffae5be5639490c54f017bdb7006dc33af0ffe8492015da5918c9b9f135` |
| `baseline-inputs.json` | `6bbe32cfdcff9e6ada673150e9ea7e102917a0cf7754ac1363e3cfcb9791033e` |
| `native-probes.json` | `a92e09c655b0dd8043ce2fa05ca5b343e71ad965143e94ca204259185445d34c` |

## Remaining original goal and next exact proof boundary

The original contract is still
`∀ s x n, supported s → inferInitial s x n → Acc (fun next prev => inferStep prev next) n`.
This packet removes one false source of unlimited extrusion allocation:
changing generation/Context alone cannot republish a changed target for a
fixed raw Value pair in the uncancelled projection.

The remaining allocation obligation is a source-derived finite ancestry for
**new raw endpoint pairs**, including source FreshUse from the current graph,
new Value structures/rows, level-lowering merges and canonicalized pairs.
It must be derived from the source cursor and actual silent extrusion links,
active bound replay, capture incidence and retained-copy behavior. No such
bound is assumed or established by the present module. Decreasing copy level
alone does not bound lower-level siblings.

A concrete whole `inferInitial`/`inferStep` assignment is still absent from the
existing repository model. It must compose source cursors/use publication,
graph and typed tables, levels/representatives/intrusion generations, Context
and relation state, pending work, replay cursors and retained child-drain
stacks. The required committed/private-attempt extraction across rollback
must accompany that composition. Then the exact finite event supply and
callback return order must support the actual global accessibility theorem.
The ordinary Context enqueue finding narrows this composition, but does not
prove total nested retained restoration.

This packet is offered for independent native correspondence and theorem
review; worker kernel acceptance is not self-certification. No principal,
soundness or global termination gate is declared passed.

**Writes stopped:** revision 1 freezes all three leased repository paths and
all evidence referenced above. All checker/probe processes launched by this
worker have exited; there are no child agents. The primary may independently
review and commit this component. Continuing global ancestry requires the
primary's requested follow-up exact new-file lease; the original task remains
active at the primary level.
