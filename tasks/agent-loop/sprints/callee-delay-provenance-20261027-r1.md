# CALLEE-DELAY-PROVENANCE-20261027/r1

Status: PRIMARY-ADMITTED bounded constructive proof/source-correspondence sprint.
Baseline `f0acc5d1ab103adf4f41f49088b754231b665c1b`, branch `yulang3`.
Authority: unchanged original whole-Yulang inference/executor obligation and approved Simple-sub design. No compiler behavior, Rust, semantic, source-domain, or production change authority.
Contract revision r1. Primary Luna grants exact leases below after this byte hash is recorded in `current.json`.

## Original parent and fixed outcome

The parent remains the complete original inference/executor A/B obligations over all supported source forms, original quantifiers/scopes, lawful histories, complete Call/effects, and the shared-witness requirements. Whole-language soundness, Effect hygiene, principality, progress/termination, source/native correspondence and production remain OPEN.

Construct the actual Callee Delay/value/view allocation prefix and compose it with the accepted post-Delay-allocation Value-entry suffix. The outcome must either establish a constructor-preserving representation relation for the composed path or isolate its first exact missing owner law. Another executable projection alone is insufficient.

Altitude: remove the existing suffix theorem's independently supplied Delay handle/view operands.
Depth: follow `machine.rs:1181–1198, 2028, 2701`, `receiving.rs:208–222`, the actual Closure continuation, and later ValueEntry Force. Preserve the source site, argument code, saved environment, ValueHandle freshness, executable insertion, direct-formal lookup result, inherited image/unknown coverage, and all state mutation order.
Range: use compositional data refinement over the append-only value/view stores and executable insertion. Derive freshness, lookup and preservation from constructors, then transport the existing suffix result through the relation. Do not introduce a free simulation premise or identify receipt histories merely by count.
Independent falsifier: mismatched fresh handle, code/environment, old executable/value preservation, inherited view, provider source, dictionary state, or failure poststate defeats the correspondence. A Lean-only happy-path projection without source-to-model laws is not success.

The source Parameter receipt is formed before the native pre-Force Value-entry demand in the current original constructor path; the Rust Value callback receipt is minted only after Force returns. Keep source receipt, native receipt, and demand event distinct unless an existing proved law connects them. The prior Return-assignment vs `Native.fields` equation stays OPEN. If the original consumer cannot preserve required receipt identity/owner/view, report that exact obstruction without narrowing the original source domain or changing semantics.

## Two continuing lanes

**Implementation/source lane:** registered `implementer` is granted read-only inspection of at least the two exact Rust owners below. It must check the actual allocations, source/formal resolution, view inheritance, receipt timing and later consumers, and either identify a concrete approved owner-local correction or return `NO_SAFE_CODE_SLICE` with owner-specific evidence. This contract grants no code edit. Luna will apply any accepted source result to the parent; absent a real confirmed defect there is no Rust change.

**Proof lane:** one registered `lean_prover`, requested Sol/high (effective settings UNKNOWN unless reported), writes the exact Lean module, audit and single handoff below. Stages: (1) encode only the Rust constructor state needed for Callee Delay/value/view provenance; (2) derive append freshness, executable lookup, source/environment retention and inherited view coverage; (3) compose with `OriginalValueEntryDemand` suffix without free Delay/view operands; (4) connect the original receipt consumer from constructors or stop at the first exact owner law. Apply every useful result to the full parent and preserve omitted branches.

No Astra assignment: the decisive challenge is constructor correspondence and representation alignment, with established Sol/Lean path and no named core risk justifying Astra. One child at a time; wait for stopped-writes evidence before the next child. Fresh review is assigned only after the proof bytes and direct dependencies freeze.

## Exact leases and boundaries

Proof artifact leases:
- `notes/theory/lean/YulangClosure/OriginalCalleeDelayProvenance.lean`
- `notes/theory/lean/AuditOriginalCalleeDelayProvenance.lean`
- `tasks/agent-loop/inbox/callee-delay-provenance-20261027.md`
- isolated proof/cache/log output under `/tmp/yulang-callee-delay-provenance-20261027/proof`

The implementer is read-only on `tools/inference-playground/src/runtime/machine.rs` and `tools/inference-playground/src/runtime/receiving.rs`; it has no file output lease and may not edit source/tests/configuration. Luna alone owns `current.json`, the outcome record, Git and integration. No root import, manifest/toolchain/lockfile, tests/expectations, source restriction, new semantic decision or production edit is authorized.

## Frozen pins

Before any proof write, verify every dependency against workspace bytes and `git show HEAD:path`. Stop on any mismatch. The baseline tree is exactly commit `f0acc5d1ab103adf4f41f49088b754231b665c1b`.

```text
10ff6a2d4ac8a4a2c386396c495e0edfecc9bd4bb3ae40c8e0ab07e4cb0c7531  notes/theory/lean/YulangClosure/OriginalNameForceExtraction.lean
f26878514518f14a4a99e799dad2ca28e4513c467a8dd24d86e6329b9e640616  notes/theory/lean/YulangClosure/OriginalIdentityCarrier.lean
30b0676f4af22dc7da2c75596a338db57a24b17662a4057801cfdff7ab4a2f42  notes/theory/lean/YulangClosure/OriginalIdentityRealization.lean
0710f5d969af927c8f42b42f4972ba4f53ddce4ddb082e9d3d360e90c9ccf12b  notes/theory/lean/YulangClosure/OriginalReturnWorld.lean
abb9d69546e284fcb5fe6be9bb3c18269227e91da94e09eebf1a62e0b56e67f7  notes/theory/lean/YulangClosure/OriginalFormalShared.lean
0e12d33d1b912820324f5140fbe3f16983d0b7ef33137642aaef07faa573f132  notes/theory/lean/YulangClosure/OriginalSourceEnvironment.lean
1069c185c6fa190c2a0dd776ebf4efc7bfab8ece7e36f2f4049d480e50fa65e7  notes/theory/lean/YulangClosure/OriginalRecursivePair.lean
9a171ecfbad7d632b2a15ef1f57d2d2dd46444aa36452de9158f1d1c7cfdae63  notes/theory/lean/YulangClosure/OriginalValueEntryDemand.lean
efceba608e3942710c4f53d8bfc1516ba3f18c5470b7fae64810e04020d04772  notes/theory/lean/AuditOriginalValueEntryDemand.lean
ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c  notes/theory/lean/lean-toolchain
212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4  notes/theory/lean/lakefile.toml
058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3  notes/theory/lean/lake-manifest.json
b621ba8ec28d7819db881a4fd5bad0236edbf23e2aa92a879eb1dd211a30c46e  tools/inference-playground/src/runtime/machine.rs
57b1664e26f137e6425731dde2bb1f1559170d9914f5be7a0f17fae3a8555e26  tools/inference-playground/src/runtime/receiving.rs
63abf6e04d1d8d6b365690ff0bbf345978b56a08f2f6903fe9fd322e9139267f  tasks/agent-loop/inbox/value-entry-demand-20261027.md
6b9b1a67551e679af7c5b82197f2274eb764b02d6dde1f1d1ecfac8655e4276c  tasks/agent-loop/inbox/value-entry-demand-20261027-review.md
1a877139a8a10b5cfa7882459234345b3505d75d775280af613a34bc74420b54  tasks/agent-loop/sprints/value-entry-demand-20261027-r1-outcome.md
69ea721db72b5f11b9a640c63d06a5672c625adc43a068ed1f2e7c44bf82c795  tasks/agent-loop/inbox/name-force-receiver-join-20261027.md
```

The current sprint contract and each leased output are not dependency inputs. Use pinned Lean 4.35.0, `-j1 -M1024`.

## Resources, checks, review and stop

Total sprint ceiling 2700 active seconds: proof <=1500, primary source/check/integration <=600, fresh review <=420, selection <=180. Proof <=6 checker invocations/360 seconds, 120 seconds each; at most one heavy process and one checker owner at a time. Astra 0. Preserve all nine historical UNKNOWN reservations as quarantined; one serial child at a time. Record runtime IDs/receipts, requested/observed model separately and UNKNOWN when missing. Do not reclaim uncertain leases or reset spent budget.

Proof worker must retain failures, print complete originating theorem types and audit every originating declaration/transitive axiom. No `sorry`, project axioms, checker bypass, global option relaxation or native-evaluation assumption. Primary independently verifies exact frozen hashes and checks the module in a separate isolated copy. A fresh non-author `compiler_referee` reviews frozen constructors, representation equations, failure states, receipt/demand distinctions and parent application; author and reviewer never overlap.

Stop before assuming any native/source readout equality, changing original source coverage, or spending beyond this packet. A source-qualified counterexample remains distinct from a projection obstruction. Integrate a coherent reviewed milestone with current-state/outcome receipts and exact paths. Next selector trigger: material source/consumer obstruction or counterexample, changed authority/dependencies/leases/resources, cross-lane seam, or sprint END.
