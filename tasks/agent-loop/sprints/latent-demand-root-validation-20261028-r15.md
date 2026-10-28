# LATENT-DEMAND-ROOT-VALIDATION/r15 — complete workspace validation

Status: **ADMITTED BY LUNA** under the standing inference/executor research
authorization. This is a new packet after R14 `CLOSED_INCOMPLETE`; it does not
reopen or retry R14.

## Fixed objective and boundary

Run the unchanged focused fixture once against the exact R14 candidate using a
complete, byte-pinned Cargo workspace. Determine whether FreshUse passes the
original demand-root lookup and reaches the next existing guard, or record the
next concrete failure. Relate the observed native trace to the original source
Call/Generalize obligation without treating root lookup as source adequacy.

The R14 candidate is immutable at SHA-256
`f489868d88e6f56724bdd2c83d2979edc8a9a0c077dd4e81ff6c9f3ef374d4f0`.
R14 remains `CLOSED_INCOMPLETE`; its Cargo attempt failed before test
execution because the isolated workspace lacked a declared member. This packet
uses a new workspace and a fresh one-attempt grant. It does not edit the
candidate, change `Cargo.toml`, remove members, change `Cargo.lock`, alter
dependencies, weaken guards, change expected output, or patch semantics.

## Frozen input snapshot

Input manifest: `tasks/agent-loop/sprints/latent-demand-root-validation-20261028-r15-inputs.json`,
SHA-256 `53464d82524e314e468bb02cf5ed49886a208be9bc2719d1da06ef242685ea32`.
It pins 418 workspace files plus 8 governing semantics/theorem inputs and
references the exact R14/R13 parent receipts. Snapshot:
`isolated/latent-demand-root-validation-r15/`.

The 418 workspace files are the 324 exact R14 workspace inputs (with the
reviewed candidate successor at its frozen hash) plus all 94 tracked files for
the formerly absent `apps/yulang-wasm`, `tools/bench-runner`,
`tools/inference-playground`, and `tools/xtask` members from baseline commit
`31aa3451dff76185ccb642191f25e0dc97116342`. The snapshot contains all 12
declared workspace member manifests and all 15 direct path references resolve.
No package manifest or lockfile was edited. The build target is new and
isolated at `isolated/latent-demand-root-validation-r15/build-target`; no
prior cache is used.

Before Cargo, Luna authenticates all manifest entries and the complete member
and path-dependency closure. The implementer and source/proof worker
independently authenticate their assigned inputs. A fresh reviewer must ACCEPT
the complete inputs and frozen candidate before the test may run.

## Exact leases and lanes

- Luna primary — **600 seconds** total. Owns the exact 418-file snapshot,
  manifest, current state, the one Cargo attempt, `isolated/latent-demand-root-validation-r15/logs/r15-cargo-1.*`,
  and final review/outcome receipts. No other primary source path is authorized.
- Luna/high implementer — **300 seconds**. Read-only snapshot/candidate
  completeness and native-invariant audit. Sole write lease:
  `tasks/agent-loop/inbox/latent-demand-root-validation-r15-impl.md`.
- Sol/high source/proof — **600 seconds**. Map actual execution evidence to
  the original Call/Generalize obligations, preserving their open status.
  First stage (up to 300 seconds) audits the frozen source rules and defines
  the exact native joins and still-open laws; freeze handoff revision 1 and
  report `WAITING` for the Cargo receipt. After Luna ACKs that handoff and
  freezes Cargo-1 logs, resume within the remaining original reservation for
  the trace-to-source analysis; freeze sequential handoff revision 2. Sole
  write lease:
  `tasks/agent-loop/inbox/latent-demand-root-validation-r15-source.md`.
- Fresh independent reviewer — **300 seconds total**, in sequential stages:
  pre-run input review up to **90 seconds**, then STOP; after Luna ACKs the
  frozen receipt and completes Cargo-1, resume the same reviewer for up to
  **210 seconds** to authenticate and review the retained execution evidence.
  Sole sequential write lease:
  `tasks/agent-loop/inbox/latent-demand-root-validation-r15-review.md`.

Aggregate cap: **1,800 seconds**. Astra 0; no descendants. Worker grants are
not extended or reset. The pre-run reviewer STOP receipt is required before
Cargo. Any STOP, missing pin, changed candidate, input gap, reviewer rejection,
or budget boundary prevents the run or ends the packet.

## One exact Cargo attempt

Only after pre-run review ACCEPT, Luna may run this exact fixture once:

```text
CARGO_TARGET_DIR=isolated/latent-demand-root-validation-r15/build-target cargo test --manifest-path isolated/latent-demand-root-validation-r15/crates/yu-solver/Cargo.toml --locked --features shadow-apply-candidate replay_constructor_lineage_observes_rejected_cross_route_authentication
```

Limits: wall **180 seconds**, CPU affinity **0 only**, process-group RSS at or
below **2 GiB**. Record exact argv and environment, Cargo/rustc versions,
complete stdout/stderr, UTC start/end, exit status, sampled process-group CPU
and peak RSS, and limit termination. No second attempt, workspace repair,
semantic patch, alternative command, Lean run or other test is authorized.
Any Cargo error, timeout, resource breach or runtime failure ends this packet.

## Acceptance and source boundary

The maximum positive result is evidence that this fixed candidate and this
focused native fixture pass the original root lookup and expose the next
existing guard or success. Capture graph, bound/relation, root and node must be
joined within the same invocation. Preserve the antecedent's observed
`EvidenceCoverage { gaps: 56 }` unless new exact output proves otherwise; do
not infer eligibility from map membership.

The source/proof receipt must state which source obligations are evidenced by
the trace and which remain open. It must preserve original
`YulangClosure.SourceProblem.InferenceSoundness`, source Call/shared-witness,
Generalize allocation, complete source/native correspondence, effect hygiene,
principality, termination, and production as **OPEN** unless separately
established through their governing obligations. The R14 native
representation ACCEPT supplies no source law. No source-domain restriction,
fixture expectation change or inference rule change is allowed.

Final status is `DONE` only for the bounded evidence goal after post-run review
ACCEPT and Luna integration. A workspace/load/build/test failure is
`CLOSED_INCOMPLETE`, not a reason to retry here. All parent and production
gates remain separate.
