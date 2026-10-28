# NATIVE-IDLE-CHILD-LAUNCH/r5 outcome — CLOSED_INCOMPLETE

**Status: CLOSED_INCOMPLETE / REJECTED.** Independent review rejected the frozen Rust and Lean package. No Cargo, Lean/Lake, build, test, formatter, or producer revision is authorized under this packet. The broad soundness/effect-hygiene goal remains OPEN; no parent, source/native, semantic or production gate closes.

## Authority and inputs

- Contract: `tasks/agent-loop/sprints/native-idle-child-launch-20261028-r5.md`, SHA-256 `dacdb0dac5b36b13d3e1ee3b8ea37d08195668b4e4620a5fba5d7fdd6ca33ecf`.
- Amendment 01: SHA-256 `1f75d1fde7945f7bb937daf26201ca6cb9ffd708182d24186e9fef5b86170687`.
- Amendment 02: SHA-256 `b8be576a1890081f7aa0f8be759e7922941d255a7b1da31ed89a74b1a592c787`.
- Source baseline: `418bde889`; record-only state was kept separate from source baseline.

## Frozen outputs

| Artifact | SHA-256 |
|---|---|
| Isolated `candidate_scheme.rs` | `6164824155f75c9c164d40b6a7c6dc2ebf9de12c10ff23bb0086e5044b0f0142` |
| Isolated `candidate_extrusion.rs` | `e885c26fb77aa7619cb05c40148b841b5ed5d6e7111dea8f8299294c9b0ba0e0` |
| Isolated `candidate_context.rs` | `6e6259e1ed0d612a0e219abc6f86211299c4d2c7ec124566f459b29a9526d1c2` |
| Rust handoff `tasks/agent-loop/inbox/native-idle-child-launch-r5-rust.md` | `a3c39846a6ebff047bcf327c347717758bdffe1f969dee2d50b9250207920809` |
| `NativeIdleChildLaunchR5.lean` | `282e0f68922d3176e0d98aab04e535426cf2558403f2648ee4916ec5bb1644f4` |
| Proof handoff `tasks/agent-loop/inbox/native-idle-child-launch-r5-proof.md` | `1757aed4b4a6bf0657596f3a826845a0fd550078573073ed128c670d3b8620a8` |
| Independent review `tasks/agent-loop/inbox/native-idle-child-launch-r5-review.md` | recorded after primary persistence |

Rust evidence is provisional test-only source instrumentation. It records an actual restoration return, FreshUse source association, mapped destination and emission readback, and attempts a same-ID raw transformer falsifier. No ordinary test was executed. The Lean module has eleven local calculations but no successful Idle/Some-to-Running theorem. It stops at the capacity-growth resource observer in `candidate_prepare_replay_wait`; theorem printing and complete axiom audits are NOT_RUN.

## Independent review and disposition

Reviewer: `/root/native_idle_child_launch_r5_review`, registered `compiler_referee`, requested Sol/medium and observed model/effort UNKNOWN. Read-only source-first review; no checks, Git, builds, tests, Lean/Lake, formatter, descendants or generated outputs. Reviewer-authenticated clock interval: 09:12:30–09:14:11 UTC; total assignment duration was not measured.

Verdict: **REJECT**. Blocking findings:

1. Statically identified use-after-move of `ScopeTransformer identity` in isolated `candidate_scheme.rs:8022`, followed by use at line 8028; no compiler ran.
2. Completed authentication consumes retained readback records but does not reread the current physical vector slot, permitting vector replacement/removal with evidence retained.
3. Restoration handle is recorded but not checked by matching or completed authentication; sibling reassociation is invisible.
4. `candidate_context.rs` adds observation type, State vector and recorder/accessor beyond Amendment 01's sole raw-row replacement helper. No retrospective waiver.
5. The raw-mutation rejection assertion precedes restoration, so assertion failure leaves the row mutated, contrary to contract ordering.

The Rust worker separately disclosed two prohibited non-mutating Git commands (`git diff --stat`, `git diff --check`). This deviation is retained and not waived; the reviewer did not independently authenticate execution history. These technical and authority findings independently require rejection.

The original `SourceProblem.InferenceSoundness` quantification and separate `NativeCorrespondence` remain OPEN. No concrete parent instance, shared source witness, full-language proof, or production correctness follows. All original scope, immutable-birth correction, and effect-hygiene obligations remain unchanged.

## Execution and records

No conditional compiler/Lean/Cargo check occurred. Rejection closes the packet before its conditional checks gate. Rust and proof outputs are frozen; no revision follows. Preserve R4 history and all unknown/quarantined paths. At this disposition, `current.json` is synchronized with STOPPED proof/Rust/reviewer receipts and frozen artifact hashes. `python3 tools/agent_sprint.py check` passed after synchronization; this is static record validation, not source/compiler verification.

The primary authored and pushed the in-scope autonomous-continuation instruction in `AGENTS.md` at commit `80119f69a`; the user's latest instruction confirms it remains applicable.
