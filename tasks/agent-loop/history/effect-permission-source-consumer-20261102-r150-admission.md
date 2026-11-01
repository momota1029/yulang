# R150 admission — source laws and immutable-baseline Rust candidate

Admitted by Luna for the continuing user-authorized Rust/Lean effect-hygiene
objective. Dispatcher recommendation: derive producer initialization and
consumer laws from original rules, then make a candidate patch from immutable
committed blobs. No working-tree Rust edit, execution, or production promotion.

Contract: `tasks/agent-loop/sprints/effect-permission-source-consumer-r150.md`
SHA-256: `88583b62e60e28de8f14fe07c5ab2764ae2aae1922528b12d326656442fb9971`.
Baseline and branch: `7a8a20bf7a92172d7732ae7b18e0955423778f02`,
`yulang3 == origin/yulang3` at admission. Dirty working-tree files remain
excluded. Runtime `machine.rs` and `receiving.rs` remain UNKNOWN_WRITER and
QUARANTINED. `candidate_receiver.rs` is excluded because its dirty diff removes
owner/batch/live-state, provider/arm, and permission-origin checks.

## Governing source inputs

| Source | SHA-256 |
|---|---|
| Directional inferred-effect protection addendum | `f11c6594e43c29fbfdbca1638b5c548cecc12a5beb192cac743e60f022c1cc73` |
| Handler protection-filter derivation | `82402427727102e9afdf3065da4f6b6e2e836b4571b1355ece088dbda36f1cc1` |
| Concrete effect-annotation implementation | `3a3186723cd93edd2f767a7e4a481cb6dbed701fc749502e640071f65a4d89ae` |
| Annotation effect-hygiene integration | `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18` |
| Compose-scoped effect release | `fd56f819f9b33adc5d75cbfdae378c90903e4aa3a266fc053c05dda315d40679` |
| Playground hygiene soundness audit | `c5be565192c940e714832b86a16b7d3681b6d7cadc160f9ce6f38acb2974e3ce` |
| R149 outcome | see committed R149 outcome receipt and R149 contract/source/proof/review hashes in current state |

## Fixed packet and leases

Proof lane: registered `prover`, 900 seconds, output only
`tasks/agent-loop/inbox/effect-permission-source-laws-r150-proof.md`.
Derive incoming input/protection state per producer, same-witness FreshUse
transport, and distinct annotation permission / actual inflow / capture / scope
release / Catch consumer rules. No convenient assumed seed or arbitrary State.

Implementation lane: registered `implementer`, 900 seconds, starts only after
proof handoff is frozen; output only
`tasks/agent-loop/inbox/effect-permission-source-consumer-r150.patch` and
`tasks/agent-loop/inbox/effect-permission-source-consumer-r150-source.md`.
Candidate patch may touch only the six pinned Rust paths in the contract and is
not applied. Insufficient source law means no patch and a precise blocker.

Fresh `compiler_referee`, 360 seconds, reviews both frozen artifacts and exact
immutable-base coverage. Primary integration: 180 seconds. Total ceiling 2340
seconds; Rust/Lean execution, build/test, cache, scratch, new environment,
checkout, worktree, nested teams all zero. Existing parent gates remain OPEN.

## Runtime and Git

At admission, live roster synchronization returned `/root` active and all listed
children completed; no R149 worker remains active. Existing UNKNOWN assignments
and quarantined paths remain untouched; the current state already records a
user-authorized capacity reservation release. No path-lease release is inferred.
Only Luna owns Git. Admission checkpoint is safe when current state points to
this exact contract and the outbound range contains only intended R150 records.
