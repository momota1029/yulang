# R27 admission and source intake

Sprint: `EFFECT-PERMISSION-OWNER-CERTIFICATE/20261030-R27`. Status: admitted by Luna; child work waits for the admission push.

## Frozen records

- Contract: `tasks/agent-loop/sprints/effect-permission-owner-certificate-20261030-r27.md`, SHA-256 `2cc9c8ae08a6fcbf98f237e6a1640ceb042a456a6beaadc448fa0a0308b431f0`.
- Schema: `tasks/agent-loop/sprints/effect-permission-owner-certificate-20261030-r27-schema.json`, SHA-256 `15eeaa3fdb4243dfbbea19fd752f30d1cb858d75f38352144b34d42c59bd2bf8`.
- Inputs: `tasks/agent-loop/sprints/effect-permission-owner-certificate-20261030-r27-inputs.json`, SHA-256 `4a7f4f5e2f9892d2a4f9f2cf6721be4e7b975b823d9798914819a8eb3062a878`.
- Branch admission base and upstream before this admission: `68dd3616e6b3b31cae67bd855c14d919beedde0b`; `origin/yulang3` matched this exact ref. The full upstream outbound range therefore contains only the admission checkpoint once committed.
- Clean runtime source baseline: `9a74a70a32ebda716a00c7203d8e606343cf442a`. Direct SHA-256 comparison confirmed runtime `machine.rs`, `receiving.rs`, `continuation.rs`, `program.rs` and the companion fixture match the branch admission base byte-for-byte.

## Dispatcher, parent gate and decision

At the sprint boundary `/root/next_action_selector` proposed authenticating immutable template/frame certificates and proving owner-replay correspondence. The live primary accepted the bounded direction because R26's rejected candidate lacked exact immutable node lookup, connected complete outer boundaries, and mutations that establish a real changed target. This does not authorize production representation changes or a semantic/source-domain change. R26 remains `CLOSED_INCOMPLETE — PREFLIGHT_REJECTED`; its separate budgets and candidate are not resumed or rewritten.

The unchanged effect-hygiene parent and user-approved callback/companion behavior remain OPEN. The R26 Lean artifact is reused only as a read-only abstract conditional module; its hash is pinned in inputs. The candidate is explicitly test-only and provisional. Native Grant, RootComp reachability, concrete History conversion, source/native application, parent soundness/principality, termination and production remain OPEN.

## Live roster, leases and resources

At `2026-10-29 20:42:56 UTC`, live roster synchronization showed `/root` active; all returned prior child assignments were completed except `/root/effect_permission_owner_consumer_r22_review`, which was interrupted. No child was running or waiting. The stale `/root/latent_demand_transport_classification_r17_source` row remains WAITING in current state but was absent from the live roster; its held inbox path remains unchanged and is not reused. The already authenticated 13-slot capacity override remains unchanged; this admission releases no capacity and no path lease. All UNKNOWN identities and quarantined root paths remain intact.

Only the exact R27 paths in the contract/input manifest are newly leased. The root runtime `machine.rs` and `receiving.rs` remain quarantined to `UNKNOWN_WRITER`; the worktree is detached and will be created from committed `68dd3616e6b3b31cae67bd855c14d919beedde0b`, never from root working bytes. Existing dirty/untracked paths are excluded from Git staging.

Fresh finite envelope: Rust 1,550s; Lean 800s; one independent referee 1,000s; Luna 3,850s including 500s closeout; total 7,200s; Astra 0. Cargo total ≤360s; at most two Lean audits and 120s combined. Heavy processes serialize. Candidate compile/runtime require fresh exact-hash independent ACCEPT and a separate Luna stage authorization. No R26 remainder transfers.

No compiler, test, formatter, Rust build, Lean/Lake audit or runtime command ran during admission preparation. `python3 tools/agent_sprint.py check` is required after state synchronization. No workers were launched before the admission is pushed.
