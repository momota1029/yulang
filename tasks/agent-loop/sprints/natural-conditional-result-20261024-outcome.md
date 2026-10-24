# NATURAL-CONDITIONAL-RESULT-20261024 — live outcome record

Status: ACTIVE; graph-generic proof construction continues in the isolated worktree. No source edit, build or runtime observation is claimed.

- Parent objective: implement Yulang type inference and evaluator from proofs. Whole-language inference/evaluator and original A/B remain OPEN.
- Selected obstruction: candidate graph construction already records both conditional branch result constraints, but `scheme.rs::heads` rejects distinct concrete Value lower heads.
- Before evidence: baseline `d788d94da66385bf09947932f0aae1972cd51f21`; `candidate_source.rs` SHA-256 `57b119592a6a8d4afd42aca10c5e2bb749cfdf0fb0fdea967dd437d552a1a04e`; `scheme.rs` SHA-256 `82019fd22ad565c753461d8962934fcfe8e6663f8a7971b4fcbc5f5067026be0`; `lib.rs` SHA-256 `45bf78af436efa50e02ca97ba3b639c11f7dd88272d87c47f2822643786653d4`.
- Exact proof destination: `notes/theory/2026-10-24-natural-conditional-result.md`; handoff: `tasks/agent-loop/inbox/20261024-natural-conditional-result.md`.
- Exact implementation lease: `tools/inference-playground/src/scheme.rs`, Luna only and only after proof review.
- Isolated branch/worktree: `codex/natural-conditional-result-20261024`, `/tmp/yulang-natural-conditional-result-20261024`; source baseline remains d788. Legacy UNKNOWN reservations stay quarantined; no merge/copy-back is authorized.
- Authority: sprint contract rev3 `tasks/agent-loop/sprints/natural-conditional-result-20261024-rev3.md`.
- Proof producer remains active on the exact note/inbox leases. No proof result, source change, build, or runtime observation is claimed yet.

## Revision 2 boundary

After the producer identified that source `If` actions enter the solver's candidate-specific typed drain, the dispatcher recommended a narrow read-only expansion. Rev2 pins the actual path through `constrain_live_value` / `run_candidate_typed_drain`, `candidate_apply_value`, candidate bound/identity retention, and `CandidateGraphExport`. Added dependency hashes were matched in the isolated worktree before access: `lib.rs` `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07`; `candidate_extrusion.rs` `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61`; `candidate_scheme.rs` `02349de1a2d69289eb348f7ff807a9e36faa2e2028cf61d10c1af9cd364409c5`; `candidate_context.rs` `33af2efb6ed782e4f143cccff03c62087e6ba8d0fbe90415846537fc2a08cec5`; `shadow_apply.rs` `f8d92f2d59353e5b9cda014545b352c8d6356cc0aff3b4eeae0e81893e78202d`.

The expansion changes no write lease, source semantics, executable validation, baseline, or budget. The producer is continuing the graph-generic projection proof; a scalar-only restriction would not satisfy the sprint. The public API renders binding items, so its exact observation wraps the unchanged `if true { 1 } else { "str" }` expression in `my answer = ...`; no parse/runtime observation is claimed.

## Revision 3 boundary

The producer identified that the local/shared classification premise also depends on definition-root initialization. After the `next_action_selector` recommended a narrow clarification, rev3 authorized read-only inspection in the same pinned `crates/yu-solver/src/lib.rs`: definition-root initial `level` and `non_generic`, its contrast with expression-root initialization, and the direct join from those fields to exported local/shared classification. A later mutation may be read only if it directly affects that classification, with its owner identified before relying on it.

The proof claim now covers only constraints and identities represented by the existing `CandidateGraphExport`; both conditional contributions reaching that export remains explicit. It makes no claim that the export contains every source fact. No dependency hash, lease, budget, source/semantic authority or executable validation changed. The falsifier remains: a shared/non-generic root is quantified, a local row is misclassified as an external anchor, or final locality relies on an initializer without accounting for a relevant later mutation.
