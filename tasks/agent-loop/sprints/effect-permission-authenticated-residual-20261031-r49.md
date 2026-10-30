# Sprint EFFECT-PERMISSION-AUTHENTICATED-RESIDUAL / R49

Status: ADMITTED for the exact bounded private experiment; author launches pending.
Branch / baseline: `yulang3` / `3b1ef27d3795b2bc56ab1718dcd3c06700699547`.
Authority: user's ongoing Yulang Rust/Lean effect-hygiene goal; `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1, 1.1–1.2, 3–5; `notes/design/2026-10-10-concrete-effect-annotation-implementation.md`; `notes/design/2026-10-11-yulang-inference-top-level-principles.md`; R48 reviewed bounded outcome.
Previous gate: R48 `CLOSED_BOUNDED_PASS`; permission consumption, residual subtraction, source extraction completeness, original A/B and production remain OPEN.

## Original obligation and bounded outcome

The original goal remains complete Yulang Simple-sub source preservation and effect hygiene over the unchanged supported source domain. For this effect position, the approved policy distinguishes annotation permission, actual constraint-derived inflow and residual: the Catch handles the selected concrete operation from the supplied computation, while another effect such as `write` remains outward. The permission does not create inflow or impose a closed input row. Full original A/B and hygiene claims are not changed or discharged here.

R48 added a private physical-lower-edge certificate tying the same R45/R47 Internal permission entry and original Catch slot-51 fact to one retained Operation `AnnotationMember`. Its search cannot pass through `Support(view)`, and the existing residual experiment's suppression branch does not consume R45–R48 evidence. The concrete next outcome is to connect authenticated permission, arrival, and source-selected Catch-arm evidence to the existing private residual fold while preserving every unmatched original endpoint.

Success evidence:

1. A typed path records actual current physical lower edges with their retained owners plus an explicit logical `SupportMember` expansion that reads the exact retained view, member ordinal/family, and closed-tail condition. No synthetic physical emission is invented for this expansion.
2. The selected arm certificate comes from the actual source Catch occurrence and arm: exact arm source/position, resolved operation declaration identity, supported payload/continuation pattern and Catch identity. A supplied `selected` boolean or same-family match alone is insufficient.
3. A complete immutable decision plan is validated before residual-result constraints are added. Suppression requires the same R45 permission, same R47 entry emission, R48 exact provider arrival/common endpoint and exact selected-arm evidence. Every unmatched original endpoint is forwarded unchanged, including a distinct contribution of the same family.
4. Missing or ambiguous evidence needed to suppress a matching provider candidate returns unavailable before residual publication. An open Support tail, stale/reversed edge, wrong arm, foreign provider, or disconnected path cannot authorize suppression or produce a successful fallback certificate.
5. The Lean model proves Support-member step soundness, accepted-suppression prerequisites, endpoint-wise residual-fold correspondence and unmatched preservation; it applies through R45–R48 with the same witnesses and retains source/runtime obligations as OPEN.

Falsifiers: permission without arrival; same-family but foreign operation; wrong Catch arm or declaration; missing/duplicate/stale/reversed physical edge; invalid Support member or open tail; a split endpoint/path; an unavailable certificate reported as success; dropping a sibling contribution at the same family; or mutating/publishing part of the result before the whole plan is checked.

## Exact lanes and leases

### Rust implementation — Luna/high, at most 1,800 seconds

Write only:
- `crates/yu-solver/src/candidate_receiver.rs`
- `tasks/agent-loop/inbox/effect-permission-authenticated-residual-r49-rust.md`

Refactor the existing private residual experiment and R48 certificate in this file only. Keep ordinary inference, routing, propagation, production consumers, public APIs, source semantics, diagnostics and fixtures unchanged. If a required producer/constructor outside the lease is missing, stop and identify the exact transition.

### Constructive Lean proof — at most 1,800 seconds

Write only:
- `notes/theory/lean/YulangClosure/AuthenticatedResidualConsumerR49.lean`
- `tasks/agent-loop/inbox/effect-permission-authenticated-residual-r49-proof.md`

Use the installed Lean 4.35.0 project through bounded read-only stdin audits, one CPU and `-M1024`, with at most 120 seconds per Lean process. Do not run Lake/build/tests/Cargo, create scratch files, `.olean`, cache, target, project copies or environments. Record complete types, per-theorem transitive axioms, commands, input/stdout hashes, all material failures, resource receipts and exact parent application. Never assume Rust extraction completeness, runtime success, selected-handler execution or source rules as a proved theorem.

### Fresh independent review — at most 1,200 seconds

Only after both authors STOP and freeze hashes. One fresh `compiler_referee` reviewer with no authorship or contributing descendants. Write only `tasks/agent-loop/inbox/effect-permission-authenticated-residual-r49-review.md` or return a complete frozen report for primary placement. Review source arm provenance, Support expansion, path and certificate lifetimes, prepublication plan ordering, exact native forwarding calls, family-sibling preservation, complete theorem types/axioms and dirty-baseline isolation. No builds/tests/checker rerun, Cargo/Lake, Git, scratch, cache, target or environment.

## Frozen baseline and direct dependencies

- Baseline and branch: `3b1ef27d3795b2bc56ab1718dcd3c06700699547`, `yulang3`.
- Rust owner before edits: `candidate_receiver.rs` `ae7d4b12db10f46ba4588bb2c62ef906a71997ae6de184dbc93bfe08644e533a`.
- R48 Rust source dependencies: `candidate_context.rs` `1ba38a85e8575b1d6d3cf50d918a3603c4e23068cb730d1c3645e605148636bc`; `candidate_effect.rs` `2a86befde95581decef8fe01698961062bd22388cff2459e9611570a20b9fba3`; `candidate_scheme.rs` `bf8f5c80ce2761dc2a1235d2e02e348a91bc9e8965653db26b9abd4c8d6ca631`; `candidate_source.rs` `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a`; `lib.rs` `25498cc1be404b12d060cbd47f77e78c23ad27b2b99113e15823bc8b6fa92ca4`; HIR `crates/yu-hir/src/module/local_source.rs` `7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1`.
- R48 reviewed evidence: contract `b4ff4331c8d864023a7f1afbdab779ef93e44ada738ec32fe179d114c4316cdd`; Rust handoff `ec21520fdb3857f6b379c5da8a9f0f5278fa5bb46114faa8905c7c2bd02ba677`; proof handoff `b7c6f80dcb943293f49f1dc7ba01c516706c58fa5e809970c9d27bde37697a38`; Lean `ProviderEntryArrivalR48.lean` `b85dfad5c0e80f7fbc2480e7f38421cc6c50107144d9abb160e688208b192575`; review `a11dfabcc5c7291299ce9a92d19f00bf70c3e7ac82da443d9f4d556c5af9a7f3`; outcome `28663a7ebc1bea04b6efd0ecfb1e12f15d2cbe9dc03398b65da9d6a2f1468186`.
- Inherited Lean dependencies: R47 `CurrentEmissionOwnershipR47.lean` `d64c54f7c977e110305a76e6437fc87c8ff14201a4d69eb0bbcb5ee0e1cd8b9c`; R45 `InternalPermissionIncidenceR45.lean` `9ff4fd544375a3d4a46100647cba93ddde6f34bebd767ba402f3bd3d35a84b1f`; `lean-toolchain` `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c`; `lakefile.toml` `212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4`; `lake-manifest.json` `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3`.

All pins are rehashed at admission and again before review/integration. Dirty dependency files remain exact read-only inputs. No unknown or quarantined path is read, reclaimed, or modified.

## Resources, non-goals and closeout

Aggregate sprint budget: 6,000 seconds — Rust 1,800; Lean 1,800; review 1,200; primary 1,200 including at most 500 seconds closeout; Astra 0. Keep one existing checkout and installed toolchain. No new worktree/environment, build/test/Cargo/Lake, formatter, cache, target, scratch, service or nested CLI. Preserve all 32 pending entries and UNKNOWN/quarantined assignments/paths.

This is a feature-gated private experiment only. No production cutover, language restriction, new effect semantics, arbitrary family deletion, or generic filtering. Original source A/B, complete source/native extraction, concrete Rust runtime success, Catch execution authorization, full subtraction/hygiene, principality, termination and production remain OPEN. No tests were added or run under this resource-bounded packet; source/Lean evidence is not runtime evidence.

Luna owns exact current-state and handoff intake, review adjudication, staging, commit and non-forced push. The next consultation boundary is a material blocker/counterexample, changed dependency/lease/authority, result-to-consumer seam, or sprint end.
