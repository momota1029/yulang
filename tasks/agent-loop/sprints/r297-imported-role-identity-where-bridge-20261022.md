# Sprint R297 — authenticated imported role identity in declaration prerequisites

Status: CHECKPOINTED_UNREVIEWED
Branch / baseline commit: research/simple-sub-intrusion / 6977aff3569c86847a318e5776d01a5801defd5c
Authority: user-provided unchanged Y2 samples; Authoritative R149 design; design plan stage 4; proof companion §§7.1–7.2.
Mode: solo serial continuation under the user's no-subagent instruction. No independent review is claimed.

## Original outcome and success evidence

Parent: R149 unchanged Types/Console samples, ordinary test execution, runtime output, source/native correspondence, and proof; all remain OPEN.

This slice joins an implicitly imported `where` role spelling to the exact provider `SourceRoleId`, then retains that identity beside the declaration's existing subject row and source nodes. Success requires a source export route and provider role index to agree on module, declaration source, range, visibility, and name. Missing or stale identity remains unavailable. Existing import construction without role indexes must not invent identity. Candidate preflight for nonempty `where` clauses remains fail-closed.

## Implementation paths

- `crates/yu-hir/src/module.rs`: include the role head in implicit-prelude name collection; add an import constructor that authenticates resolved role exports against supplied provider role indexes.
- `crates/yu-hir/src/module/source_exports.rs`: retain optional exact role IDs in the source import environment.
- `crates/yu-solver/src/candidate_effect.rs`: join a where-clause spelling to the resolved imported role identity.
- `crates/yu-solver/src/candidate_scheme.rs`: retain the optional identity through the existing obligation, Capture, and FreshUse copies.
- `tools/inference-playground/src/lib.rs` and the solver's focused test: check exact provider identity and its arrival at the retained declaration obligation.
- One outcome note and compact current-state update.

No type-directed obligation solving, implementation selection, imported provider scheme assembly, sample rewrite, runtime change, or preflight opening is authorized by this slice.

## Proof boundary and open premises

The source route and provider role declaration are joined by exact source identity. The carrier stores identity only; no conformance, role satisfaction, method lookup, or call certificate follows. Capture/FreshUse transports the record structurally, not a proof of role discharge. R149 source/native correspondence and whole-compiler theorem remain open.

## Resources, review, and Git

Budget: 900 seconds, no carryover. Primary is sole writer and Git integrator. User-directed solo work means no independent reviewer is claimed. Tests are focused implementation evidence only. Keep the existing unknown legacy leases quarantined. Commit the coherent slice and push the research branch after checks; leave worktree clean.
