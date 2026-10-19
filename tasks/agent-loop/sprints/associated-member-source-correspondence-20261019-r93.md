# R93 associated member and role source correspondence

Status: ACTIVE; source correspondence only.  Contract revision: 1.
Branch / baseline: `research/simple-sub-intrusion` /
`d34568a7ca062c8004122bf4a9ac8d7fa9434bb0`.
Primary: Luna `/root`; Luna owns activation, review assignment, adjudication,
central state, integration and Git.

## Goal and bounded result

Add a checked source bridge from the R76 raw `FieldTail` inventory to the
receiver child produced by the existing `associate_chain_owned_with_sources`
constructor. Also resolve each retained `RoleDeclaration` and standalone
`ImplDeclaration` to the actual parser node from that same `ParsedFile`.
Supply a constructive source-to-construction proof and one focused HIR
verification. Keep values borrowed and occurrence identities artifact-bound.

This is prerequisite evidence for future method/role work. It adds no member
typing, method lookup, dispatch, role identity, implementation compatibility,
candidate eligibility, generated inference constraints, evaluator behavior or
production authority. R85 remains `AWAITING_USER_ADOPTION`; A/B remains
`OPEN 0→0`; R50 remains `NOT_ADOPTED`. Preserve all six effect-hygiene fronts
and the R92 runnable effectful source example in current state. This bounded
method/role step must hand progress back to effect-hygiene work afterward.

## Exact source domain and proof obligations

Use one successfully published `ShadowArtifact` and its own `ParsedFile`.
Field sources are the complete accepted `FieldTail` nodes already enumerated
by `pending_field_tail_sources`, attached to their owning `OperatorChain`.
Role sources are the exact retained `RoleDeclaration` and standalone
`ImplDeclaration` nodes returned by `pending_role_impl_sources`. Preserve
artifact/parse brands, source order, member identity, exact source range,
constructor kind, and lexical occurrence. Malformed, recovered, missing,
duplicate, ambiguous or foreign joins fail closed.

The receiver must be the actual HIR child zero paired with the FieldTail's
actual `AssociationProvenance::Node`, produced by the same association call.
Prove the paired HIR/provenance child invariant from the constructors, including
`structural_continuation`, nested/chained tails and synthetic grouping. A raw
prefix, equal range, spelling, or separately re-associated prefix is not a
receiver proof. Validate the complete selected inventory before publishing
callbacks/results; no partial callback publication on a later join failure.
Do not clone receiver subtrees, retain root-to-occurrence paths, or repeat
whole-tree searches per FieldTail. Preserve distinct association error classes:
`ExactOperatorEnvironment`, `StructuralInvariant`, and `Allocation` must remain
distinguishable at the public/internal seam; map only the bridge's own checked
shape failures to the existing structural error class.

For role/impl nodes, resolve each retained position through the same artifact's
unique source-key map to the actual node from its own parsed tree. Same-spelled
declarations remain distinct occurrences. No semantic `RoleId` or
implementation judgment is constructed.

Expected falsifiers: `.first.second` maps either tail to the wrong child;
grouped/operator-sensitive receiver changes under the join; source identity is
reconstructed from text/range; parse/artifact mismatch is accepted; omitted or
duplicate inventory entry; role/impl order or kind changes; ambiguous identity
gets guessed; error categories collapse; callback runs before full validation;
receiver subtrees are cloned or work becomes per-field whole-tree traversal.

## Preserved R77 evidence

The exact R77 rev1 receipt records one failed command (2 passed, 1 failed): the
test expected source slice `"b"` and observed `" b"` because the authentic
receiver node range includes its leading trivia. No retry occurred. R77 rev2
proposed a versioned test expectation correction and preservation of association
error distinctions but was never activated. Preserve both historical outcomes;
do not import the isolated R77 overlay or rewrite its frozen artifacts. Any new
test must assert the actual constructor-owned range, including trivia, rather
than trimming it. The new implementation must retain error distinctions from
its first revision.

## Exact leases and outputs

Implementation lane (one owner, no overlap):
- `crates/yu-hir/src/shadow.rs`
- `crates/yu-hir/src/tests/shadow_method_role_source.rs`
- `tasks/agent-loop/inbox/20261019-r93-implementation.md`

Constructive proof lane (read-only source inputs; separate outputs):
- `notes/theory/2026-10-19-r93-associated-member-source.md`
- `tasks/agent-loop/inbox/20261019-r93-proof.md`

Primary-only:
- this contract; `tasks/agent-loop/current.json`;
- `tasks/agent-loop/inbox/20261019-r93-compiler-review.md` and
  `tasks/agent-loop/inbox/20261019-r93-spec-review.md` assigned only after both
  producer lanes stop;
- `notes/progress/2026-10-19-r93-closeout.md`.

All other source, design, frozen R76/R77/R85 artifacts, effect examples,
fixtures, expected outputs, semantics and test contracts are read-only.

## Frozen inputs and hashes

Baseline and direct source inputs:
- `crates/yu-hir/src/shadow.rs` —
  `7fce00d94303e83b08d1dbd132b278489a0af85224f751d3e2a00de4b9804593`
- `crates/yu-hir/src/lib.rs` —
  `8f6e2b688418dbdb4e2c551cbd9b7b58c809623d492f2da6f7d29cc64189d8d8`
- `crates/yu-hir/src/module.rs` —
  `c40ebde1755d300c83aafba0a81a85d19ed5200dfc2163ab72c8a3bb08baf29a`
- `crates/yu-hir/src/source_identity.rs` —
  `7f0ba057a28ec8c42d2b08bcbe698ee9b422819bfde8ea43ce184457ea586bb3`
- `crates/yu-syntax/src/full_parse.rs` —
  `24fdbc0f792b748138bcb1b6fded72714dba7f02880f0d395c914fcff546a8d8`
- `crates/yu-syntax/src/operator_table.rs` —
  `369ce0a3a8f5ac39da9da572cfe4fab6f61dd4ca07c554cfcc44aa7051643`
- Existing focused HIR test file —
  `0b1e570845b62237ac8e19b94b29facc42b40b5bcb943676078b8e5c33eed53a`
- `crates/yu-hir/Cargo.toml` —
  `a97f52fc6b9e577f23be4160ecdda9693bec8fe48c626d0e9b7c0e3b0c6fe8d1`

Governing source/design inputs:
- syntax OperatorChain —
  `56cd8495ad0b14cddb4da9fa8088e43647ce4d522ffcab19a08857d2dda1c842`
- syntax FieldTail —
  `0fbbe46d52328b0438c4acc5e2e958380efa45e74ef0020c4762383804d3c253`
- redesign charter —
  `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed`
- top-level inference principles —
  `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`
- R76 projection contract —
  `38142e65fa9a73e9efa073208ec5456da5e9fec22f984baf83b65e3e28b84ff8`
- R76 source proof —
  `04b36001d9ccaaace8930d6304745928b03906f9e4e0a2d041f47223f543b275`
- R76 implementation receipt —
  `680e9b17922a4b46cab9f62a7a5c455fba084754e0356daea868395dc2561029`
- R77 rev1 contract —
  `26735a4d825ecd783856675dadb91b9d97df5f8b71e8f62d1fde06b92d8ce3b1`
- R77 rev1 failed verification receipt —
  `644119a06abfd2b2cc3ddc1448ee5eb948241546dd9d4db4a330441ea242899b`
- R77 rev2 candidate contract (not activated) —
  `cd4ccb504ba4d2882dd6b48c7a2c66e19bdb42f1f932fcd35b1fc6351e87ca0f`

Pins were checked against current bytes or the preserved Git object before
activation. Producers may not expand these inputs or source domain.

## Verification, resources and stop conditions

After both outputs and the implementation freeze, Luna may run exactly once:

`CARGO_BUILD_JOBS=2 timeout 120s cargo test -p yu-hir --lib shadow_method_role_source -- --nocapture`

No retry, fix-after-failure, extra build, or probe under this contract. Tests
support the bounded executable correspondence only; they do not prove the
mathematical constructor invariant or any language semantics.

Fresh compiler/source review and fresh spec review each receive at most 300
seconds after freeze. Integration/reconciliation is 180 seconds. Total cap is
2400 seconds: implementation 900, constructive proof 600, one verification
up to 120, compiler review 300, spec review 300, integration 180; Astra 0.
No prior sprint time is refunded or carried over. Existing unknown identities
and quarantined paths retain their reservations. Stop on a dependency mismatch,
false receiver premise, verification failure, unresolved blocking/major review
finding, runtime uncertainty or budget boundary.

## Handoff and next portfolio step

Each producer must freeze artifact hashes, exact remaining premise, source
constructor-to-consumer route, falsifiers, omitted cases, resource use and
writer-stop evidence. Luna reviews the full diff, assigns fresh independent
reviewers, integrates only explicit paths and updates compact state plus this
closeout. Close only this source prerequisite. After R93, select one bounded
evidence slice from the six effect-hygiene fronts while retaining the R92
runnable source example; continue method/role only at its next authorized
semantic/source gate. Never promote R85 semantics without its adoption decision.
