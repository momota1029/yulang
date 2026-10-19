# Sprint method-role-source-correspondence-20261019-r77 — method receiver and role source correspondence

Status: CANDIDATE — not active until Luna validates the exact contract and records activation
Branch / baseline: `research/simple-sub-intrusion` / `af3ccf2d63ba7f87e0359e183568db548ea53307`
Contract revision: 1

## Original outcome and success evidence

Original outcome: advance the unchanged Simple-sub inference/evaluator and A/B obligations through a source-to-HIR prerequisite that covers method syntax and role declarations with constructive correspondence evidence. Preserve all original claims, quantifiers, source domain, and accepted semantics. Parent/evaluator/A-B remain OPEN 0→0; R50 remains NOT_ADOPTED.

R76 established exact parser occurrence inventory for FieldTail, RoleDeclaration and standalone ImplDeclaration. R77 must connect these retained occurrences to the structures actually produced by HIR association/parsing, without making an inference or dispatch judgment.

Success predicates:
1. For an explicit associated root and its nested closure (or disjoint outermost roots for a whole artifact, if that route is proved safe), each selected FieldTail/member has exactly one join to its constructor-produced association node and its actual receiver child zero; no occurrence is omitted or duplicated.
2. Each R76 RoleDeclaration/standalone ImplDeclaration source identity is joined exactly to its original branded syntax node from the same parsed artifact, with source order and constructor kind preserved. State explicitly which role/impl shapes are outside this fixed source domain.
3. A constructive proof establishes these joins from authentic source keys/brands and constructor provenance, and gives a falsifier for wrong receiver, wrong artifact, duplicate/omitted source, or shape mismatch.
4. Implementation retains borrowed/constant-size correspondence handles; no per-field receiver subtree clones, no stored root-to-occurrence paths, no reassociation of raw prefixes. Target O(P+A+F+R) expected work and indexing/storage beyond the existing association result, where P is raw parser nodes visited, A is visited association/provenance nodes, F selected field tails and R selected role/impl occurrences. Do not hide repeated whole-tree searches behind constant-size handles. Do not claim the existing association producer itself is linear unless separately proved.
5. Fresh compiler and spec reviews find no blocking/major source or contract issue; one contracted bounded HIR verification either passes or records the exact blocker. This evidence does not count as theorem closure by itself.

Before/after: R76 provides source inventory only; R77 may establish an exact identity bridge from those occurrences to parser/HIR-owned nodes. It must not claim typing, dispatch, role selection, solver constraints, evaluator correspondence, parent closure, or A/B progress unless separate authorized evidence actually changes those gates.

## Fixed scope and source authority

Read-only authority and dependencies (pin exact bytes in activation receipt):
- `crates/yu-hir/src/lib.rs` SHA-256 `8f6e2b688418dbdb4e2c551cbd9b7b58c809623d492f2da6f7d29cc64189d8d8`
- `crates/yu-hir/src/shadow.rs` SHA-256 `7fce00d94303e83b08d1dbd132b278489a0af85224f751d3e2a00de4b9804593`
- `crates/yu-hir/src/source_identity.rs` SHA-256 `7f0ba057a28ec8c42d2b08bcbe698ee9b422819bfde8ea43ce184457ea586bb3`
- `crates/yu-hir/Cargo.toml` SHA-256 `a97f52fc6b9e577f23be4160ecdda9693bec8fe48c626d0e9b7c0e3b0c6fe8d1`
- `crates/yu-syntax/src/full_parse.rs` SHA-256 `24fdbc0f792b748138bcb1b6fded72714dba7f02880f0d395c914fcff546a8d8`
- `crates/yu-syntax/src/operator_table.rs` SHA-256 `369ce0a3a8f5ac39da9da572cfe4fab6f61dd4ca07c554848cfcc44aa7051643`
- syntax reference OperatorChain authority `syntax-reference/en/src/expressions/operator-chain.md` SHA-256 `56cd8495ad0b14cddb4da9fa8088e43647ce4d522ffcab19a08857d2dda1c842`
- syntax reference FieldTail `syntax-reference/en/src/expressions/call-field-path-tails.md` SHA-256 `0fbbe46d52328b0438c4acc5e2e958380efa45e74ef0020c4762383804d3c253`
- redesign charter SHA-256 `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed`
- top-level inference principles `notes/design/2026-10-11-yulang-inference-top-level-principles.md` SHA-256 `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`
- R76 frozen contract SHA-256 `38142e65fa9a73e9efa073208ec5456da5e9fec22f984baf83b65e3e28b84ff8`
- R76 proof SHA-256 `04b36001d9ccaaace8930d6304745928b03906f9e4e0a2d041f47223f543b275`
- R76 implementation receipt SHA-256 `680e9b17922a4b46cab9f62a7a5c455fba084754e0356daea868395dc2561029`

Use the actual retained parse/operator environment and artifact-owned ParsedFile. Authenticate joins with the artifact's own source keys/brands and exact constructor provenance. Text/range coincidence is insufficient; ambiguous synthetic zero-width keys must fail closed. Preserve existing association errors and never rebuild the operator environment.

## Two continuing lanes

Proof owner: Sol/high, constructive source/native correspondence proof. One paired expression/provenance traversal; establish exact multiplicity and identity for field receiver joins, then establish role/standalone-impl occurrence joins to original parser nodes. Apply both results back to method/role source prerequisites. At first unsupported identity or shape premise, report the precise missing constructor/map law and stop that subclaim; continue the independent subclaim if its inputs remain sound.

Implementation owner: Luna/high. Add a borrowed association/provenance correspondence API for the fixed FieldTail domain, plus exact role/impl node resolution from the same artifact-owned ParsedFile. Do not add semantic field/method classification, receiver typing, RoleId, impl applicability, candidate selection, generated constraints or dispatch. After artifacts freeze, run exactly one command: `CARGO_BUILD_JOBS=2 timeout 120s cargo test -p yu-hir --lib shadow_member_receiver_association -- --nocapture`. On timeout, compile error, or failed assertion, stop this contract's verification; no retry is authorized here.

Fresh independent compiler review and fresh independent spec review are separate from authors and proof producer. Review frozen bytes and one bounded delta if needed.

Falsifiers: chained tails map to the wrong receiver; grouped/application/dynamic-operator input changes association; a source occurrence maps across artifacts; provenance shape does not match expression shape; selected constructor is missing or duplicated; role/impl source order or kind changes; unequal identities collapse; per-occurrence clones or repeated prefix association make the bound false.

## Non-goals and boundaries

No effect-storage follow-up is admitted by this contract. No method inference, method lookup, role identity resolution, role/impl compatibility, dispatch, solver rule, semantic approval, evaluator path, production change, or R50 adoption. R76's source inventory and R77's correspondence are prerequisites only. Existing approved semantic rules remain usable under Luna's authority; any genuinely new semantic choice requires its own approval.

## Permissions, resources and exact leases

Write leases, only after activation:
- Luna: `crates/yu-hir/src/lib.rs`, `crates/yu-hir/src/shadow.rs`, `crates/yu-hir/src/tests/shadow_member_receiver_association.rs`, `notes/progress/2026-10-19-r77-member-role-implementation.md`, `tasks/agent-loop/inbox/20261019-r77-implementation.md`, this primary-owned contract and `tasks/agent-loop/current.json`.
- Sol proof: `notes/theory/2026-10-19-r77-member-role-correspondence.md`, `tasks/agent-loop/inbox/20261019-r77-proof.md`.
- Fresh compiler reviewer: `tasks/agent-loop/inbox/20261019-r77-compiler-review.md` only.
- Fresh spec reviewer: `tasks/agent-loop/inbox/20261019-r77-spec-review.md` only.

No solver files, R74/R75 frozen paths, R76 proof/test/evidence paths, or other roles. R76 is integrated at `af3ccf2d63ba7f87e0359e183568db548ea53307`; its frozen source snapshot remains preserved as the baseline, while Luna may write the two explicit source files as new R77 revisions. All dependency bytes must be revalidated against activation receipt. R75's preserved dirty tree remains excluded and untouched.

Proposed active-work cap 2400 seconds total: Luna implementation and integration 900 seconds including one <=120 second HIR-only command; Sol proof 600; fresh compiler 300; fresh spec 300; integration reserve 300; Astra 0. No R75/R76 time carryover. At most one heavy process, one verification owner, and no new worker until exact leases and live capacity are reconciled. Stop at first contract failure, exhausted bound, unknown writer, user STOP, or source authority mismatch.

## Frozen seams and handoff

Freeze proof and implementation snapshots, exact dependency hashes, source constructors, multiplicity arguments, complexity/storage argument, omissions, and actual verification receipt before review. Compiler review covers source identity joins, borrowed lifetime/clone behavior, error handling and adversarial receiver cases. Spec review covers exact source-domain, semantic boundary, dependency pins and theorem-status language. Close every blocking/major finding with a frozen delta review before acceptance.

Close only this bounded source-to-HIR correspondence prerequisite. Original whole-inference/evaluator and Simple-sub A/B remain OPEN 0→0, R50 NOT_ADOPTED, and production authority unchanged. Retain method and role as named next areas of breadth after this bridge; do not let effect-storage displace them without a separately justified parent-critical-path case.

Luna's exact closeout path is `notes/progress/2026-10-19-r77-closeout.md`. Consult the dispatcher at activation and sprint end, or on material counterexample, dependency/lease change, resource boundary or cross-lane seam. Luna alone integrates and commits explicit reviewed paths.
