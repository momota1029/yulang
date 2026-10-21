# R303 — source-backed role member typing for the unchanged Types sample

Status: RUNNING, solo primary, unreviewed. Parent R149 unchanged Types+Console goal remains OPEN.
Baseline: `6afa11887`; contract: `tasks/agent-loop/sprints/r303-role-member-candidate-typing-20261022.md`.

## Governing design and proof material read

Re-read unified design §§4.3–4.5, 5.1, 6, 9–10 and proof companion §§3.1–3.6, 4.5, 7.1–7.5 for this iteration. The effect annotation rule remains the user's correction: contravariant `[io]` denotes `[io,'e]`, so passing `[state]` is not itself a violation.

## Starting evidence

R302 is checkpointed and pushed. FieldTail identity and its receiver/result Value+Effect rows survive Capture and one FreshUse map; authenticated role/member IDs attach to the deferred FieldTail; the unchanged Types receiver has an observed ordered `(int,str)` lower bound; source inventory has exactly one ordered-pair Display target among 14 implementations. These checks establish candidate-bound and source-inventory observations only.

HIR currently carries role and implementation declarations as nonshipping sidecars. Their member IDs preserve module and declaration `SourceNodeKey`, while role/impl bodies are retained as source snippets. Ordinary HIR items are only Binding, Expression and Error; source roots and candidate scheduling are built around actual definitions/expressions. The candidate FieldTail path therefore has authenticated IDs but no inference root for the original role/impl member body. Creating a fake top-level definition would break source ownership and is not an acceptable bridge.

## R303 target and falsifiers

Carry an original role/implementation member body into candidate inference with its authentic member ID, source node and module owner. Check that malformed/recovered or missing source fails closed, that same-spelled members from a different role cannot cross-route, and that target matching is delayed until receiver bounds settle. Preserve tuple element order and exact row identities. Advance the unchanged Types route through body inference; runtime execution is a stretch only if body formation, selection and typing have landed without weakening semantics.

The proof lane traces source constructors, source keys, new HIR/candidate roots, generated constraints, propagation and body consumer. The implementation and proof work are both solo and unreviewed. Passing tests, exact candidate inventories and selected source matches do not close the source/native theorem, Console, A/B, or production gates.

## Expected application

If the source-to-candidate bridge holds, apply it only to the original Types sample's `Display.a.say` prerequisite and ordered tuple `show` candidate, then continue toward ordinary execution. Keep Console and all original R149 quantifiers open. If the bridge cannot be represented without manufacturing a binding or losing source identity, preserve that as the exact obstruction and choose a different source-root representation before selection code.

## R303 source lookup slice

Added `HirModule::source_role_member` and `source_implementation_member`. Each lookup checks the module owner, exact enclosing declaration identity and exact member identity. It returns no member when declaration/body/member recovery is present, when an implementation body is absent, or when a member ID has been transplanted under another implementation. A where-clause entry has no member identity and cannot be returned as a member. The API is explicitly source ownership only; it does not resolve roles, type bodies, select implementations or authorize dispatch.

The role identity test now has two distinct `Pick` declarations with the same `value` member spelling and verifies each ID resolves only to its own member. The implementation identity test verifies the exact member resolves and a transplanted declaration key under another implementation ID does not. Both focused `yu-hir` tests pass. The first run exposed an old expected source slice after changing the fixture; the expected text was corrected and the rerun passed.

This closes only the lookup sub-obligation. Original method body syntax is still a retained source snippet/identity, not a candidate definition-use root. Candidate constraint generation, receiver-bound selection, body typing, unchanged Types execution, Console and source/native proof remain OPEN.

## Original syntax recovery bridge

A direct attempt to retain Rowan `SyntaxNode` values in the role/implementation sidecars failed the existing `HirModule: Send + Sync` compile-time contract, so that representation was discarded before commit. The replacement stores a fallibly constructed child-index path for each member under the original parse root and retains the immutable `ParsedFile` green tree on local-source HIR. The new `source_role_member_node` and `source_implementation_member_node` APIs reconstruct an owned node from that tree only after exact member lookup, parse-brand ownership, and kind/range/text checks. Impl where clauses carry no member path. No source is reparsed or rewritten, and no syntax node is held inside `HirModule`.

Evidence: both focused member tests pass with exact range/text/kind/source-key assertions; all 155 `yu-hir` library tests pass, including the Send+Sync trait-surface check; `cargo check -p yu-solver --features shadow-apply-candidate` passes. Existing unrelated warnings remain. This provides a way to hand the original member syntax to an HIR-side source constructor, but no candidate graph consumes it yet. Method-body lowering, role/impl candidate roots, selection after settled bounds, sample execution and source/native proof remain OPEN.
