# R276 — pinned role source inventory

Status: provisional source identity bridge; primary-only and unreviewed. R149 Types/Console, imports, role selection, sample execution and proof remain OPEN.

## Parent application

The exact unchanged Types sample now reaches a parse-owned `FieldTail` for `pair.say`, while the solver correctly withholds candidate inference until role selection is available. The pinned bundle contains exact `std::core::fmt` source whose `Display` role defines `say` and whose two-element tuple implementation defines `show`. The current `pinned_stdlib` helper validates all 40 source blobs and module closure, but it returns source texts without pairing role declaration positions with a stable Y3 `ModuleIdentity`.

This step adds that source identity pairing. It does not treat `say` as a built-in or infer which role implementation applies.

## Parser boundary discovered

Parsing the exact pinned `lib/std/core/fmt.yu` with the playground syntax environment yields syntax diagnostics. `ShadowArtifact::from_parsed` rejects that snapshot, so no HIR artifact or complete parser-owned declaration positions can be claimed. The focused test retains the exact `ParsedFile`, its diagnostic count, and available `RoleDeclaration` / `ImplDeclaration` node anchors, paired with the source-root `ModuleIdentity`. It separately checks the complete role and tuple implementation text against the same bundle entry whose Git blob is asserted. Those text checks are byte-source evidence, not parser judgments about declaration bodies.

The test observes 50 syntax diagnostics in the current parser. The declaration anchors and exact bundle bytes establish where the next parser compatibility or role-resolution work must begin; they do not authorize solving or selecting an implementation.

## Verification

Focused `cargo test -p yu-playground --lib pinned_fmt_role_and_tuple_impl_keep_exact_module_and_parse_positions -- --nocapture` passes. The direct-dependent playground compile, sprint static check and diff check remain pending. Exact unchanged Types still fails closed at candidate inference; Console, imported role selection, sample output, proof and production remain OPEN.
