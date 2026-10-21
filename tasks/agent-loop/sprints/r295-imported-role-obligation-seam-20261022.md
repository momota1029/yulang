# Sprint R295 — locate the imported role obligation seam

Status: solo source-to-solver boundary checkpoint; R149 stays OPEN.
Branch/baseline: `research/simple-sub-intrusion` at `8dc8fbf4b`.
Parent: unchanged Yulang2 Types and Console samples under R149.

## Outcome

Trace the exact route needed to take the pinned `say(value: 'a)` declaration,
its `where 'a: Display` prerequisite, and the imported `say` use into one
accepted candidate type scheme. Preserve public export identity, the same
provider, type-variable sharing, and the user's `[io]` open-row correction.

## Findings

- The ordinary provider HIR now owns the exact pinned `say` binding and its
  same-parse `where 'a: Display` source carrier (R294).
- `LocalSourceWhereClause` retains source keys, spans and text for subject and
  role, but does not resolve either name to a type-variable or role identity.
- `candidate_source::preflight` rejects every nonempty `where_clauses` list.
  The focused solver test confirms this fail-closed behavior.
- `candidate_source::preflight` also rejects every `LocalSourceResolution::Imported`;
  the source collection path independently returns unavailable for Imported
  names. `FieldTail` has no candidate consumer and explicitly awaits the
  authentic imported role/field resolver.
- `CandidateInference::solve` accepts one HIR. Its export API requires a
  definition root owned by that same solved HIR. The source export/role indexes
  added in R291-R294 authenticate declarations but do not provide a shared
  inference session or imported scheme consumer.
- Annotation variables already have a solver identity keyed by
  `(AnnotationScope, spelling)`. A where-clause consumer must join to that same
  identity and carry the role obligation through generalization and each fresh
  use. Resolving the spelling independently would be unsound.

These gaps are jointly on the Types/Console critical path: the Console sample
imports `println` and `say`; the Types sample imports and uses `Display` for a
tuple. No intrinsic or chosen method may replace those source routes.

## Evidence and checks

- `cargo test -p yu-solver --features shadow-apply-candidate candidate_preflight_does_not_drop_retained_declaration_prerequisites -- --nocapture` — passed; confirms declaration prerequisite is retained and candidate preflight returns `Unsupported`.
- `cargo test -p yu-playground --lib authenticated_implicit_prelude_names_keep_source_identity_and_local_shadowing -- --nocapture` — passed; confirms authentic imported `SourceExportId` routing and local shadowing.
- `cargo test -p yu-playground --lib pinned_public_export_route_retains_source_owned_edges_and_names -- --nocapture` — passed; confirms exact `say` provider owner and carrier from R294.
- The exact R149 samples remain 142 and 92 bytes; no source fixture was rewritten.

## Boundary and next action

No candidate inference, runtime behavior, theorem or production gate is closed.
The next implementation packet must establish a single source-owned module
world: imported value schemes, role prerequisites and deferred member selection
must retain their declaration identities and share type/effect/fresh-use maps
with the receiving source. Start by designing and implementing the identity-
bound role-obligation record and its Capture/FreshUse transport alongside the
provider-scheme import edge; do not add a detached textual typeclass solver.

No subagents were used under the user's explicit solo-work instruction. This is
a serial primary checkpoint; no unknown or quarantined leases were reclaimed.
