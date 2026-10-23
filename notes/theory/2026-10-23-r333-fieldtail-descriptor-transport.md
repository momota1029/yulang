# R333 — FieldTail descriptor transport

Status: OPEN_CONTINUATION; direct-primary, UNREVIEWED. Baseline: `85f41587e`. This note records a bounded source-to-candidate-solver correspondence investigation under the unchanged Yulang2 catalog goal. It does not close the original Simple-sub A/B, source/native, receiving, principality, independent-review, or production gates.

## Question

Does an authentic FieldTail descriptor retain all source metadata and its authenticated role requirements through admission, capture/refresh, FreshUse, and active member consumption, even where dedup keys omit some descriptor fields?

The descriptor fields fall into two groups. Source metadata is `source`, `member`, and `role_member_candidates`; `required_roles` is derived during graph capture from authenticated role obligations whose subject has the reciprocal relation to the field receiver. Four Value/Effect ports and Case guard inputs are graph rows and must follow the same FreshUse row image. `owner`, `operator_origin`, and dispatch context track the active path.

## Baseline observations

1. `candidate_source` registers each `LocalSourceExpr` occurrence under its owning `SourceRootId`. A FieldTail/GeneratedFormatSelection arm retains one `DeferredFieldTail` recipe with the exact source node, member, candidate role-member identities, Case guards and four endpoints. Prelude candidate enrichment happens on the recipe before inference admission.
2. Admission looks up `source_owner` by the authentic occurrence and retains a descriptor with `owner == source_owner`, `operator_origin == None`, no dispatch context, and empty `required_roles`. The source metadata is cloned from the final admitted recipe.
3. Capture clones the descriptor, canonicalizes guards and four ports by intrusion representative, seeds these rows, and validates they are present. It derives `required_roles` by scanning source role obligations with the same provider and an authenticated reciprocal role-subject/receiver relation. The root schedule appends where-clause actions after body actions; the definition graph is captured after its source schedule completes.
4. `field_tail_freshuse_row_indexes` maps all four ports to indices in one graph row vector. `activate_source_obligations` clones the whole descriptor, maps guards and ports through that vector, changes only the active owner, and validates every `required_roles` entry against an exact provider/role identity and reciprocal same-FreshUse row relation.
5. `candidate_field_tail_has_source_instance` compares original source, member, role-member candidate list, Case guard source data, exact four-port mapping, role prerequisites, dispatch context, and operator origin where the selected route supports that comparison. Existing tests cover capture/FreshUse layout, imported authenticated role identity, candidate lists, and mutation rejection.
6. Several key/removal sites compare `source_owner`, occurrence, operator origin, dispatch context, guards, and four current representatives, while omitting `source`, `member`, candidate identities, and `required_roles`. Source occurrence uniqueness justifies using those fields as the core key only when a same-key collision separately checks immutable metadata. It cannot justify omitting capture-derived `required_roles`; those are a mergeable set.

## Active proof and falsifier

The source-valid mismatch is confirmed. The regression builds an imported `Display` role with an `int` implementation, then compiles a consumer definition with `where 'a: Display`, a local initializer `my shown = value.show`, and a concrete `display 1` use. Before pending coalescing, the local capture has `required_roles=[]`, while the completed definition graph has `[Display]` for the same authentic HIR occurrence and identical four current ports. The pre-fix focused assertion observed that refresh left the local descriptor empty.

The source order explains the mismatch: body actions capture the local initializer before the trailing where-clause action registers its role obligation. Definition capture runs after the full source schedule and derives `[Display]` from the exact reciprocal role-subject/receiver pair. Occurrence identity proves the immutable source metadata corresponds; it does not prove the role set is stable.

## Repair and descriptor audit

The repair merges distinct `required_roles` at pending-template coalescing, retained local/global state, and definition/local refresh. It compares `source`, `member`, and `role_member_candidates` separately for every same-core-key match and returns `ReceiptMismatch` if those immutable fields conflict. The equality used by `has_source_field_tail_obligation` treats the prerequisite vector as a set.

Definition refresh merges role sets into an existing same-key template before recapture. Local refresh consults the owning source graph selected by `SourceRootId` (definition, member, or expression provider). It joins by source owner, occurrence, operator origin, immutable metadata, and ordered guard source IDs; verifies the provider descriptor's four port keys are present in that graph; unions the authenticated role identities; and imports only role records whose subjects have the reciprocal relation to a matched field receiver in that same graph. A local residual can be a later FreshUse image with different row keys, so source identity carries the role set into the reusable capture while the provider graph supplies the source-level pair. This does not create a bound or authorize activation. Local activation still requires the reciprocal relation inside the local FreshUse graph, or (for a definition provider) the exact provider pair with both rows shared and unchanged by that FreshUse. Missing source rows, role pairs, or local capture fields fail closed.

Key audit:

- Pending coalescing and retained state use `source_owner`, occurrence, operator origin, dispatch context, source guards/current inputs, and all four current ports as the core identity. Source metadata is checked on collision; role sets are unioned.
- Definition refresh and residual removal use the normalized core identity plus immutable source metadata; `required_roles` is intentionally absent from a removal key because removal consumes the complete already-merged record. Local prerequisite refresh uses the exact source occurrence and guard-source sequence, then preserves the four provider ports and reciprocal relation inside the provider graph while transporting role identities across a potentially fresh local row image.
- Active consumption removes the item only after pending coalescing and retention validate metadata and merge role sets. FreshUse maps all four ports and guard inputs through one graph row map.
- `candidate_field_tail_has_source_instance` already requires source, member, candidate identities, role set, guards, origin/context where applicable, and all four ports. Active route/template joins now also check immutable metadata and role-set equality; the source-qualified role-frontier join checks metadata, guards and origin.

The end-to-end fixture selects the imported Display member for `display 1` and retains a member FreshUse for the exact source occurrence. After residual refresh, the local reusable descriptor has `[Display]`. A recaptured local graph then carries the exact role record and FieldTail through one FreshUse; the fixture confirms the receiver and role subject are nonlocal shared rows and retain their exact row keys before local activation succeeds.

## Open gates and limits

No parent theorem, source-domain quantifier, A/B claim, accepted semantics, or production gate is narrowed or promoted. The diagnostic Button sequence and R332 evidence are not evidence of successful capture refresh. Tests establish executable correspondences only for their exercised paths; a source proof and fresh review remain separate obligations.

## Evidence log

R333 startup: clean tree at `85f41587e`; `python3 tools/agent_sprint.py check` passed (static tooling evidence only). Exact baseline hashes and leases are pinned in the sprint contract.

Source-valid repair verification passed:

- `cargo test -p yu-solver --features shadow-apply-candidate --lib local_initializer_fieldtail_keeps_late_where_role_requirement -- --nocapture` — 1 passed; authentic provider/consumer HIR, late role comparison, actual Display member selection, member FreshUse, local residual refresh, and local FreshUse activation.
- `cargo test -p yu-solver --features shadow-apply-candidate --lib declaration_where_subject_uses_provider_row_and_same_freshuse_image` — 1 passed.
- `cargo test -p yu-solver --features shadow-apply-candidate --lib deferred_field_tail_rows_survive_capture_and_same_freshuse_map` — 1 passed.
- `cargo test -p yu-solver --features shadow-apply-candidate --lib deferred_field_tail_keeps_authenticated_role_member_candidates` — 1 passed.
- `cargo test -p yu-solver --features shadow-apply-candidate --lib field_source_instances_require_original_metadata_and_all_four_rows` — 1 passed.
- `cargo test -p yu-playground` — passed through the ordinary package path, including the scheduled local-initializer host-write regression and CLI integration groups.

The runs report existing compiler warnings. The R333 evidence is direct-primary and UNREVIEWED. The original Yulang2 catalog, source/native, Simple-sub A/B, receiving, principality, independent review and production gates remain OPEN.
