# R333 — FieldTail descriptor transport

Status: ACTIVE; direct-primary, UNREVIEWED. Baseline: `85f41587e`. This note records a bounded source-to-native correspondence investigation under the unchanged Yulang2 catalog goal. It does not close the original Simple-sub A/B, source/native, receiving, principality, independent-review, or production gates.

## Question

Does an authentic FieldTail descriptor retain all source metadata and its authenticated role requirements through admission, capture/refresh, FreshUse, and active member consumption, even where dedup keys omit some descriptor fields?

The descriptor fields fall into two groups. Source metadata is `source`, `member`, and `role_member_candidates`; `required_roles` is derived during graph capture from authenticated role obligations whose subject has the reciprocal relation to the field receiver. Four Value/Effect ports and Case guard inputs are graph rows and must follow the same FreshUse row image. `owner`, `operator_origin`, and dispatch context track the active path.

## Baseline observations

1. `candidate_source` registers each `LocalSourceExpr` occurrence under its owning `SourceRootId`. A FieldTail/GeneratedFormatSelection arm retains one `DeferredFieldTail` recipe with the exact source node, member, candidate role-member identities, Case guards and four endpoints. Prelude candidate enrichment happens on the recipe before inference admission.
2. Admission looks up `source_owner` by the authentic occurrence and retains a descriptor with `owner == source_owner`, `operator_origin == None`, no dispatch context, and empty `required_roles`. The source metadata is cloned from the final admitted recipe.
3. Capture clones the descriptor, canonicalizes guards and four ports by intrusion representative, seeds these rows, and validates they are present. It derives `required_roles` by scanning source role obligations with the same provider and an authenticated reciprocal role-subject/receiver relation. The root schedule appends where-clause actions after body actions; the definition graph is captured after its source schedule completes.
4. `field_tail_freshuse_row_indexes` maps all four ports to indices in one graph row vector. `activate_source_obligations` clones the whole descriptor, maps guards and ports through that vector, changes only the active owner, and validates every `required_roles` entry against an exact provider/role identity and reciprocal same-FreshUse row relation.
5. `candidate_field_tail_has_source_instance` compares original source, member, role-member candidate list, Case guard source data, exact four-port mapping, role prerequisites, dispatch context, and operator origin where the selected route supports that comparison. Existing tests cover capture/FreshUse layout, imported authenticated role identity, candidate lists, and mutation rejection.
6. Several key/removal sites compare `source_owner`, occurrence, operator origin, dispatch context, guards, and four current representatives, while omitting `source`, `member`, candidate identities, and `required_roles`. Source occurrence uniqueness may justify the first omissions; it cannot by itself justify the capture-derived `required_roles` omission.

## Active proof and falsifier

The remaining source-qualified premise is stability of `required_roles` across records that share the current dedup identity. In particular, a local initializer may retain its active descriptor before the root's trailing where-clause action registers a role prerequisite, while the later definition graph capture derives that role on the same source occurrence and representative rows. If both records reach `execute_candidate_field_tails`, a key that keeps only the earlier descriptor may drop a real requirement.

The decisive falsifier is an authentic source with a declaration where-role and a FieldTail in a local initializer, producing both the pre-clause active record and the post-clause graph template. Compare the complete descriptors immediately before pending coalescing. Synthetic mutation of `SourceFieldTailObligation` is useful for testing a defensive checker, but cannot establish that this source path occurs.

If the source trace confirms the mismatch, the in-scope repair must preserve every authenticated requirement before member selection and keep the exact source/guard/four-port correspondence. A conservative failure is acceptable only where the existing semantics already require withholding; the repair must not add a new source restriction. If no source-valid mismatch is reachable, complete the uniqueness/derivation argument and explain why each omitted key field is congruent.

## Open gates and limits

No parent theorem, source-domain quantifier, A/B claim, accepted semantics, or production gate is narrowed or promoted. The diagnostic Button sequence and R332 evidence are not evidence of successful capture refresh. Tests establish executable correspondences only for their exercised paths; a source proof and fresh review remain separate obligations.

## Evidence log

R333 startup: clean tree at `85f41587e`; `python3 tools/agent_sprint.py check` passed (static tooling evidence only). Exact baseline hashes and leases are pinned in the sprint contract. Source-valid local-initializer/where-role comparison, code repair, focused runtime evidence, independent review, and parent application remain pending.
