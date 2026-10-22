# R322 — exact member selection and FreshUse

## Parent obligation

The user goal remains unchanged Yulang2 sample inference/execution with proofs. R321 reached a same-session `Display.say` MemberGraph and retained the consumer `pair.say` FieldTail, but did not select an implementation or infer the sample successfully. R322 follows that seam without changing sample text, output, accepted semantics, quantifiers, or source domain.

## Established inputs

R321 captured one exact source member graph for the pinned `Display.say`, including receiver/result/effect roots. Its nested `show` FieldTail is represented in the graph's FreshUse row-index layout. The unchanged consumer's `pair.say` remains deferred in the same solver session.

The receiver shape readback for Types is `(Int, Str)`. The pinned source inventory structurally matches one exact tuple `Display` implementation and substitutes `a=int`, `b=str`. Its source where clauses are exactly `Display int` and `Display str`, each with exact role identity. These readbacks do not themselves select a method, discharge evidence, establish later-bound stability, or prove source/native correspondence.

Effect annotation interpretation is fixed: contravariant `[io]` denotes `[io,'e]`; a `[state]` effect argument is permitted. Any selection/application work must preserve this interpretation.

## Question and bounded claim

Can the solver connect exact source-owned member selection to one FreshUse of the captured MemberGraph, consistently map receiver/result/effect rows, and transport the selected implementation's complete where obligations into the consumer's candidate constraints? For the unchanged tuple receiver, the only applicable source identity must be the authenticated tuple Display implementation with both exact prerequisites represented. If the existing source/native producers cannot establish a premise, record the exact obstruction instead of inferring it from a readback.

## Evidence still required

- Actual candidate-session path from `FieldTail` to exact member and implementation source identities.
- Correct uniqueness/applicability condition, accounting for complete inventory and reachable negative bounds.
- Same shared row map for the member graph's receiver, result, effect, and nested FieldTail rows.
- Exact where-prerequisite evidence through existing role/implementation source identities.
- Unchanged Types successful inference, or a precise producer/consumer obstruction.
- Independent review and source/native A/B remain absent; no theorem or production gate can close from solo code/tests.

## Result: precise missing consumer

The source producer retains `DeferredFieldTail` with exact role-member candidates and receiver/value/effect rows. Captured graphs retain these obligations, and `field_tail_freshuse_row_indexes` maps their four rows to the graph's shared FreshUse row vector. `prepare_candidate_fresh_use` stores those indices in `FreshUse.source_field_tail_obligation_rows`.

Repository-wide symbol search shows that this FreshUse field has no solver consumer: it is used for retained-byte accounting and observation/layout reporting only. It does not produce a fresh implementation or role-default graph, connect the fresh receiver/result/effect rows, or requeue nested FieldTails. Separately, `resolve_source_role_implementation_members` returns exact override member identities but documents that it does not compare targets, establish applicability, or select. `retain_role_implementation_members` only retains that metadata. Candidate execution therefore leaves the original obligation pending and `execute` reports `DeferredSelectionUnavailable`.

The exact next construction is source projection of authenticated implementation override members into candidate member templates, followed by a FieldTail consumer that checks uniqueness, complete source inventory, all exact where prerequisites, and positive/negative receiver bounds before one FreshUse and interface connection. This does not establish source/native A/B, later-bound stability, or theorem closure. The unchanged Types sample, Console, R149, all-samples goal, and production remain OPEN.

R322 was a solo read-only source trace. No independent review was available under the user's no-subagent instruction. No new test was added or run; existing R321 receipts remain as previously recorded and validate capture only.
