# R296 — source role obligation through Capture/FreshUse

Status: bounded implementation slice complete; parent gate OPEN.

## Construction and result

A declaration `where 'a: Display` now enters the candidate source schedule as a source-owned action after the declaration annotation has created its named variable rows. The consumer accepts only an exact subject spelling already interned under that declaration's `AnnotationScope`; it reuses the existing row and records the where-clause, subject, and role `SourceNodeKey`s. The role spelling remains unresolved data and cannot select an implementation.

The candidate graph state retains prerequisites by exact `DefinitionRootId`. Provider Capture clones them into the provider `Graph` and explicitly interns each subject value row, because an obligation subject can be absent from the ordinary type-reachable shape. Capture then checks that the subject row is in the graph's retained row list. After staged provider graphs publish, the temporary per-root table is released so the Graph is the sole retained owner. `FreshUse` records `(obligation ordinal, graph row index)` and carries it into `RetainedFreshUseMaps`; the associated subject image is read from the same existing FreshUse row vector used by the provider's other rows. No separate freshening or identity map was added.

Retained allocation accounting includes the state map, its per-provider vectors, each graph copy, and role spelling bytes. A test compares incremental retained bytes with the existing full recount.

Candidate preflight still rejects every nonempty `where` list. R296 has not resolved the spelling to `SourceRoleId`, discharged a role obligation, admitted imported provider schemes into one inference world, or selected a type-directed implementation. Keeping preflight closed is required until those consumers exist.

## Evidence

- `cargo test -p yu-solver --lib --features shadow-apply-candidate candidate_scheme::authentic_demand_capture_tests::declaration_where_subject_uses_provider_row_and_same_freshuse_image -- --exact` — passed.
- `cargo test -p yu-solver --lib --features shadow-apply-candidate candidate_source::where_clause_source_tests::candidate_preflight_does_not_drop_retained_declaration_prerequisites -- --exact` — passed.
- `cargo check -p yu-playground` — passed.
- `python3 tools/agent_sprint.py check` — passed; static evidence only.
- `python3 -m unittest discover -s tools -p 'test_agent_sprint.py'` — 57 passed.
- `git diff --check` — passed.

The focused Capture/FreshUse test directly executes the internal candidate source schedule because public candidate preflight still rejects where clauses. It does not show ordinary Y2 inference or runtime behavior. No independent review ran under the user's solo-work instruction.

## Exact remaining seam

Resolve each role source through the authenticated source import/role index into an exact `SourceRoleId`, attach the obligation to its provider scheme and same FreshUse row, and add the real type-directed consumer before loosening preflight. Then import the provider scheme into the importing inference world. R149 Types/Console, runtime output, source/native correspondence, and proof closure remain OPEN.
