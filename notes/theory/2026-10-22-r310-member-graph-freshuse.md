# R310 — Member graph and per-use FreshUse

Status: ACTIVE, solo primary, unreviewed. R149 remains OPEN.
Baseline: `0b48195c2276e1199d21b721f99a5924c8708d43`.
Contract: `tasks/agent-loop/sprints/r310-member-graph-freshuse-20261022.md`.

## Governing evidence reread

Read the converted unified design §§9 stage 4 and 10 and proof companion §§3.2–3.3, 3.6–3.8, 4.5, 7.2–7.4 for this iteration. Stage 4 requires delayed selection with a stability condition and forbids trial typing. The proof companion's FreshUse result applies to records actually in the graph and maps one use at a time; it does not establish member registration or source-to-record correspondence. The original correction remains in force: contravariant `[io]` is `[io,'e]`; a `[state]` residual is permitted.

## R309 result and R310 implementation progress

R309 retained authentic member header/body ownership, a source-owned receiver parameter, candidate Member schedule, role-member source identity, and authenticated receiver endpoint. The unchanged Types sample still reaches `DeferredSelectionUnavailable`. Focused evidence and limitations are recorded in the R309 note.

Current code confirms three concrete boundaries in `candidate_scheme.rs`: `GraphState.graphs` is sized by ordinary definitions; `execute_candidate_graph_plan` iterates definition SCCs; and `capture_candidate_graph_inner` rejects FieldTail groups whose owner lacks `DefinitionRootId`. A Member body can generate nested FieldTail records, but none can be attached to a member graph and carried through the same-use FreshUse route. Executing a shared member template globally would alias rows across uses.

R310 now keeps a separate `member_graphs` map keyed by exact `SourceMemberRootId`; it does not allocate fake definition positions. The source scheduler runs each member body once as a template, captures receiver Value, body-result Value and body-effect rows as explicit roots, and retains any nested FieldTail obligations inside the graph. `capture_candidate_graph_inner` now accepts a same-owner Member obligation bundle while still rejecting Expression owners and mixed-owner bundles. Graph byte accounting includes retained Member graphs.

The focused member-source test now uses a nested `receiver.other` lookup in both the role default and implementation body. `execute_candidate_graph_plan` captures two distinct Member graphs; the test checks each graph's exact owner and that receiver/result/effect interface rows all occur in the graph. `cargo check -p yu-solver --features shadow-apply-candidate` passed. The focused test passed after correcting its assertion to expect a separate body-result endpoint for FieldTail. The first test attempt exposed only a test import error; the next attempt passed. These checks establish graph construction, not per-use FreshUse, method selection or typing.

The next unfinished edge is a field-tail-owned consumer that selects an authenticated member template only from established receiver bounds, copies that graph for this exact use, maps the four outer ports to the copied receiver/result/effect rows, and waits for a stable bound frontier. Until that exists, unchanged Types remains at `DeferredSelectionUnavailable`. Tests cannot close source/native, A/B, principality, termination, or independent-review gates.
