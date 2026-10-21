# R302 — unchanged Yulang2 sample route through deferred FieldTail

Status: RUNNING, solo primary; no independent review. R149 acceptance and theorem remain OPEN.

## Governing sources read at sprint entry

Read `docs/yulang-unified-design-and-proof-plan-ja.md` §§4.3–4.5, 5.1, 6, 9–10 and `docs/yulang-proof-companion-ja.md` §§3.1–3.6, 4.5, 7.1–7.5. Capture/FreshUse correspondence applies only to semantic records actually included in the graph. Newly registered FieldTail metadata needs its own source-to-record correspondence and then an application of the existing row-map result; candidate collection or a test pass is not source typing or proof closure.

## Frozen baseline and before evidence

Baseline: `d47629717`. R301 converted the immediate FieldTail collection rejection into `CandidateRelation::DeferredFieldTail`, retaining the parse-owned source key, member spelling, receiver/result value endpoints and receiver/result effect endpoints. It contributes no type fact and fails closed at `Solve(DeferredSelectionUnavailable)`. The unchanged Types focused test passes at that boundary. The relation remains in the batch; it is not yet a `Graph` prerequisite or FreshUse mapping. Console remains before imported-name candidate collection. Neither sample executes.

R302 preserves the unchanged exact templates and pinned source identities. No method is selected by spelling, no member type is assumed, and no unresolved obligation may escape as a successful candidate result.

## Next implementation seam

Register each deferred relation under its exact source owner and occurrence; associate the imported exact role/member identity from the pinned role index. Include its receiver/result Value and Effect rows in provider Capture. Reconstruct all row references with the same `FreshUse.rows` map, preserving source/member identity unchanged. Keep unresolved obligations private and fail closed. Then determine the route by receiver bounds in the common session, resolve a unique role implementation, and discharge the method's nested `show` obligation on the same receiver before accepting the method application.

Proof work must identify the source constructor, generated obligation, all rows and source identities, graph capture inclusion, one-use remap and actual consumer. Existing proof companion §3.6 justifies the mapping operation once its assumptions hold; it does not establish this FieldTail registration or discharge. Falsifier: drop/alias any receiver/result/effect row across Capture/FreshUse, accept missing/ambiguous/stale role members, or accept a method while `show` remains unresolved.

The original R149 goal remains both unchanged CLI samples, public types/output, ordered execution and applicable proof. Console imports/host operation, whole-module execution, exact output, independent review and production remain open.

## Captured FieldTail row bundle

Candidate admission now registers each deferred FieldTail by exact `SourceRootId` and occurrence. Its obligation retains the parse-owned source key/member spelling and four typed rows: receiver Value, receiver Effect, result Value, result Effect. Before Capture, rows are canonicalized in the current intrusion state. The provider Graph interns all four and validates their presence. `FreshUse` stores one obligation ordinal with four graph-row indexes; all four reconstructed identities are read through the same `FreshUse.rows` vector. The source/member identity remains attached to the captured Graph. Pending obligations still force `DeferredSelectionUnavailable` at candidate finalization.

The solver test `deferred_field_tail_rows_survive_capture_and_same_freshuse_map` passes with `shadow-apply-candidate`, including checked resource-byte refresh and local-versus-shared row identity behavior. The unchanged Types and Console focused Playground tests both pass at their current fail-closed boundaries. Types now passes candidate collection, executes capture/session processing and remains rejected because role selection is unresolved; Console still fails at imported-name preflight. Neither source executes.

This does not yet authenticate a role/member candidate from import identities, select a type-directed implementation, discharge nested `show`, or connect the relation to a selected method application. The source-to-obligation registration has executable coverage but no independent source/native proof. The accepted-sample and parent theorem gates remain OPEN.

The transport test uses the generic provider source `my select x = x.show`, so it exercises a FieldTail inside a captured definition rather than only the top-level sample expression. It confirms source occurrence/key and spelling survive into `Graph`, all four rows are present after Capture, and each local row's FreshUse image is distinct while shared anchors remain fixed. This is a bounded algebraic bridge test; the ordinary sample tests still stop before method selection.
