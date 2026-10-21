# R302 — unchanged Yulang2 sample route through deferred FieldTail

Status: CHECKPOINTED at a cross-layer integration seam, solo primary; no independent review. R149 acceptance and theorem remain OPEN.

## Governing sources read at sprint entry

Read `docs/yulang-unified-design-and-proof-plan-ja.md` §§4.3–4.5, 5.1, 6, 9–10 and `docs/yulang-proof-companion-ja.md` §§3.1–3.6, 4.5, 7.1–7.5. Capture/FreshUse correspondence applies only to semantic records actually included in the graph. Newly registered FieldTail metadata needs its own source-to-record correspondence and then an application of the existing row-map result; candidate collection or a test pass is not source typing or proof closure.

## Frozen baseline and before evidence

R302 entry baseline: `d47629717`. R301 converted the immediate FieldTail collection rejection into `CandidateRelation::DeferredFieldTail`, retaining the parse-owned source key, member spelling, receiver/result value endpoints and receiver/result effect endpoints. It contributes no type fact and fails closed at `Solve(DeferredSelectionUnavailable)`. The unchanged Types focused test passes at that boundary. At entry to R302, the relation remained in the batch; it was not yet a `Graph` prerequisite or FreshUse mapping. Console remains before imported-name candidate collection. Neither sample executes.

R302 preserves the unchanged exact templates and pinned source identities. No method is selected by spelling, no member type is assumed, and no unresolved obligation may escape as a successful candidate result.

## Next implementation seam

The exact owner/occurrence, receiver/result Value and Effect rows, one FreshUse row map, and authenticated imported role/member candidates now survive into the deferred obligation. Next determine the route by receiver bounds in the common session, resolve the unique role implementation, and discharge the method's nested `show` obligation on the same receiver before accepting the method application.

Proof work must identify the source constructor, generated obligation, all rows and source identities, graph capture inclusion, one-use remap and actual consumer. Existing proof companion §3.6 justifies the mapping operation once its assumptions hold; it does not establish this FieldTail registration or discharge. Falsifier: drop/alias any receiver/result/effect row across Capture/FreshUse, accept missing/ambiguous/stale role members, or accept a method while `show` remains unresolved.

The original R149 goal remains both unchanged CLI samples, public types/output, ordered execution and applicable proof. Console imports/host operation, whole-module execution, exact output, independent review and production remain open.

## Captured FieldTail row bundle

Candidate admission now registers each deferred FieldTail by exact `SourceRootId` and occurrence. Its obligation retains the parse-owned source key/member spelling and four typed rows: receiver Value, receiver Effect, result Value, result Effect. Before Capture, rows are canonicalized in the current intrusion state. The provider Graph interns all four and validates their presence. `FreshUse` stores one obligation ordinal with four graph-row indexes; all four reconstructed identities are read through the same `FreshUse.rows` vector. The source/member identity remains attached to the captured Graph. Pending obligations still force `DeferredSelectionUnavailable` at candidate finalization.

The solver test `deferred_field_tail_rows_survive_capture_and_same_freshuse_map` passes with `shadow-apply-candidate`, including checked resource-byte refresh and local-versus-shared row identity behavior. The unchanged Types and Console focused Playground tests both pass at their current fail-closed boundaries. Types now passes candidate collection, executes capture/session processing and remains rejected because role selection is unresolved; Console still fails at imported-name preflight. Neither source executes.

At this checkpoint the imported role/member candidate identity is retained, but no receiver-bound implementation is selected, nested `show` discharged, or selected method application connected. The source-to-obligation registration has executable coverage but no independent source/native proof. The accepted-sample and parent theorem gates remain OPEN.

The transport test uses the generic provider source `my select x = x.show`, so it exercises a FieldTail inside a captured definition rather than only the top-level sample expression. It confirms source occurrence/key and spelling survive into `Graph`, all four rows are present after Capture, and each local row's FreshUse image is distinct while shared anchors remain fixed. This is a bounded algebraic bridge test; the ordinary sample tests still stop before method selection.


## Authenticated member candidate identities

Pinned provider role indexes now accompany export indexes through Playground preparation and provider projection. Import resolution retains exact role and member IDs only when a resolved imported public declaration is authenticated by a unique intact role index. This inventory supplies identity candidates only; it does not inspect receiver bounds, choose an implementation by spelling, or synthesize a member type. A role declaration that cannot be reconciled with its source export index still rejects import construction, preserving the prior import contract. A recovered, duplicate, or ambiguous member inventory yields no member candidate, so later selection remains fail-closed.

Candidate collection attaches the exact imported role-member IDs whose member spelling matches a FieldTail to the deferred relation. The IDs survive admission beside the existing parse source key and member spelling. The focused solver test `deferred_field_tail_keeps_authenticated_role_member_candidates` verifies that an imported `Display.show` source member identity reaches the FieldTail obligation; `deferred_field_tail_rows_survive_capture_and_same_freshuse_map` verifies the separate row transport contract. The unchanged Types/Console boundary tests and `cargo check -p yu-playground` pass.

This slice still does not select a role implementation from receiver bounds, connect the FieldTail to a chosen method application, discharge nested `show`, or execute either unchanged sample. The exact samples, source/native bridge, independent review, and R149 parent gate remain OPEN.


## Types receiver bounds

A bounded solver test now runs candidate source scheduling through the unchanged Types bindings and retained `pair.say` FieldTail. After the full source schedule, the receiver row reaches a positive two-element tuple lower bound. Its children remain separate positive Value rows; following the ordinary direct-lower edges reaches `IntPositive` for the first child and `StrPositive` for the second. This is the exact receiver evidence needed to distinguish the pinned ordered-pair `Display` implementation from the other source candidates.

The test `types_sample_fieldtail_receiver_bounds_expose_ordered_pair_shape` passes. It observes solver bounds directly and does not force a type, choose an implementation, type the method body, or run output. The next implementation seam is to match authenticated implementation target structure against these already accumulated receiver bounds, then transport the selected default/member source and its nested `show` prerequisite through the same candidate session.


## Source tuple to receiver-bound bridge (candidate lane)

For the candidate collector's `LocalSourceForm::Tuple`, each source child contributes its positive endpoint in source order to `CandidateRelation::Tuple`. Candidate admission turns that ordered endpoint vector into one positive tuple term and constrains that term as a lower bound of the tuple expression's result row. The source Name/use path for `pair` links that result row to the FieldTail receiver row. Consequently the direct-lower traversal in the test reconstructs the same ordered tuple constructor and its two element rows; their independent lower chains preserve the `answer` integer and `name` string facts.

This is a source-constructor-to-candidate-bound correspondence for the inspected production path, supported by the end-to-end session test. It does not establish the declarative Yulang typing rule, completeness of bound enumeration for arbitrary intrusion/replay, role implementation selection, `show` discharge, or evaluator correspondence. Those remain separate OPEN obligations under the companion's source/native closure contract.


The pinned `Display` source inventory test now also counts matching ordered-pair targets and confirms exactly one among the 14 authenticated implementations. Together with the Types receiver-bound probe, the source inventory has one structurally matching candidate for the observed outer tuple shape. The compiler still has no code that performs this join, checks all receiver bounds against the source target, or routes the selected `show` body; unique source inventory plus observed shape is not yet selection or conformance proof.

## R302 checkpoint and next cross-layer seam

R302 ends at 1740/1800 charged seconds. The evidence changed the next implementation question: matching the raw implementation target to the receiver's outer shape can identify a candidate but cannot type or execute that candidate's original member body. The next route must carry the exact role default member and implementation member source identities into HIR and a candidate definition-use path, then select only after the same session's receiver bounds settle. R302's captured FieldTail rows and imported member IDs are reusable inputs. No method selection was made; both unchanged samples and all source/native, A/B, review and production gates remain OPEN.
