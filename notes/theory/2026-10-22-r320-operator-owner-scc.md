# R320 — operator candidate dependency owner

Status: OPEN. This packet begins from a source-verified obstruction, not a completed operator implementation.

## R319 result

R319 corrected the candidate boundary. `ClosedSchemes::for_root` is a legacy binding scheme API, not the main candidate consumer. Candidate graph capture is allocated and scheduled by binding definitions. F0 `DefinitionUse.target` and F1 `SccPlan` also accept only `DefinitionOrderId`; candidate expression schedules execute after the binding SCC plan. Therefore a late expression-root capture cannot satisfy a consumer route that already needs a per-use scheme.

The exact ownership chain remains available: imported `SourceOperatorOwner`, provider `ExpressionRootId`, and parser-owned consumer occurrence. None of those identities is itself a generalized candidate value yet.

## R320 construction target

Introduce a source-backed operator scheme owner in candidate dependency order without changing the ordinary binding identity path. The provider graph must be executed/captured before consumers, then instantiated independently at each authenticated operator use. For supported strict infix forms, retain left/right order and lower through two ordinary Candidate Apply relations with all four function ports and both effect endpoints intact.

The key invariant is that the provider declaration owner, its RHS expression root, and every consuming operator occurrence remain distinct source identities. A synthetic definition key, spelling lookup, direct primitive shortcut, or sample-specific stdlib body path would not establish the requested correspondence.

## Remaining proof boundary

Tests can establish exact construction and solver routing only. Source-generation completeness, source/native A/B, runtime correspondence, principality, all operator fixities/laziness combinations, R149 and production remain OPEN. No independent review is available under the user's solo-work instruction.

## Provider-root lookup seam

By source inspection, candidate code can validate a root without adding a HIR identity: require the HIR module and revision to equal the imported owner, then find the direct expression whose `expression_source_key(root)` equals the owner's exact body `SourceNodeKey`, and require its original `LocalSource`. This is a construction route, not yet executable regression evidence; implement and test it before using the root as a dependency node.

## Executed root-lookup evidence

`candidate_operator_provider_root` now joins an imported `SourceOperatorOwner` to one unique provider HIR and `SourceExportIndex`, then calls `HirModule::source_operator_root_for` and requires its existing `LocalSource`. The focused regression passes for the exact parse and rejects a separately parsed artifact with identical bytes and revision. This verifies only owner-to-root lookup; no candidate scheme or infix Apply path is admitted yet.

## Candidate-plan retention checkpoint

The candidate source plan now carries imported operator provider receipts with
their exact `ExpressionRootId`, plus a separate record for each retained infix
occurrence. Each use records its consumer root and HIR occurrence, exact
operator source key, provider slot, ordered left/right value endpoints and
effects, and result value/effect endpoints. Provider roots are computed from
the exact module/revision owner and parse-owned source index before batch
collection. `yu-syntax` moved from a dev dependency to a normal dependency so
the production planner can use the public fixity/provenance types it receives
through HIR.

`cargo check -p yu-solver --features shadow-apply-candidate` passes. The exact
provider-root regression passes and `cargo test -p yu-playground --lib` passes
42 tests. Collection still returns Unsupported when retained operator uses
exist: candidate provider graph capture, dependency scheduling, per-use
FreshUse, two Apply relations, and proof/runtime correspondence remain open.

## Provider graph capture checkpoint

After the binding SCCs have captured their graphs, candidate execution now
executes each exact imported operator RHS expression schedule and captures its
live candidate graph under that `ExpressionRootId` before member schedules can
admit an operator use. The graph remains separate from binding and member
graphs. Expression-owned FieldTail obligations are retained with the graph;
scoped capture and provider bodies that themselves use infix operators remain
fail-closed until their dependencies can be ordered.

The new `imported_operator_expression_is_captured_before_consumer_admission`
regression builds a provider and imported infix consumer from distinct parses,
checks the exact owner/root, then observes the provider graph and its retained
FieldTail before execution returns `DeferredSelectionUnavailable` at the still
missing FreshUse/Apply consumer. The focused solver regression passes. This is
construction evidence only; the unchanged samples still do not pass through
the candidate inference path.
