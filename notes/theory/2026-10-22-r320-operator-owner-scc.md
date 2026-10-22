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

## Per-occurrence FreshUse and curried Apply checkpoint

Candidate execution now freshens the retained exact provider graph for every
operator occurrence after provider expression schedules finish. Each route uses
a dedicated occurrence slot and keeps its `FreshUse` maps in `GraphState`,
accounted as retained memory; provider graphs are shared by `Arc` and charged
once. The root scheme is consumed as a curried function: first Apply receives
the left operand and its effect, then the resulting function receives the right
operand and its effect. The intermediate result and effect are fresh rows. The
second Apply publishes the original infix result and final effect. The imported
operator value lookup has an explicit empty computation effect.

The focused imported-owner regression now reaches `execute_scc_plan == Ok(())`
and checks exact provider/owner/occurrence retention plus retained provider
FieldTail evidence. `cargo test -p yu-solver --features shadow-apply-candidate
imported_operator_expression_is_captured_before_consumer_admission` passes, and
`cargo test -p yu-playground --lib` passes 42/42. `python3 tools/agent_sprint.py
check` and `git diff --check` pass. This checkpoint proves only candidate
construction for strict infix uses. A two-binding fixture verifies two uses of
one imported provider retain distinct FreshUse contexts. Nested provider
dependency ordering is covered in the later checkpoint below; source/native
proof, the unchanged sample command path, R149 and production/cutover remain
open. The unchanged Types test still stops at deferred FieldTail/role selection
after operator candidate execution.

## Nested-provider fixture probe

A direct fixture was attempted with provider `(*)` whose RHS contains imported
`(+)`, while the supplied provider roots were intentionally ordered dependent
first. The source-owner roots themselves were available, but the assembled
candidate batch returned `ComponentIdentityExhausted` before `execute_scc_plan`
ran. A first HIR setup using `SemanticImports::with_source_imports` returned
`SourceImportResolutionUnavailable`; retrying with empty value imports got
past lowering but still failed candidate collection. Neither attempt tests the
provider-order executor, so no nested-ordering claim follows. The temporary
failing regression was removed. The next useful step is to isolate which
candidate source collection invariant rejects the nested operator-use carrier,
then rerun the exact provider-before-dependent execution fixture.

## Nested dependency execution checkpoint

The earlier nested fixture failure was caused by omitting the pinned
`std::prelude` indexes required by `SemanticImports::with_source_imports` for
identifier-bearing source modules. The fixture now builds the base and derived
operator providers plus the prelude indexes, while deliberately listing the
derived provider before its base dependency. `execute_scc_plan` succeeds; both
provider graphs are captured, the derived RHS retains a use of the exact base
owner/root, and the consumer retains a separate use of the exact derived
owner/root. Their `FreshUse` context IDs differ. The focused regression
`nested_operator_provider_rhs_uses_dependency_before_capture` passes.

The strict-infix and nested-provider regressions pass, and `cargo test -p
yu-playground --lib` passes 42/42. `python3 tools/agent_sprint.py check`,
`python3 -m unittest discover -s tools -p 'test_agent_sprint.py'` (57/57), and
`git diff --check` pass. This closes R320's bounded candidate correspondence.
Runtime/source-native correspondence, the unchanged Types candidate success,
Console, R149, independent review, parent proofs, and production remain open.
