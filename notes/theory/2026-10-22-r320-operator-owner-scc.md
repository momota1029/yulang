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
