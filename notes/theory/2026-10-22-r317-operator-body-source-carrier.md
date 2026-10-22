# R317 — provider operator body source carrier

## Entry

R316 joined the selected imported operator use to the exact provider declaration/body owner receipt. The consumer `LocalSourceForm::InfixOperator` still stops in candidate collection. The provider's original RHS is not an ordinary HIR binding. A focused probe found it is retained as an ordinary `HirItem::Expression` with its own expression source root and LocalSource carrier; the missing bridge is a checked lookup from the imported owner receipt to that existing root.

## Bounded objective

Expose a checked lookup from an imported `SourceOperatorOwner` and its exact selected provider index to the already-retained operator RHS expression root in the provider HIR artifact. Require provider module/revision and full owner receipt equality, source-key ownership by the provider parse, a unique supported carrier, and exact root body range. Preserve the actual RHS form, child source keys and nested parser-selected operator uses.

This is source ownership and construction only. It does not infer or generalize an operator scheme, type the RHS, lower infix to ordinary function application, select, execute or change accepted syntax. The next consumer gate must connect the exact provider body value to the consumer's preserved operator occurrence with correct per-use behavior.

## Current evidence

`SourceExportIndex` retains operator body text, range and `SourceNodeKey`. `HirModule` local source maps currently key ordinary definition roots; separate member roots exist for role and implementation members. R315 already captures four nested infix uses in the original `Display.show` body. R316 proves imported receipt equality with the exact selected provider index and rejects private/recovered declarations.

## Outcome

`HirModule::source_operator_root_for` now authenticates the imported owner against the exact selected provider index and joins it to the unique supported `SourceRootId::Expression` whose source key is the owner's exact body key. It checks the provider module, selected revision, full receipt, parse brand, carrier ownership and exact body range. The RHS was already retained as a direct expression; the implementation reuses that root and creates no synthetic binding or duplicate carrier. Same bytes from a different parse fail closed.

Pinned stdlib coverage follows the consumer's imported `+` provenance through the R316 receipt to the matching `core/ops` provider HIR carrier and verifies the original body range/text. `cargo test -p yu-hir --lib` passes 166 tests and `cargo test -p yu-playground --lib` passes 41 tests. Static sprint consistency and diff whitespace checks pass.

## Proof and falsifiers

The bounded correspondence is: the consumer-selected owner receipt equals the exact provider-index receipt; its body key identifies one expression root in the same provider HIR parse; the LocalSource carrier for that root retains the exact body range. Therefore the returned root denotes the selected provider RHS source. This proves source identity only. This does not establish typing, candidate completeness, soundness, principality or runtime behavior.

Falsifiers: foreign parse brand, stale range, private/recovered source admitted, duplicate match, missing nested occurrence, changed operator provenance or changed ordinary binding behavior. Do not introduce a second root: the provider expression carrier already exists. If the owner cannot resolve uniquely to it, preserve fail-closed behavior and identify the exact identity invariant.

## Next gate

Connect the existing carrier to candidate Apply while preserving the consumer operator use and both operands, with sound per-use generalization/effect handling. The operator RHS currently appears as an error-adjacent module expression and is not yet an exported generalized operator value; resolve that declaration/generalization owner before linking candidate terms. Parent Y2 sample objective and R149 remain OPEN.
