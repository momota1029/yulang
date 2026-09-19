# AssociatedChains ownership amendment

Status: Authoritative

Scope: ownership of nested associated operator chains in the approved first
`yu-hir` association slice only. This does not define later `HirModule`,
declaration, name, type, effect, or ID ownership.

Approved-by: user
Approved-at: 2026-09-19
Drafted-by: primary agent
Reviewed-by: performance_auditor (resource-risk audit, 2026-09-19)
Supersedes: the unspecified nested-chain retention detail in
`2026-09-18-hir-operator-association-first-slice-draft.md`

## Decision

`AssociatedChains` retains only top-level `OperatorChain` results. When an
`OperatorChain` occurs inside another expression's structural child, the
associator visits and associates it exactly once, then retains its owned result
only through the enclosing `HirExpr` tree. It does not also retain that result
as a standalone `AssociatedChain` entry.

The top-level result order remains source order. The owned recursive expression
representation selected by D3a remains unchanged.

## Rationale and invariant

The initial candidate retained every chain in a flat postorder vector while
also deep-copying each nested owned tree into its parent. A valid nesting depth
of `D` could therefore retain `O(D^2)` expression data and require matching
clone work. The approved topology keeps one owned expression representation per
source chain containment edge and avoids that duplication.

This changes ownership only, not association behavior:

- every encountered chain is still associated exactly once;
- nested chains are associated before their enclosing structural consumer;
- the CST remains unmodified;
- the exact `ParsedFile` operator table remains the sole association environment;
- no diagnostics, types, names, declarations, or `yu-types` dependency are added.

## Consequences

Consumers that need an independent index over nested chains may build one in a
later explicitly approved phase. They must not reintroduce duplicate owned trees
as an incidental convenience. If stable nested IDs or shared expression handles
are needed, that is a separate representation decision.
