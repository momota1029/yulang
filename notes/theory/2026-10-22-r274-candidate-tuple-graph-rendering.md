# R274 — ordered Tuple candidate graph rendering

Status: provisional diagnostic-rendering packet; unreviewed. R149's public type display and all sample/proof gates remain OPEN.

## Parent application

R270/R271 retain ordered Tuple structure in the candidate graph; R273 adds ordered positive and negative Tuple constructors to the closed-type API. `tools/inference-playground/src/render.rs` still traverses only fixed Function children, so direct Tuple nodes and nested children are not shown by the candidate graph renderer.

This packet makes that existing diagnostic view expose retained Tuple structure in source order. The graph retains unresolved row/effect premises and is not a public closed scheme. No source typing, principal type, R149 Types pane or production claim follows.

## Evidence

Pending focused direct/nested candidate-render checks. The renderer remains provisional and unreviewed under the user's solo-work instruction.
