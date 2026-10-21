# R288 rev2 — Index pinned fmt role/impl source without lowering unrelated bodies

Status: solo continuation under the unchanged Y2 sample goal; no subagents by user instruction.
Baseline: `69704582a57db3b73517a2fab7e385b2864deba2`.
Supersedes R288 rev1's proposed ordinary local-source HIR route after direct counterevidence: lowering the exact, diagnostic-free `lib/std/core/fmt.yu` stops at `my format_fill(spec: format_spec): str = case spec.fill` with `StructuralProjection`.

## Outcome

Add a source-only role/implementation declaration index for one supplied `ModuleIdentity` and `ParsedFile`, using parse-owned `SourceNodeKey`s. Use it on the blob-checked pinned `std::core::fmt` file and verify the `Display` role members and two-parameter tuple implementation retain exact ranges, order, module IDs and parent-qualified member IDs.

## Limits and falsifiers

The caller-supplied module identity is not itself import authentication. This index performs no import linking, semantic name resolution, type/member validation, conformance, selection, constraints, runtime, or theorem closure. Fail if declarations are recovered/unexpected, source ranges/text mismatch, member order/ownership changes, or the same source index requires unrelated body lowering.

## Exact paths and checks

`crates/yu-hir/src/module.rs`; `crates/yu-hir/src/shadow.rs`; `tools/inference-playground/src/lib.rs`; this contract; R288 outcome note; `tasks/agent-loop/current.json`. Run the focused pinned-fmt playground test, HIR check, sprint check and `git diff --check`. Solo-authored, unreviewed.
