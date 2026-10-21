# R289 — Index role/impl sources across the pinned Y2 library closure

Status: solo continuation; user explicitly prohibits subagents.
Baseline: `87b1a0405f95b61da55a836d07a829a07fc3addc`.

## Outcome

Use the exact 40-source closure already validated by `pinned_stdlib::resolve_implicit_stdlib`. For each file, derive a source-root identity from its pinned path, parse with the playground syntax environment, and index role/implementation declarations by their parse-owned IDs. Verify every retained declaration's ranges/text and module owner, and report per-module role/impl counts. This supplies authentic declaration identities as input to the later import and candidate resolver.

## Limits and falsifiers

The existing syntax environment is not asserted to be each module's full language import environment. A source-only index is not import visibility, name resolution, semantic conformance, selection, constraints, execution, or proof. Fail if any pinned source cannot be indexed safely, an identity is duplicated across module roots, or any retained source slice mismatches.

## Exact paths and checks

`tools/inference-playground/src/lib.rs`; this contract; outcome note; current state. Run focused and full playground library tests, HIR check, sprint check and diff check. Solo-authored, unreviewed.
