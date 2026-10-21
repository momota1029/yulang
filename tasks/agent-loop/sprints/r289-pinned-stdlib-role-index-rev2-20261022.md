# R289 rev2 — Index root role/impl sources over the exact Y2 stdlib closure

Status: solo continuation; user explicitly prohibits subagents.
Baseline: `87b1a0405f95b61da55a836d07a829a07fc3addc`.
Supersedes rev1 after the common playground syntax environment produced 90 diagnostics in `lib/std/text/str.yu`. Rev2 builds each file's syntax environment from the public headers of its exact direct pinned imports.

## Outcome

Use the exact 40-source closure validated by `pinned_stdlib::resolve_implicit_stdlib`. For each module, derive its own syntax environment and source-root identity, then index direct-root role and standalone implementation declarations by parse-owned IDs. Retain recovery flags instead of treating a source-only identity index as semantic admission. Verify module ownership, globally unique IDs, member parent IDs, source ranges/text, and counts of recovered declarations and parser diagnostics.

## Limits and falsifiers

This is source identity inventory only. Recovery flags do not authorize type/member checking, conformance, import visibility, candidate selection, constraints, execution or proof. Fail on missing imports, unexpected direct declaration structure, duplicate module/role/impl IDs, bad source slices, or loss of recovery status. Nested attached impls remain outside this root-only index.

## Exact paths and checks

`crates/yu-hir/src/module/source_role.rs`; `crates/yu-hir/src/module/source_impl.rs`; `tools/inference-playground/src/pinned_stdlib.rs`; `tools/inference-playground/src/lib.rs`; this contract; outcome note; current state. Run focused and full playground library tests, HIR check, sprint check and diff check. Solo-authored, unreviewed.
