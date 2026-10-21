# R250 — resolve the pinned standard-library module graph

Status: ACTIVE; solo primary implementation and source correspondence.
Baseline: `443e6357b`; original Yulang2 sample goal and R149 scope unchanged.
Resource envelope: 900 seconds, no carryover; no subagents per user direction.

## Outcome

Resolve module declarations and `std::` header imports from the authentic
40-source pinned bundle into a deterministic reachable module closure, starting
at the implicit `std` root. Every declared child module and every `std::` import
must resolve through its longest existing module-path prefix in the bundle.
The root traversal must reach exactly the 40 files pinned by R149 rev10. Keep
source bytes, paths and Git blob IDs attached to each result. Do not infer
imported value names or visibility, or synthesize semantic bindings from the
graph.
The playground parser must obtain its `std::core::ops` syntax dependency from
this resolved graph.

This advances the real source loader needed before semantic HIR import. It does
not accept either sample in inference and does not close any proof gate.

## Exact write paths

- `tools/inference-playground/src/pinned_stdlib.rs`
- `tools/inference-playground/src/lib.rs`
- `tasks/agent-loop/sprints/yulang2-pinned-stdlib-graph-20261021-r250.md`
- `notes/theory/2026-10-21-r250-pinned-stdlib-graph.md`
- `tasks/agent-loop/current.json`

## Checks and falsifiers

Add ordinary tests for the implicit-root graph, exact 40-source closure,
missing module/import rejection, cycle-safe traversal and preservation of
source identities. Run the focused playground tests, existing six-example CLI
tests, formatter for edited Rust, `git diff --check` and sprint-state check.
When the parent `lib.rs` formatter reports differences, compare against HEAD so
pre-existing formatting does not drive unrelated edits.

Falsifiers: a declared module is omitted or mapped to another path; a `std::`
import has no module prefix in the closure; playground syntax bypasses the
resolved graph; traversal duplicates a cycle;
closure differs from the R149 pinned 40-source manifest; or source identity
metadata is lost. HIR semantic imports, tuple inference, roles, runtime, host
writes, output publication, Web/WASM and source/native proofs remain OPEN.
