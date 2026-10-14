# Executable source inference playground

Status: reviewed experimental implementation; complete for the documented CLI scope.
Branch: `research/simple-sub-intrusion`.
Implementation baseline: `e450c1836c008aa0bb81d4ad7edab9788e2fb9c2`.
Proof checkpoint: `793886f76`.
Authority: the user's October 14 request to implement a playground while
proving necessary properties and repairing the implementation; the
[research playground direction](../design/2026-10-04-inference-research-playgrounds.md)
and [top-level inference principles](../design/2026-10-11-yulang-inference-top-level-principles.md).
Mode: M2 for the executable/API slice, two independent reviewers
(`regression_auditor`, `performance_auditor`). The bounded mechanism proof has
its own independent `compiler_referee` review.

## Delivered behavior

The workspace package [`yu-playground`](../../tools/inference-playground/README.md)
accepts a local source file or standard input. It runs the existing parser,
retained LocalSource and `CandidateInference`, then prints finite graph node
references, canonical row identities and every retained bound. Cycles do not
cause recursive type printing. Function fields retain their actual
argument/argument-effect/result-effect/result order. Effect operands with no
public content observation remain explicitly opaque.

`--intrusion` adds a borrowed observation of actual source Value endpoints and
SCCs, original extrusion records, separate reuse occurrences referencing their
original pair groups, current row representatives, group activation and pending
consumption. The original reference graph moves into the frozen candidate
result after existing accounting. No graph reconstruction, cloning, new
inference rule or production routing is introduced. The retained candidate
graph has a longer lifetime until result drop; its storage is already included
in collection accounting. The public legacy result does not retain it.

The nested-recursion example yields two mutually qualified source associations,
four parent/copy records in one activated group, and four consumed requests.
These are observations of that example, not a source-global correctness claim.
Application locations are authentic call-tail spans. For the exact example,
byte ranges `33..34` and `43..44` select `y` and `x`; no parser/HIR coordinate
repair was necessary.

Syntax diagnostics, unsupported candidate construction, candidate conflicts
and tool limits remain distinct outcomes. Conflicts withhold graphs and
intrusion observations. All report construction is atomic: a failed report
prints no graph prefix. Examples cover identity, nested recursion, effects and
a type conflict; usage is documented in the tool README.

## Proof consumed

The [retained-event activation theorem](../theory/2026-10-14-value-intrusion-activation-correspondence.md)
passed fresh independent review at the frozen implementation baseline. The
primary accepts original-Value reachability/SCC preservation by helper
projection, exact group activation from original or reuse event sets, one
registration/consumption per original pair with the resulting equivalence
closure, immutable original ownership and rollback restoration. The only
review finding was read-process provenance; it is corrected.

This closes the bounded mechanism obligation. Source-global applicability of
transported event sets to every later extrusion and preservation of typing and
required principality remain separate open obligations. The actual source,
replay, fresh-use and generalization owners now have this mechanism lemma to
reuse. Existing hygiene results remain available; this work does not reprove
them or certify their missing executable boundary correspondence.

## Review repairs and resource boundary

The regression review confirmed API fidelity, source diagnostics, effect
opacity, Function fields, feature gating and examples. The acyclic test now
checks source health, both top-level binding identities and their exact event
endpoints. Nonempty source-generated reuse observation/rendering coverage is
still absent; conditional checks do not claim to supply that witness.

The performance review found that per-graph caps alone allowed excessive
aggregate output, repeated source snippets and source-set printing. The repair
uses one checked writer for all graphs, intrusion records or diagnostics:

- Input: at most 65,536 bytes.
- Per graph: at most 4,096 observed nodes, distinct rows or bounds.
- Whole report: at most 1 MiB of UTF-8 bytes and 16,384 observation work entries.
- Work includes raw row visits, node/child visits, definitions, bounds,
  diagnostics, intrusion records and every printed source-event incidence.

Formatting goes directly into that writer from borrowed source/name slices.
Failure is sticky and rejects the complete report. Both independent delta
reviews closed with no blocking or major findings. Observation-local vector
interning, representative walks and reverse-map/source lookups remain bounded
outer traversals with potentially multiplied inner work; no linear rendering
or solver CPU-time bound is claimed. Timing measurements were unnecessary:
benchmark processes and samples consumed are both zero.

## Verification

Cargo commands used `CARGO_BUILD_JOBS=2`, `timeout 300s`, and one test thread.
Final checks:

- `cargo test -q -p yu-playground -- --test-threads=1`: 3 writer unit tests and
  12 CLI tests passed. A bounded source-generated case uses 20 simple calls on
  a line padded by 60,000 spaces to reach the report cap; it verifies nonzero
  exit, the tool-cap diagnostic and empty stdout.
- `cargo test -q -p yu-solver --features shadow-apply-candidate --test candidate_intrusion_observation -- --test-threads=1`:
  3 passed.
- The same solver command with `--test candidate_lifecycle_retirement`: 2 passed.
- `cargo check -q -p yu-solver`: passed without warnings.
- `cargo check -q --workspace`: passed without warnings.
- `rustfmt --edition 2024 --check` on the four new tool source files, tool CLI
  tests and new solver observation test: passed.
- `git diff --check`: passed.
- `cargo xtask check-graph`: failed on the existing `yu-solver` development
  dependency on downstream `yu-core`. Exact baseline `e450c1836` already has
  that unchanged entry in `crates/yu-solver/Cargo.toml`. The new tool introduces
  no prohibited dependency. Resolving this requires a separate solver/core
  test-layout review.

Final focused runtime coverage is 20 passing tests. No full workspace test
suite, timing benchmark, source reuse-witness search or global inference proof
was run. Formatting touched only new Rust files; unchanged broad checks were
not repeated for record-only updates.

## Remaining implementation and integration

At this CLI checkpoint the carrier lacked If/Boolean/String/arithmetic
construction. The subsequent [conditional checkpoint](2026-10-14-conditional-source-playground.md)
implements the user's heterogeneous-branch example using the existing colon
grammar, with both branches generating constraints. Arithmetic remains outside
the carrier. The existing hygiene
theorem still needs its executable permission/protection constructor and
consumer correspondence. Neither gap is hidden by successful playground output.

The primary synchronized `tasks/current.md`, `tasks/research-lab.md`, the design
index and playground direction. The pending negative-formal-permission question
bundle remains unstaged and outside this work. The implementation checkpoint
contains only the tool, read-only solver observations, their focused tests and
these records. No F5 cutover or broader source-admission claim is made.
