# R281 — production-only source view for the R70 row/storage edge

Status: Luna preparation only. No Sol proof or code work begins until the source
view and its boundary review pass. Parent is the unchanged Yulang inference and
evaluator soundness/Rust implementation goal, with original source domain,
quantifiers, Simple-sub A/B and semantics. Parent/A/B remains 0->0.

## Fixed parent edge and outcome

Continue only the row/level/bound/representative component of R70's existing W
at both unchanged production `dispatch_live_item -> candidate_extrude` entries,
then apply any proved clauses explicitly to
`R70-ORDINARY-EXTRUSION-ENTRY-RETURN-1`. Derive actual session initialization,
source-generated component/parameter level maps, fresh-row creation, level
lowering, bounds, merges, extrusion copies, FreshUse/restoration, and permitted
failure/resume routes. Do not assume initialized storage or a manually
fabricated native state. Leave every other W clause and parent premise open.

The R280 gate STOP is preserved as a scope incident, not mathematical evidence.
Its full 300-second charge remains consumed; no R280 proof stage was issued.

## Source-view construction and boundary gate

Luna owns these four exact preparation artifacts:

- `tasks/agent-loop/sprints/extrusion-entry-validity-r281-ranges.json`
- `tasks/agent-loop/sprints/extrusion-entry-validity-r281-cfg-exclusions.json`
- `tasks/agent-loop/sprints/extrusion-entry-validity-r281-source-view.txt`
- `tasks/agent-loop/sprints/extrusion-entry-validity-r281-view-index.json`

Use only R255's authenticated 36 workspace path/hash rows and the separately
pinned `crates/yu-solver/src/candidate_context.rs` at SHA-256
`a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905`. Verify
all pins before reading bodies. R255 is only an inventory, not a proof premise.
Read exact production function intervals only. Include all actual writers,
constructors, rollback/restoration and resume paths required by the fixed edge,
including `candidate_source.rs` level-map producers and solver `lib.rs`
level-lowering writes. No source body outside the authenticated paths.

The view's fixed production cfg has `test=false`; feature cfg values remain
symbolic unless the predicate is already false from `test=false`. Parse cfg
expressions structurally. For every omitted span record its original path,
source offsets/lines, exact predicate, why it is false, and SHA-256. Never use a
line filter or a top-level-only `cfg(test)` check. Render only source bytes from
approved production intervals. Put omission markers outside payloads and keep
payloads on either side as separate indexed pieces; do not make removed code
look contiguous. Every source payload must match its exact authenticated
original byte interval. If parsing or boundary classification is ambiguous,
stop preparation without a proof grant.

A fresh read-only compiler referee (300 seconds) checks all payload/hash/offset
correspondence; no overlap with excluded nested test spans; each omission's
production-cfg justification; complete source-constructor/write/restore/resume
coverage; and completeness of every directly required helper body. The referee
must not review its own contribution later as the proof referee.

Forbidden: tests/test bodies in the view; registry/external library bodies;
parser/classifier, runtime or quarantined paths; tests, builds, Cargo, Lean,
probes, benchmarks, compiler edits, semantics or expected-output changes; Git
operations or descendants for the preparation lane.

## Proposed lanes and total resource ceiling

R281 ceiling: 4,700 seconds; no renewal or carryover. Preserve prior R279 and
R280 charges separately.

1. Luna source-view preparation and adjudication: 600 seconds, active.
2. Fresh source-boundary referee: 300 seconds, only after the four artifacts
   freeze.
3. Fresh Sol/high owner-coverage gate: 200 seconds, only after boundary PASS.
4. Sol constructive invariant/application to unchanged R70 W: 2,400 seconds,
   only after owner gate PASS and indexed-view GO.
5. Different fresh independent proof referee: 1,200 seconds, only after Sol
   freeze.

Suggested identities: `/root/r281_source_boundary_review`,
`/root/sol_r281_extrusion_entry_validity`, and
`/root/r281_extrusion_entry_review`. Each worker is a leaf; no descendants.
Future proof output leases, granted only after gates:
`notes/theory/2026-11-03-extrusion-entry-validity-r281.md` and
`tasks/agent-loop/inbox/extrusion-entry-validity-r281.md`. Final review receipt:
`tasks/agent-loop/history/20261103-r281-extrusion-entry-review.md`.

No production code or tests are authorized. Implementation stays
`NO_SAFE_CODE_SLICE` absent an independently reviewed accepted-source violation
of an approved clause and a separate exact code lease. Parent/A/B stays 0->0
until a justified result is applied at its unchanged edge.
