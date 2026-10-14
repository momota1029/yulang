# Omitted formal: exact retained pair/source uniqueness discriminator

Date: 2026-10-15
Status: provisional test-only harness; focused execution passed; independent M1 review found no issues
Branch: `research/simple-sub-intrusion`
Assigned frozen HEAD: `e2d913d6412bd332bea1860d495999d5717bc5ff`
Production source baseline: `427d1ff5daab866fa7d89cb513a077063cc6454d`
Parent gates: H1/H2/U OPEN; H3/P disabled

## Scope and bounded method

Authority is [top-level inference principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§1.1 and [annotation integration](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§§1,3–5. Dependencies are the reviewed
[consumer frontier](../theory/2026-10-15-omitted-formal-extrusion-consumer-frontier.md)
and [receiving-call observation](2026-10-15-omitted-formal-receiving-call-dispatch.md).
The only code change extends the existing receiving-call test. Its exact fixture,
HIR/Apply/FormalConstruction authentication and same-parent repair
`incidence.comparison == parent` are preserved.

For every retained extrusion Parent, enumerate the entire retained Relation
table, across all contexts, matching `Some(key.pair) == parent.comparison` and
`key.sources == parent.sources`. Print each candidate RelationId and full
RelationKey. Do not canonicalize the Parent or restrict candidate contexts.
Authenticate `cb x` by the checking occurrence of the already HIR-authenticated
Apply input. Print every origin with that exact occurrence and its full key.

Only a singleton candidate equal to the sole authenticated source origin may
enter the subsequent join. Missing pairs, zero/multiple candidates or a different
source relation print an obstruction and stop inference for that Parent.
The existing dependency observation continues, without weakening its assertions.

For each exact FunctionPort Argument parent, inspect only immediate Replay
dependencies whose child equals that parent. Preserve the existing checks that
both Replay input RelationKeys have the exact corresponding bound pairs. Follow
only explicit Derived/Transport parent edges from the Replay upper input, with
cycle suppression. A source origin reached through those edges connects the
singleton Parent join to that exact Replay and Argument edge; print both edges
and the traversed ancestry. Multi-input Replay ancestry is never used to select
the source of the upper bound. A singleton with no such consumer prints an
ancestry obstruction. All numeric identities are session-local observations.

This establishes a conditional source-to-copy initiation and source-to-consumer
provenance join. It does not establish a direct Function field path for a copied
row, or that every copy initiated by the source relation supplies that Argument
port. Selected bound descendants are copied in the same extrusion traversal;
the initiating relation alone cannot distinguish their field paths.

## Read-only owner correspondence and processing alignment

At the frozen production baseline:

- `candidate_effect.rs::candidate_task_scope` sets pair processing to the exact
  active task key. `lib.rs::step_typed_drain` sets that scope and the active
  contextual RelationId from the same current TypedWorkItem before each stage.
- Transport updates the current item's RelationId using
  `candidate_context_transport_task`; `candidate_context_execute_relation`
  checks its pair against the task's contextual pair. Dispatch sends a changed
  canonical task back to the queue before structural extrusion. At the
  structural-bound extrusion branch, the active task pair and the retained
  contextual pair therefore agree. Context execution restores its enclosing
  processing relation on return.
- `lib.rs::dispatch_live_item` invokes `candidate_extrude` for the structural
  upper demand when the lower is a receiving Value row and the endpoints are
  not both Functions. `candidate_extrusion.rs::candidate_extrude`, at each
  actual copying Visit, allocates the copy and calls `retain_extrusion_parent`
  before inserting its one-sided bound. Function ports and selected bounds are
  both traversed; no field path is retained by Parent.
- `candidate_intrusion.rs::retain_extrusion_parent` copies `comparison` from
  `effect_algebra.processing` and `sources` from
  `context.extrusion_sources()`. The latter reads the sources of
  `context.processing`'s exact RelationKey. These are the pair and source set
  of the same active typed-drain relation/task on the route above. The copy
  traversal does not replace these processing slots; bound-origin admission
  and transfer construct dependency/evidence records without changing them.
- `candidate_function_port_admit` records the actual processing RelationId as
  the FunctionPort parent. The harness joins Replay to that recorded parent,
  preserving the distinction between source checking relation and comparison.

This is bounded static correspondence for this route, not an assertion that all
possible extrusion entrypoints have the same alignment. The runtime discriminator
requires exact retained pair/source identity, singleton uniqueness and the source
origin before applying this correspondence. No production retention change or
copy-time instrumentation was made.

## Outcome, verification and handoff

Primary outcome: the exact focused command below passed twice (`1 passed; 688
filtered out` on each run). The second run followed a log-label-only clarification
that grouped consumers by source RelationId. Every one of the four retained Parent entries matched exactly
one full RelationKey: `RelationId(5)`, with the authenticated `cb x` checking
origin, `ContextId(0)` and `sources: Some(0)`. Those session-local labels are
observations, not expectations. The four Parent entries share this same
initiating relation; tuple uniqueness does not give each copied row a separate
identity.

For the later FunctionPort Argument comparison, its immediate Replay upper
input reaches `RelationId(5)` through explicit `Transport` and `Derived` edges.
The source relation therefore has both an exact retained Parent-initiation
association and an upper-bound ancestry to that Argument consumer in this run.
The harness deliberately records these as two paths from one relation. It does
not claim a serial per-copy-to-consumer path or identify which copied Function
field supplied the Argument port. The separate receiving-call Argument chain
to `outer/cb` remains independently authenticated.

The primary made a log-label-only clarification between the two runs: repeated
output no longer labels each copied Parent as a separate consumer. Relation
matching, ancestry selection and assertions were unchanged. The exact command
reported `1 passed; 0 failed; 0 ignored; 0 measured;
688 filtered out`; no broad suite, formatter, executable probe or measurement
ran. Two Cargo processes were used by the primary; the worker Cargo/test/probe
budget was zero. The producer's static/edit pass stayed within the assigned
twenty-minute ceiling; total measurement samples and heavy worker processes
were zero.

Fresh `compiler_referee` M1 review of the frozen harness and pre-execution
record found no issues. It verified exact all-context matching, source-origin
authentication, the scoped processing alignment, exact Replay/FunctionPort
join, the existing same-parent repair, and the no-per-copy limitation. The
primary incorporated the runtime observation above without changing inference
behavior or relaxing that limitation.

Primary-owned single focused command:

```sh
CARGO_BUILD_JOBS=2 timeout 300s cargo test -q -p yu-solver --features shadow-f5,shadow-apply-candidate --lib candidate_context::tests::omitted_formal_receiving_call_records_authenticated_argument_dispatch -- --exact --nocapture --test-threads=1
```

Frozen input SHA-256 values checked by the producer (test file before edits):

```text
5424885f127469ed1148ede2d9aadecd06f88c35df6094854962c80ccaa233bd  candidate_context_tests.rs before edits
6301ca80eec137df3f2c2c44e2edaa7dbdf1ed7a78c69617228888e63654e461  candidate_context.rs
ed3e213e943a553943784e409194723f64acb810a0bcf06607ee95b0eb4e4ed1  candidate_extrusion.rs
77b145ed8a8bf2fae30a07ed74d11a29f38d18930f92e3c1c10456244fe9402e  candidate_intrusion.rs
f414efa7efdb17644f4dfa6b0bba621c1bb7cccd0f83735c33a0acb875da6b91  candidate_effect.rs
e902da1c9a7f0fb4dcd806c87563d1ae46d35bbb999e69b7fee51c3c0f6e4bf5  lib.rs
```

Leased outputs are `crates/yu-solver/src/candidate_context_tests.rs` and this
note only. Production dependency assumptions did not change. Git operations and
shared synchronization at `tasks/current.md` and `tasks/research-lab.md` remain
primary-owned. Proposed checkpoint message:
`research: discriminate omitted-formal copy relation identity`.

Unverified beyond this one state: uniqueness/ancestry in other runs and any
direct copy-output field attribution. All-path transport, source-profile
introduction, protection preservation, U selection/coverage/bypass, dynamic
Receive/Observe, full Call, generic opening, soundness, principality and F5
cutover remain open. H1/H2/U stay OPEN and H3/P disabled. No omitted-formal
position matrix, language/API/representation decision or parent-gate closure
follows. An ambiguous join stops this packet; any production retention change
requires a separate authorized owner packet.
