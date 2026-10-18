# Replay fiber consumer certificate implementation checkpoint

Sprint: `npair-replay-fiber-consumer-certificate-20261018`, contract rev1
SHA `fce2f48df81227bfc427503fb785541835865f4c0970dbc27a514ff9f8cbb565`.
Source baseline: `f56022c19`; this candidate was authored after the independent
proof checkpoint `5d107a2bf` and does not change that proof artifact.

## Result

The observer now distinguishes module and local FreshRoute owners and retains
the source relation, copied bound, Replay upper and child roots, consumer
relation, physical fiber slot, and four port relation IDs independently. The
gate checks captured BoundEvidence against the already imported snapshot ID,
the exact FreshUse admission/emission and physical owner/lane, retained Replay
recipe, scoped-flow identity, p1→h root equality in its explicit zero-step
case, q→C zero-step identity, and all four typed endpoint pairs in field order.
Unsupported nonzero root rewrites fail closed.

Two actual-record mutation negatives were added for a route-owned captured
snapshot and retained scoped-flow transformer. Assertions were added to the
fixed two-use module fixture for distinct module ownership, p1=h and q=C
zero-step roots, and retained physical slots. These assertions and mutations
have **not** been run. Therefore no positive route authentication or observed
root equality is claimed. The statically visible source route carries the
mapped source term in `RetainedFreshUseMaps.terms[node_index]`; the Replay upper
root is read from `row.upper_input`. The equality is only asserted in the
focused fixture, not established by this authoring pass.

## Remaining source-owner obligations

- `BoundEvidence` retains the imported source snapshot and source bound, but
  its coverage still explicitly contains `ReplayUseAntecedentsNotRetained`;
  this implementation cannot reconstruct antecedents the owner did not store.
- The source slice retains no constructor for a nonzero p1→h root rewrite. Such
  rows are rejected. The missing owner is the relation/replay producer that
  maps the copied function root to the Replay upper root.
- C is currently authenticated only as q's zero-step consumer. A nonzero q→C
  rewrite needs a retained typed-dispatch producer edge naming C.
- Existing targeted wrong-use/root and swapped-port falsifiers remain. Actual
  dependency-kind, fiber-membership, and stored consumer-endpoint mutation
  negatives were not added in the remaining authoring window.

No new persistent storage was added. Endpoint reconstruction scans existing
graph nodes and retained maps without allocation. Diagnostic strings are
created only in the existing observation output path.

## Checks and freeze

- `git diff --check`: passed.
- Whole-file `rustfmt --check` on the three solver files: failed on broad
  pre-existing formatting differences; it made no changes and is not evidence
  of a new formatting regression.
- No Cargo, build, or test command was run, as required during authoring.
- No commit, push, or Git state mutation was performed by this lane.

Changed leased paths and frozen SHA-256:

| Path | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/candidate_context.rs` | `c0952a2c618bc01d7291f8c48c5e2012cffaa1c95491e2d026ff16a0831e0d12` |
| `crates/yu-solver/src/candidate_scheme.rs` | `9e548da9575d74a1da9ca8e70a70249eb3dc7a7c0f54f2cba5c525e0bfe1e73e` |
| `crates/yu-solver/src/shadow_apply.rs` | `6e5bd643cec8ce4ac1af38148746136f096f741567ba9ff9041286799698dc25` |
| `crates/yu-solver/src/tests/candidate_graph_call.rs` | `5ab72a8afcfb439e076f00d304909c0cc790c706687738389054fa590b578548` |

Unchanged leased source/example SHA:
`crates/yu-solver/examples/research_scoped_formal_replay.rs` =
`e4c1bec2a41accfe09f664d5992b2575ce78b855c3ff622f08eeb6de8765e3d3`.

The source-to-proof parent theorem remains open; no theorem condition is
counted as resolved by this unrun candidate. Next step: independent review of
the frozen code, then run the fixed two-use fixture and mutation tests only if
review accepts the candidate. If a positive assertion fails, preserve the
first missing owner record and fail closed rather than weakening the gate.
