# R52 Luna source-construction audit: mixed capture

Status: static source/owner audit complete; no source-qualified mixed-cut counterexample or closure theorem. Original parent remains OPEN 0→0.

Contract: `tasks/agent-loop/sprints/computation-mixed-capture-20261019-r52.md`, revision 4. Scope is the ordinary candidate source/capture route and its actual owners. No code edits, tests, builds, runtime, probes or measurements were performed.

## Source construction and qualification

The approved single-local-self-recursion rule permits a parameterized local function to refer to its own still-open monomorphic initializer root. It does not authorize mutual recursion or polymorphic recursion (`notes/design/2026-10-10-local-self-recursive-binding.md`, “Selected source behavior” and “Proposed source-to-solver seam”). A useful static source shape is:

```yu
my loop x = {
  my forward (t: [io] int) = t
  my used = loop forward
  used
}
loop
```

This shape is source-construction evidence, not a claim that the scoped recursive Apply consumer succeeds. `candidate_source` gives nested initializers the next level and schedules initializer work before `Install`; while the initializer is active, its self Name becomes a direct `Action::Link` to the existing endpoint. The Apply is retained separately and records a `local_callee` route when the scoped experiment is enabled (`crates/yu-solver/src/candidate_source.rs:1033–1040, 1090–1104, 1238–1253, 1259–1310`).

`candidate_value_graph::retain_source` assigns initializer expressions to their local binding owner, adds each resolved Name edge, and represents an Apply event as `(owner of Apply, resolved callee Value)` (`crates/yu-solver/src/candidate_value_graph.rs:92–143, 181–196`). Thus the loop initializer's final `used` Name supplies `loop → used`, and the Apply in `used` supplies the event `(used, loop)`. These Values are in one SCC, so that event qualifies under `Graph::qualifies` (`:206–233`). This defeats an invariant that would simply rule out every qualified recursive-local Apply source event.

Qualification alone does not establish the native path needed by R52. The scoped consumer peels the callee to a Local Name and then requires an exact retained `LocalFreshRoute` plus an installed `LocalScheme` (`crates/yu-solver/src/candidate_call.rs:689–735`). The active self Name is linked before Install and has no such installed-use route. The approved source-recursion decision does not itself approve a new active-Link consumer interpretation; R50 remains NOT ADOPTED. I therefore do not count this candidate as a completed same-lineage native witness.

## Signed owner and capture findings

For scalar row-row constraints, `candidate_apply_value/effect` assigns a negative owner to the lower row when the upper row level is less than or equal to it; otherwise the upper row owns the positive bound (`crates/yu-solver/src/candidate_extrusion.rs:912–969`). A successful negative demand through an older recursive root can therefore activate the negative closure. In the candidate source above, proof-side analysis finds the corresponding signed group would carry both original Function ports and selected closure, rather than only a lone positive result port. That conclusion remains conditional on successful native dispatch and completion; it is not evidence that the scoped admission gate has been passed.

The first mixed-capture owner boundary remains exact and unchanged:

- `Capture::row` marks a row local iff `level > boundary && !non_generic`; `expand_row` stops at a nonlocal row (`candidate_scheme.rs:778–786, 1054–1059`).
- `prepare_candidate_fresh_use` freshens only rows satisfying the same level/boundary/metadata guard and uses one canonical map per source representative (`candidate_scheme.rs:1555–1608`).
- A successful parent-copy merge appends both physical bound sides, lowers the representative level by `min`, combines `non_generic` by OR, redirects the forest and replays lower bounds (`candidate_intrusion.rs:599–690`, inspected statically). Qualified source events only put retained parents into the pending intrusion worklist (`:324–365`).

The static recursive candidate is not the problematic positive-only lowering case: its conditional signed group contains both Function ports. I found no approved ordinary source constructor plus completed native route that realizes the mixed cut and preserves an alternate path between the same reconstructed ports. I also found no invariant excluding that cut for the original source domain. The first missing bridge for this candidate is source-qualified active-Link Apply admission; even after that gate, the general owner invariant at nonlocal `expand_row` versus independently freshened ports remains open.

## Disposition

`NO_SOURCE_QUALIFIED_NATIVE_MIXED_CUT_WITNESS`. The qualified source event is real at the retained source-Value graph level, but the native Apply/consumer route is unestablished. The conditional all-port merge is useful pressure evidence only. No compiler repair or safe code slice follows. Preserve the original quantifiers, source domain and expected outputs; the full inference/evaluator theorem and original Simple-sub A/B remain OPEN 0→0. R50 adoption remains separate and unanswered.

Inspected producer/consumer owners: `candidate_source.rs`, `candidate_value_graph.rs`, `candidate_call.rs`, `candidate_extrusion.rs`, `candidate_intrusion.rs`, `candidate_scheme.rs`, and the authoritative local-self-recursion decision. Exact consumed file hashes are the 24 pins in R52 `current.json`.
