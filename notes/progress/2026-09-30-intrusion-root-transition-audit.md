# SCC intrusion: Oracle root-transition audit

Date: 2026-09-30
Branch: `research/simple-sub-intrusion`
Reference: frozen Yulang2 Oracle `a58eefc3`
Classification: source audit; root simulation theorem remains open

## Observed lifecycle

`AnalysisSession::quantify_component` processes the scheduler's member/root
pairs in order. For each member it runs
`generalize_root_with_prepasses_and_metrics`, collects role prerequisites,
and saves that member's generalized root. It inserts all saved schemes only
after the loop, then finalizes/records them. Incoming-use events follow the
component event. See frozen Oracle
`crates/infer/src/analysis/session/instantiate.rs:14-82` and
`crates/infer/src/analysis/session/selection.rs:1107-1119`.

Within a member, the generalizer loops over compacted root views and constraint
prepasses; restart iterations observe the resulting constraint epoch. After
that loop, it performs bounded alias-expanded and stack-cleaned dominance
passes. Either pass may apply constraints and route constraint events without
restarting the root loop. The generalized root is then formed from the
stack-cleaned compact view. Thus later members read the shared solver state
after earlier root preparation, while an earlier saved root is not recomputed.
The exact ordering is in frozen Oracle
`crates/infer/src/analysis/session/generalize.rs:478-577`; the restart loop
begins at `:30-60`.

This source audit does not establish a fixture in which a bounded post-loop
pass changes a later member's result, nor a source-level accepted witness for
such a two-root interaction. A bounded synthetic-graph probe against an
isolated checkout of the frozen Oracle also found no valid two-root witness;
it made no Oracle edits and is not evidence that the post-loop mutations are
redundant. A fixture remains useful diagnostic evidence, but the proof target
is the ordered root-step simulation for arbitrary finite member lists.

## Proof status

The current root-indexed simulation in
`notes/design/2026-09-29-intrusion-abstract-semantics-draft.md` is an obligation,
not a theorem yet. Independent compiler review found that its minimum state
relation must include member root, `B_d`/fetch mode, birth levels, and `E_d`
lookup correspondence; otherwise projection congruence does not follow.
Failure simulation must distinguish attempt-local errors, round and inference
terminal latches, and the surface's default-root continuation, including
downstream public reporting. The draft now records these obligations. It still
does not establish the exact supported graph algebra, diagnostic/failure
observations, principal-solution preorder, or why an earlier saved view remains
equivalent when later root steps mutate shared state. The conditional
injective-renaming lemma begins after edge selection and does not prove these
properties.

## Next Gate C action

Define the polarized constraint denotation and principal-solution preorder,
then prove projection congruence and whole root-step simulation over the
declared envelope, including publication/finalization and incoming uses. Keep a
two-root characterization as optional diagnostic evidence; the bounded probe
did not find a valid witness, and no witness is required if the general ordered
simulation is proved. Preserve the source-envelope gap for any synthetic graph
evidence. Production representation remains gated on a reviewed successor
contract and explicit approval.

No compiler code or tests were changed or run for this source audit.
