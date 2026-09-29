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
such a two-root interaction.

## Proof status

The current root-indexed simulation in
`notes/design/2026-09-29-intrusion-abstract-semantics-draft.md` is an obligation,
not a theorem yet. It does not define the state relation between Oracle and
intrusion states, the exact supported graph algebra, diagnostic/failure
observations, the principal-solution preorder, or why an earlier saved view
remains equivalent when later root steps mutate shared state. The conditional
injective-renaming lemma begins after edge selection and does not prove these
properties.

## Next Gate C action

Construct a two-root graph-level Rust characterization in which both roots
share a variable and the first root's bounded post-loop phase adds an edge.
Record the first saved view, post-root state/epoch, second saved view,
diagnostics, and incoming-use observations. If a source-level witness is not
available, keep the source-envelope gap explicit; synthetic graph evidence
does not establish source-level Oracle parity. Use the fixture to define and
review the ordered root-step relation and solution preorder before selecting
the intrusion representation.

No compiler code or tests were changed or run for this source audit.
