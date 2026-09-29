# Current task: prove and implement SCC-intrusion Function inference

Updated: 2026-09-29. Branch: `research/simple-sub-intrusion`.

## Objective

Prove that the SCC-intrusion redesign can match the frozen Yulang2 Oracle's
capabilities on an explicit supported input envelope, then implement the
replacement inference machine on this branch. F5 Function generalization and
closed schemes are to be removed from the target architecture. The user's
current objective authorizes completing the proof/design and implementation
work; unresolved semantic choices still need a reviewed successor contract
before code depends on them. Frozen Yulang2 `main` at `a58eefc3` remains the
observable reference. Do not modify frozen `main`.

## Inputs and existing contracts

- `notes/design/2026-09-29-scc-intrusion-generalization-sketch.md`
- `notes/design/2026-09-29-intrude-effect-hygiene.md`
- Existing F5 contract to supersede through an approved successor: `notes/design/2026-09-21-f5-general-function-scheme-foundation-draft.md`, especially §§8–9, 23, 25, and 33. It is not this redesign's acceptance criterion.
- The prior `yulang3` branch retains the in-progress F5c task state at parent commit `32f0a063`; its guarded-cycle measurement budgets are consumed as recorded in the linked plans/checkpoints there.

## Active gate

Replacement-design charter: `notes/design/2026-09-29-scc-intrusion-redesign-charter.md`.
The Oracle ledger is in
`notes/progress/2026-09-29-intrusion-oracle-ledger.md`. It now includes a
reproduced source-level identity used at both `int` and Function types, plus an
unproductive mutual-recursion result and the scheduler's forward-cycle
fixture. A nominal-guarded mutual Function SCC also yields one recursive bound
per member in a temporary Oracle probe. A local diamond probe also confirms
that an enclosing non-generic variable remains shared across two result paths
and is not quantified by the inner function. A source probe for a nested local
SCC sharing such an enclosing variable failed because sequential local `my`
declarations do not resolve the forward member reference; this exact graph
case remains open and needs an accepted source construction or graph-level
characterization. A pure Function guarded mutual cycle was also observed to
collapse to `any -> any -> never` for both members, without recursive bounds;
other cycle shapes remain open. The first Gate B candidate model is drafted in
`notes/design/2026-09-29-intrusion-abstract-semantics-draft.md`: immutable
frozen graph, boundary parent ports, outer identity preservation, and
per-incoming-use overlays. This turn added the Oracle's operational closure
rules for the pure graph fragment and corrected the candidate to one parent
per TypeVar with separate lower/upper edge transport. An injective-renaming
closure-commutation lemma is now stated with a proof sketch. A new Oracle probe
shows `pub k x = 1` projects to `any -> int` with no binders, so root projection
must eliminate one-sided exposures while preserving the shared component for
other roots. The audited Oracle path confirms projection is computed from
each member root at positive polarity, expands matching lower/upper bounds,
keys the collector cache by `(TypeVar, polarity, weight)` and recursion by
`(TypeVar, polarity)`, then erases one-sided variables and retains bipolar
identity. The small auxiliary model passes nineteen checks and
matches three recorded shapes, but is not implementation evidence. A narrow
Oracle-source lemma now states that injective parent renaming commutes with
root collection and one-sided elimination on an already scope-filtered,
ordered pure graph. A scoped compiler-referee review found no counterexample
under those assumptions and required the edge-selection boundary to remain
explicit. The lemma excludes the Oracle's other simplification passes, use
overlays, and principality. F5's Q/R shape, closed schemes, numbering, and
resource contract remain historical comparison points, not acceptance
criteria. A source audit now shows Oracle lower-edge selection itself depends
on proof records and support evidence, including replay pivots that carry type
variable IDs; copying selected structural edges alone is insufficient as a
full capability argument. Preselecting on the source graph is viable because
the Oracle collector consumes selected bounds after querying, but the query
round is recreated per root. Next compare carrying proof evidence with
freezing root-local selected-edge masks, including the freeze timing and
failure behavior, then specify root-view instantiation and prove the
composition against Oracle member uses before selecting the production
representation.

The reviewed pure-F5 protocol exposed a mistaken compatibility premise and is
retained only as historical review evidence. The new lifecycle obligations
derived from Oracle SCC scheduling are recorded in the ledger. The overall
goal is proof followed by implementation, not research-only completion.

## Stop conditions and next action

Before implementation, prove the candidate semantics for its declared graph
class and supported input envelope, then record the reviewed successor
contract. Stop or revise if it
captures an enclosing non-generic variable, merges distinct polarized
constraints, shares substitutions across independent uses, loses a recursive
bound, or changes Oracle-observable behavior inside the supported envelope.
Effect hygiene and runtime freshness remain a later separate gate.

Finite examples characterize the candidate but do not alone prove soundness or
principality. Do not run guarded-cycle resource captures: the current F5c plans
on `yulang3` have consumed their authorized runs. The immediate work is to
formalize the component/member-root denotation and use semantics, characterize
remaining open graph cases against the Oracle, then obtain independent review
of the intrusion simulation before choosing its production representation.
The Rust integration map is recorded in
`notes/progress/2026-09-29-intrusion-rust-replacement-map.md`: replacing only
F5 draft generalization is insufficient because publication, incoming-use
instantiation, and retained root projection are coupled. Further work should
use the actual Rust inference path as its characterization boundary; the
Python finite model is not implementation evidence and will not be expanded.
The abstract semantics draft now records a root-local preparation protocol
from the frozen Rust Oracle: each member view gets an independent projection
round/query per compaction attempt and lazy edge selection, while component-wide
preselection remains unproved. Independent review caught and corrected claims
about atomic Oracle publication, shared snapshots, error scope, and record
ordering. Next characterize member views and use overlays at `yu-solver`'s
Rust solve boundary; exact query behavior needs source proof or instrumentation.
Implementation remains gated on successor design approval.
