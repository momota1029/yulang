# Current task: prove and implement SCC-intrusion Function inference

Updated: 2026-09-30. Branch: `research/simple-sub-intrusion`.

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
other cycle shapes remain open. The first Gate B candidate is in
`notes/design/2026-09-29-intrusion-abstract-semantics-draft.md`: parent ports,
outer identity preservation, and independent use overlays. It includes Oracle
closure rules for a pure graph fragment and an injective-renaming lemma after
edge selection. A source audit found that lower-edge selection depends on
projection evidence, and that each member root is generalized sequentially;
root prepasses may advance the constraint epoch, while bounded post-loop passes
can mutate the solver without restarting the saved root result. The draft now
models a candidate versioned shared graph and states a root-indexed simulation
theorem rather than assuming one frozen snapshot or one equal internal graph.
This candidate remains unapproved. F5's Q/R shape, closed schemes, numbering,
and resource contract remain historical comparison points, not acceptance
criteria. The earlier auxiliary Python model has been removed from active
artifacts; its outputs are withdrawn as evidence.

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
close independent semantic/spec review of the sequential root-transition
candidate, then prove the pure root/use simulation and characterize open cases
through Rust's real solver path before selecting a production representation.
The Rust integration map is recorded in
`notes/progress/2026-09-29-intrusion-rust-replacement-map.md`: replacing only
F5 draft generalization is insufficient because publication, incoming-use
instantiation, and retained root projection are coupled. Further work should
use the actual Rust inference path as its characterization boundary; previous
Python-model outputs are withdrawn and cannot establish any Gate B/C claim.
The abstract semantics draft now records a root-local preparation protocol
from the frozen Rust Oracle. Source review found that component roots are
generalized sequentially, may mutate/restart at a later constraint epoch, and
can apply bounded post-loop constraints after the saved root result. The draft
replaces its single-snapshot premise with a candidate versioned shared-graph
transition and a root-indexed observable simulation theorem. Compiler-referee
and spec-auditor reviews of this lifecycle delta found and closed the epoch,
root-order, state, failure, and record-sync findings; they did not certify the
principality theorem or authorize implementation. A subsequent Oracle audit
found per-member `FetchValue`/`FetchComputation` boundaries: the same
identity-Function graph shape is generalized under FetchValue and retained as
a unit-boundary identity under FetchComputation in separate sessions. If a
mixed-fetch topology sharing one TypeVar is admitted within one SCC, a
synthetic graph refutes one component-wide quantification bit; the accepted
source witness is not established and computed-fetch cycles can diagnose. The
draft now proposes member-indexed
`Gen_d`/`P_d`, separates surviving free vars from erased variables, and adds
`Cycle_d` freshness through one source-identity map `Phi_d`. Independent
compiler-referee and spec-auditor reviews found no remaining blocking or major
issue in this parent-port/recursive-freshness delta; they support the evidence
distinctions but do not prove port selection or principality.
The latest Oracle source audit confirms that the root-indexed simulation is
still only an obligation: the state relation, principal-solution preorder,
supported graph algebra, diagnostics, and earlier-view stability are
undefined. A bounded synthetic-graph probe against an isolated frozen-Oracle
checkout found no valid two-root post-loop witness; it does not show those
mutations are redundant. Independent compiler review also required the
simulation state to include each member root, `B_d`/fetch mode, birth levels,
and `E_d` lookup correspondence, and to distinguish attempt-local query errors,
terminal latches, and surface default-root continuation. The draft now records
these obligations. Exact lifecycle observations and locators are in
`notes/progress/2026-09-30-intrusion-root-transition-audit.md`; the denotation
split and unresolved semantics are recorded in
`notes/progress/2026-09-30-intrusion-denotation-boundary-audit.md`. The next theorem
layer is split: define satisfaction and principality for an already-selected
regular member graph, then prove Oracle root/epoch projection and use
preparation produces a graph in that model. The draft now proposes an exact
principality criterion: the sound-and-complete member relation is the upward
closure of root values from satisfying local assignments, fibered over fixed
environment assignments. The multi-use relation retains each use's root result
and use-site constraints, with disjoint local assignments under one shared
environment assignment. The carrier, subtype order, and finite-scheme
representability remain open. A conditional lemma proves `Top` erasure for an
unconstrained negative-only Function argument under greatest-Top and
contravariant Function assumptions. A focused frozen-Oracle Rust-path probe
now confirms the premise for the `pub k x = 1` witness: its first compacted
Function argument is `TypeVar(2)` with no stored bounds, and the saved compact
argument is empty. This does not prove the general erasure/projection rule.
The bounded negative-argument source case is now characterized: when
`k x = expect x` constrains the argument to `int`, Oracle's first compact view
contains both the argument variable and `Int`, and the saved scheme is
`int -> int`. The conditional counterexample and reviewed pointwise
extremal-projection lemma show that a bounded variable projects to its greatest
admissible upper type, not automatically to `Top`. Review found the
source-level singleton-bound argument insufficient as a general Oracle
theorem: eligibility, weighted aliases, rows, lower obligations, and anchors
still matter. Establish the exact correspondence for an explicit graph class,
then continue with ordered root-step simulation,
publication/finalization, and use simulation. A two-root characterization
remains optional diagnostic evidence. A conditional lemma now shows that
injective fresh-parent renaming bijects solution assignments when finite
endpoints evaluate variable/back-edge references by direct lookup, while
keeping `E_d` anchors fixed. Recursive unfolding, root projection, and
principality remain unproved.
The first
two focused `yu-solver` Rust-path baseline
probes pass for current identity-Function and productive/unproductive recursion
behavior; they inspect F5-backed views only and are not intrusion or Oracle
equivalence evidence. The exact tests and limits are recorded in
`notes/progress/2026-09-29-intrusion-rust-replacement-map.md`. A focused attempt
to run the exact Oracle identity-use source through Yulang3 failed during HIR:
expression application and backslash lambdas are unsupported. The temporary
failing test was removed. Gate C can use a test-only semantic batch for graph
and independent-use characterization, but that cannot prove source-level
parity. Gate E must include expression application in the source envelope or
record it as a compatibility delta; a broad Oracle-capability claim requires
the source path. The abstract semantics now has a reviewed conditional lemma:
injective per-use renaming preserves finite closure, and raw use edges share
only through `E_d`; closure-derived cross-use edges through `E_d` are explicitly
allowed. This proves neither solution-space independence nor principality.
Details and review limits are in
`notes/progress/2026-09-30-intrusion-factorization-proof.md`. A Rust-only
synthetic incoming-use characterization now exercises two distinct incoming
IDs with different Function constraints through the current route. It directly
observes shared argument/result identity within each use and distinct exposed
live identities across the uses. It does not establish general graph-edge
isolation, intrusion semantics, or principality. Review scope and the focused
command are recorded in
`notes/progress/2026-09-30-intrusion-rust-use-characterization.md`. General
graph isolation remains another open Gate C obligation. This witness is
current-path characterization, not intrusion correctness or source-level
Oracle parity.
Implementation remains gated on the reviewed successor contract and explicit
user approval.
