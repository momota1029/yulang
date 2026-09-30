# Recursive selector fixture: interval calculation

Date: 2026-09-30
Branch: `research/simple-sub-intrusion`
Reference: frozen Yulang2 Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Classification: fixture-level semantic calculation; not a Gate C proof

## Oracle observation

The Rust probe in detached worktree
`/tmp/yulang-intrusion-recursive-comparison-probe` prints the raw finalized
schemes for `ints` and `mixed`, alongside the nominal field-selector fixture
recorded in `2026-09-29-intrusion-oracle-ledger.md`. The focused command
`CARGO_TARGET_DIR=/tmp/yulang-intrusion-oracle-target cargo test -p infer --lib source_recursive_nominal_field_projection_probe -- --nocapture`
passed. Both root schemes format as `int -> step int 'a`; that formatter omits
the relevant recursive interval payload. The raw scheme bodies differ:

```text
ints:  q_inner lower = q_inner ∪ int;  upper = q_inner
mixed: q_inner lower = q_inner ∪ bool; upper = q_inner
```

More exactly, the raw `ints` scheme has quantifiers `q137`, `q138`, `q139`;
`q138` is the value identity in the inner `step`, and its `Bounds` node is
`Bounds(Union(q138, int), q138)`. The raw `mixed` scheme has corresponding
`q141`, `q142`, `q143`, with `q142` represented by
`Bounds(Union(q142, bool), q142)`. The separate productive recursive root
identity (`q137` / `q141`) has lower endpoint `q ∪ step(...)` and upper `Top`.
The selector call infers `int` for `ints_inner_value` and `bool` for
`mixed_inner_value`; lowering and check reports contain no diagnostics.

This separates the finite endpoint payload identity from the recursive-root
identity. It also shows why comparing only the formatted outer schemes would
miss an observable distinction. The recursive-call OCast `UnknownOrigin` result
remains a separate observation; the no-diagnostic selector result is not a
proof that arbitrary recursive nominal mismatches are accepted.

## Conditional interval calculation

For any preorder with a binary join `∨` satisfying its least-upper-bound law,
the interval obligation

```text
q ∨ c ≤ q
```

is equivalent to `c ≤ q`: one direction follows from the join's upper-bound
property `c ≤ q ∨ c`, and the other from `c ≤ q` plus `q ≤ q` and the least
upper-bound property. Its feasible values therefore have least element `c`
up to preorder equivalence, provided the carrier admits that assignment.
Applied locally, this predicts least inner values `int` and `bool` for the two
different payload intervals. This is an algebraic consequence conditional on
the interval's interpretation as the displayed subtype inequality.

The calculation does **not** establish that the Oracle's `Bounds` node denotes
exactly that satisfaction clause for the complete scheme, that the selector's
root projection returns this least value, or that the outer recursive interval
has a satisfying assignment in a chosen carrier. The exact connection from
source root preparation and selected evidence to the displayed interval is
also still an operational simulation obligation. Run-local root epochs,
selected compact intervals, and the fresh maps for the two external uses are
now captured in
`2026-09-30-intrusion-recursive-root-epoch-capture.md`. No recursive type
equation or equi-recursive comparison is used here.

## Required next proof

Close a fixture-level adequacy lemma by (1) defining the selected Oracle view
for each root at its actual root epoch, (2) giving the interval assignment and
the shared outer anchors, (3) deriving the fresh per-use instance relation,
(4) showing that the selector constraints expose the least `q_inner` value,
and (5) matching that calculation to the two public inferred results and
diagnostic observations. The source observation rules out any candidate
whole scheme/instance/projection pipeline that makes these two source uses
observationally indistinguishable. It does not yet show that the displayed
`q ∪ int` / `q ∪ bool` intervals are the necessary channel carrying the
difference, or select a carrier or prove principality beyond this fixture.

The actual selected roots and external-use maps are now observed for this
fixture, but the selector's induced subtype/projection obligations are still
not derived. The same run reports two `UnknownOrigin`-incomplete OCast
classifications with complete explanations, source leaves, and unknown-origin
variable-link edges, alongside the `int` / `bool` results and no diagnostics.
Both OCast producer heads are `step <: int`; the classifier sees a nominal
mismatch but cannot attach a source-boundary diagnostic. Keep the inferred
endpoint and diagnostic-eligibility calculations as separate obligations;
diagnostic silence does not prove all subtype constraints succeeded. Exact evidence is in
`2026-09-30-intrusion-recursive-root-epoch-capture.md`.

Envelope-wide soundness/principality, ordered root-step simulation, and
use-event simulation remain open. F5 scheme equivalence remains withdrawn as
the target; no compiler implementation follows from this characterization.

## Review

An independent compiler-referee review validated the conditional join
calculation and identified one overclaim about the specific interval nodes.
The text was narrowed to constrain the whole scheme/instance/projection
pipeline while leaving the necessity of those exact nodes open; delta review
confirmed closure. An independent spec-auditor review found no issue with the
charter's Gate C boundary or the stated F5 withdrawal. These reviews cover only
this fixture calculation and wording, not a concrete carrier, source-root
projection, or the full successor semantics.
