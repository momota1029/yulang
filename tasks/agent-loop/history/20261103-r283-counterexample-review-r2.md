# R283-R2 clean review — CLEAR for the candidate predicate only

Reviewer: `/root/r283_counterexample_clean_review_r2`, registered
`parent_edge_auditor` (profile-fixed Sol). Fresh read-only review; 450s grant
charged in full. No descendants, writes, builds/cache access, checker rerun,
tests, Rust, Cargo, probes, Git or continuing processes.

## Authentication and sequence

- Contract-only WAITING identity/hash matched:
  `tasks/agent-loop/sprints/extrusion-row-validity-r283-review-r2.md`,
  SHA-256 `aa72f665f4d2f99746fdf764a758824ac69c246f21b67f9448378b3baef17ecf`.
- After Luna GO, the reviewer’s first technical operation hashed the explicit
  manifest and all 16 exact technical paths. All matched. Manifest:
  `tasks/agent-loop/sprints/extrusion-row-validity-r283-review-r2-inputs.json`,
  SHA-256 `1a6f485ba1e48dc0b351d644d32803a70cbe485aa5793538ab811cc732b409e5`.
- The independent review inspected `incomingJobs`, `copiedRow`, `step`, and
  `runPrefix` before opening the candidate module and handoff.
- Frozen candidate module SHA-256:
  `31c83006c8d9b411b00d045fd16c9e5875e8a73d5baead989c7a55315f3a3f10`.
  Frozen handoff SHA-256:
  `63e79d8e52243eccd6e83ddf4eef4c11d72e40e91a3f0fcea551e58084b72428`.
  Governing `OriginalExtrusionWork.lean` SHA-256:
  `c419675d75a2cdf03fe5b1ba8d2eef106fea0c4f5187f9f5c06999fa734edd58`.

## Narrow disposition: valid counterexample to this `RowsValid`

`RowsValid` checks the operation root, canonical representatives, stored row
vectors and atoms, cell and child-term references, memo keys/images, all eight
Work constructors in queues, tuple ports, Parents, and pending Parent indices.
It omits `State.captures` incidence sources.

For any caller, `captureGap caller` satisfies that exact predicate. In the
concrete `gapCaller` state there are two valid Value rows and one Effect row;
the capture contains source row 99. Funding the real `step` allocates Effect
row 1, links it, and `incomingJobs` queues a positive Effect Visit for row 99
at target 1. The resulting Effect vector has length 2, so row 99 is outside
it. The pending Work projection checks the required row bound. The transition
returns `.next`.

The exact model declarations are:

```lean
StepPreservesRows :=
  ∀ (funds : Funding) (s : State), RowsValid s →
    RowsValid (resultState (step funds s))
RunPrefixPreservesRows :=
  ∀ (funds : Funding) (fuel : Nat) (s : State), RowsValid s →
    RowsValid (resultState (runPrefix funds fuel s))
```

The kernel-checked negations instantiate the same `funded` state; the prefix
counterexample uses fuel 1, whose result is definitionally the one-step `.next`
state. `resultState` and its three audited equations exhaustively project
`.next`, `.external`, and `.failed` to their state fields.

The frozen handoff prints and the reviewer matched these complete theorem
types and axiom results:

| Declaration | Printed conclusion/type | Axioms |
|---|---|---|
| `resultState_next` | `∀ s, resultState (.next s) = s` | none |
| `resultState_external` | `∀ s call, resultState (.external s call) = s` | none |
| `resultState_failed` | `∀ s error, resultState (.failed s error) = s` | none |
| `captureGap_valid` | `∀ caller, RowsValid (captureGap caller)` | `propext`, `Quot.sound` |
| `captureGap_pending_bad` | row-99 positive Effect Visit belongs to resulting `pendingBounds` | `propext` |
| `captureGap_effect_count` | resulting `effects.length = 2` | `propext` |
| `captureGap_step_invalid` | negation of `RowsValid` on the funded step result | `propext` |
| `step_preserves_rows_counterexample` | `¬ StepPreservesRows` | `propext`, `Quot.sound` |
| `runPrefix_preserves_rows_counterexample` | `¬ RunPrefixPreservesRows` | `propext`, `Quot.sound` |
| `computed_rowInput_valid` | `∀ caller, RowsValid (Computed.rowInput caller)` | `propext`, `Quot.sound` |

These are the full axiom sets from the frozen `#print axioms` output; no
`Classical.choice` is reported. The reviewer did not rerun Lean because no
checker/cache rerun was assigned. The 16-input scan found the import graph
terminates at `Std`; no project `axiom`, `sorry`, `unsafe`, or kernel-skip
declaration appeared in the inspected cone scan. This is a review of the
authenticated producer output, not a new independent kernel run.

`computed_rowInput_valid` follows for the explicitly constructed two-effect
row input with identity maps and empty remaining stores. It does not establish
preservation along the three-step `row_bound_produced` prefix.

## Limits and parent status

The first missing preservation premise is a storage invariant covering
capture-derived canonical source references emitted by `incomingJobs`, with
source-row validity and closure under canonical maps, plus independently
established initialization and mutation maintenance. This predicate’s
counterexample refutes its universal step and prefix preservation claims only.

Preservation remains open for the other seven Work constructors, other Visit
branches, external yields/resumptions, funding failures, and partial
publication before failure. The local equations do not close those cases.
No accepted source assignment, synthesis/written-target/final-root
correspondence, contextual checking/conversion coverage or shared source
witness is established. Source-language reachability, Rust initialization and
mutation correspondence, original R70 W, and production readiness remain
open.

**Parent-edge delta: 0→0.** Original A/B and R70 are not closed or refuted.
`NO_SAFE_CODE_SLICE` remains. No capture-closed proof is admitted by this
review. Luna retains adjudication and any later sprint selection.
