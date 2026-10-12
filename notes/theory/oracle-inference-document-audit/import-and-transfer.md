# Imported base and transfer boundaries

Date: 2026-10-12
Status: bounded historical document audit independently reviewed; no parent theorem closure
Oracle baseline: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
No implementation authority or Yulang theorem closure

## Published Simple-sub base

The Oracle spec index explicitly identifies Parreaux (2020) as the inference
base. Its stored Marker conversion is a reading aid, not an additional proof.
The already independently reviewed
[original-source import](../2026-10-11-parreaux-simple-sub-proof-import.md)
pins the official paper and permanent local reference copies. Its proof
coverage must also constrain historical claims that invoke “the usual
Simple-sub proof.”

The paper §5 states declarative soundness and completeness/principality for
the non-let-polymorphic fragment. Lemmas 1–5 concern inference, constraining,
termination and completeness. It supplies sketches and describes stronger
cache/consistency hypotheses; full auxiliary proofs and mutable/immutable
equivalence are omitted. Polymorphic let implementation appears in §3.5,
but let correctness is suggested separately in footnote 15, not proved by
§5's theorem. This is a scope boundary of the imported result, not a reason
to discard its algorithm or redo ordinary lambda/application derivations.

The Oracle complete draft lines 1973–1987 invokes ordinary coalescing for
weighted compact extraction; lines 1999–2003 and 2042–2045 invoke a
generalization lemma. Neither citation supplies the extension proof for
weighted bounds, filters, row variables, static IDs, fresh runtime colors,
levels or outer nongeneric sharing. Those translation premises must be
independently established before the published base is applied.

## A small reusable semantic kernel: interval compatibility

The Oracle role spec is the definition owner for the cross conditions.
The invariant-sandwich spec inherits them; its center is display notation,
not an independently owned identity. Freeze the mathematical claim separately
from the collector's implementation:

For a lattice of interpreted types, suppose intervals `(L1,U1)` and
`(L2,U2)` are individually consistent: `Li <= Ui`. They have a common
admissible argument precisely when both cross conditions hold:

```text
exists X. L1 <= X <= U1 and L2 <= X <= U2
    iff L1 <= U2 and L2 <= U1.
```

Necessity follows by transitivity through the same X. For sufficiency take
`X = L1 join L2`. The self and cross inequalities imply `X <= U1` and
`X <= U2` by the defining property of join. Equivalently the merged interval
is `(L1 join L2, U1 meet U2)`. This finite derivation justifies the semantic
cross conditions under the stated lattice/consistency premises. It does not
prove a collector constructs all required comparisons, that their memo key
is complete, or that family/argument substitutions remain correlated.

The spec's structural lifting, co-occurrence, secondary-variable treatment,
same-slot recollection and cancellation-side family retention are separate
claims. Their correctness does not follow from interval compatibility.
Function arguments must flip polarity; argument effect, result effect and
result value are additional ports. Reuse of the kernel is conditional on
proving the selected interpretation provides joins/meets and retaining one
shared argument. It is not an all-model intrusion equality theorem.

## Historical graphs and current intrusion

There are at least three different graph domains in the documents:

1. weighted row/constraint paths used for source-cycle balance and solver
   termination in the June research calculus;
2. resolved binding references with `BindingFetch` in the June 13 value
   restriction spec (parent/target `DefId` and separately `use_value`);
3. the current approved graph of semantic values and actual value references,
   with type-occurrence associations, used to qualify extrusion parent/copy
   intrusion.

Neither a common word “SCC” nor a physical bound walk identifies these graphs.
The current [association clarification](../../design/2026-10-12-intrusion-value-type-association.md)
is explicit: qualifying associated values need not be newly allocated type
copy vertices, and arbitrary same-component types are not equated. Historical
row-cycle balance can support a termination proof only after a proven
translation to its own graph; it does not prove intrusion equality preserves
soundness or principality. The June reference metadata is useful evidence for
source identity ownership, not an automatically selected port-association rule.

## Generalization and execution boundary

The June 13 `computed-fetch-value-restriction` spec distinguishes evaluating
a function body from retrieving its function value. `FetchComputation` cannot
quantify RHS computation variables, including role inputs, effect residuals
and annotation-associated variables. Multiple-root recursive components
with an internal computed fetch are rejected; ordinary mutually recursive
function values are allowed. The spec does not prove the combined theorem.

Its operational binding-fetch interpretation is not interchangeable with
the research draft's stated CBV mini-language let. A failing mini-language
rule must be reported in that model, without inferring an Oracle compiler
bug. Conversely a production value-restriction rule cannot silently supply
a missing premise of the mini-language theorem.

Oracle `spec/2026-06-13-runtime-guard-markers.md` at the pinned anchor,
lines 48–50, 66–81, 117–149 and 214–231, owns the following protocol.
Its `frame_id` has resumable dynamic-wind semantics.
`add_id` snapshots the entry guard list, transports delayed markers through
function/thunk/structure shapes and avoids repainting requests already hidden
at entry. Therefore the hygiene dependency is a conjunction:

```text
weighted inference interpretation
  + joint scheme/ID instantiation
  + specialization evidence and marker materialization
  + runtime entry snapshots, unwind and resume
  => source handler hygiene.
```

The toy normalized-colored theorem excludes thunk/force, family type arguments
and additional constructors. A valid theorem for that model remains useful;
its extension to the production protocol and current contextual attachments
requires explicit simulation and transport proofs. Public erasure adds a
separate generality-order and future-use obligation. The June 23 explanatory
brief itself explicitly leaves public projected principality, replay-cycle
subsumption and full implementation-graph termination open.

The June 23 brief is Oracle `docs/effect-inference-brief.md`, lines 113–130
at the same anchor.

## Audit limits

This note uses pinned document definitions and the reviewed original-paper
import. It does not use execution traces as a specification, change code,
run tests, or certify the old integrated theorem. Detailed historic proof
steps and repairs are owned by the other audit reports. A fresh independent
`compiler_referee` checked the interval kernel and transfer boundaries with no
blocking or major findings. Its optional navigation finding is repaired by the
exact locators above. The review certifies the bounded derivation and accurate
scope, not any original Oracle/current Yulang parent theorem or implementation.
