# Cycle 256: actual capture aggregates and polarity

## Design gate (2026-11-18 12:36 UTC)

I50 remains current. The immediate missing connection is between actual finished
source inspection and the side-specific support checks used by fixed-basis
normalization. Uniform normalization of all consumer fields is not required by
I50; the earlier int diagnostic is not a counterexample to lo/hi normalization.

This cycle investigates the actual Allocation.lower/upper occurrence folds.
First derive nonempty occurrences for every declared input from Frame.prepared,
without a new language restriction or a desired-closure premise. Then prove
that lower-after-old-substitution has exactly the union atoms of the historical
lower endpoints, and upper has the intersection atoms of historical upper
endpoints. The nonempty fact removes artificial bottom/top support obligations.
This identifies the exact smaller historical endpoint obligations; it does not
silently discharge them for arbitrary traces. Initial identity snapshots should
satisfy these checks in the already fixed source/public basis, derived from
source endpoint membership rather than a stipulated aggregate support axiom.

Only new additive modules are planned. Existing source/runtime semantics and
frozen modules are unchanged. A checked preparation failure is a design
obligation, not source Rejected. Later historical mappings, cross-polarity
endpoint reuse, rows, persistent journal multiplicity, and strict-progress/Acc
remain separate obligations until proved. No packet compiler is to be declared
complete on the strength of these local aggregate lemmas.
