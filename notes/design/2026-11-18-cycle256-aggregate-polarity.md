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

## Actual replay family follow-up (12:41 UTC)

For the already source-reachable I45 loose-iteration family, inspect the stored
lower equations rather than substitute an arbitrary invented environment.
Each replay retains the earlier ordinary atoms and adds the actual equation
`lower(n+1) = lower(n) union lower(n)`. Consequently every model of stage n,
not only its designated witness model, makes lower(n) equivalent to initial
source 2. Actual captures are repeated `(lower(n),4)`, so their aggregate Fits
may be represented by the one fixed pair `(var 2,var 4)` in every stage model.
This is a concrete all-index semantic collapse of a known problematic family.
It is not an all-assignment unconditional syntactic normalization, does not
rewrite the source kernel, and cannot contradict the existing I45 no-Acc proof.
It does not by itself normalize old/current consumers or certify a new trace.

The family follow-up will also retain a finite syntactic list of its actual
lower equations in replay order. This list is explicitly a projection of the
source ordinary history, not the entire old snapshot or an executed successor
compiler. Ordered expansion of its current lower endpoint gives a duplicate
union tree over initial var 2; endpoint 4 stays literal. The actual incoming
capture fold can therefore pass the checked preparer on the single fixed pool
`[var 2,var 4]` for every index. Membership of the projected equations in real
reachable source history is required, so this is stronger than the toy raw2
loop, but does not establish arbitrary source closure or full-view rewriting.

## Verified at first follow-up checkpoint

The six initial lemmas/modules passed independent read-only scope review.
The four follow-up modules connect the actual all-index I45 reachable family:
`history n` is a projection whose equation block is included in actual retained
ordinary atoms; its current expansion is a duplicate union tree over var 2.
The actual capture fold passes preparation on `[var 2,var 4]` for every n and
returns the constant representative. The same pair has exactly the source
capture Fits meaning in every model of stage n. The pool is contained in the
fixed initial source/public basis and has no allocated private name reads.

This is a regression for one genuinely reachable family, not arbitrary-source
closure. The old point-preserving Step still has its previously proved infinite
path and grows slots to n+5; normalization of an observable pair alone does not
change that Step. A no-change-revision guard and whole-consumer preservation are
still required before a new Acc argument. Usage explicitly imports the old
no-Acc theorem alongside the new constant-representative theorem to keep those
claims separate. No new counterexample to a completed successor is asserted.
