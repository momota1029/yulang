# Cycle240: I45 point-preserving reobservation

The old 239 accessibility target remains refuted and stopped. I45 explicitly
chooses a successor rule: preserve literal descriptors already point-determined.
We test its blocking effect without changing any published fixture or semantics.

First claim: for every family index, bookkeeping and prior raw state, the old
FamilyRevision238 revision changes the already-point root descriptor at slot 3.
Its old anchor is the embedded anchor n, its new anchor is anchor (n+1), which
are distinct finite slots. Hence the new Preserves guard fails. This is not a
claim that every future revision, every new Step or every infinite run is blocked.

Progress analysis must distinguish finite reobservation on a fixed slot set from
Refresh growth, new descriptor installation and aggregate version growth. No
finite-version or total-accessibility conclusion follows from one loop rejection.

## Nonpoint-root counterexample-first test

`GeneralDictionaryVersionLoopLooseRevision240` constructs, for each n>0,
a local revision with root Pair((embed(anchor n), original 2), repeated).
Both endpoints denote Foo(Int) in the former family model but are distinct slots.
The revision changes the first endpoint to anchor(n+1), keeps original 2 fixed,
and turns the new last Foo(0,1) descriptor into Foo(0,0). The formal Preserves,
Improves and root_changed proofs are compatible. This is NOT a source-reachable
counterexample to the new target: the new raw-back/cache/Frame/Step certificates
and the source iteration are not supplied.

A plausible source-starting variant needs five original slots: 0/1 Int,
2 Foo(0,0), 3 Pair((2,4),(2,4)), 4 Foo(0,0). Its root is nonpoint from the
start, yet every original model forces both endpoints to Foo(Int), so the
existing ground-root semantic condition appears applicable. Subsequent capture
bindings repeat (lower_n,4), rather than (lower_n,lower_n). Aggregate lower
can remain the new version anchor while the literal upper stays source4.

Required unproved bridges: new names injectivity/version separation for repeated
(lower_n,4); raw snapshots/refinements preserving all existing descriptors;
inspection/Finished/head/schema/fullHolds and no-cycle guards for interval
captures; trusted history raw-back from new installation equations; point-safe
revision certificates; Fresh and future-upper patched models; actual source
Initial plus indexed guarded install/refresh/reobserve recursion. None of these
may be replaced by desired reachability or finite-support assumptions. In
particular the local syntactic test alone neither refutes Acc nor validates an
infinite actual execution. It does show that I45 alone does not imply literal
stability of descriptors that remain nonpoint.

## Verified concrete successor prefix

The five-slot proposal above is now instantiated in LooseLoopSource240 and
Initial240. The initial boundary is PointSourceBoundary240, with its actual
source formation, GroundRoots, checked declaration and a concrete model.
Packet/Frame/Full/Safety/Install240 establish the full guarded first install,
not a lifted assumed state. RefreshBase/Refresh/Retarget240 expose lower_1 as
slot5 Foo(0,1), then revise it to Foo(0,0) while changing root bounds (2,4) to
(5,4). The old root is nonpoint; original point Foo descriptors at 2 and4 stay
literal. The new Preserves guard holds. Prefix240 proves the real three-step
source path, reachability, a surviving full model and actual root change.
This finite prefix does not prove new target falsity.

## Uniform reobservation layer

LooseFamilyRefines/Revision/Back/Installation/Expose/History/Trusted/Cache/
Refresh/Reobserve240 port the guarded observation layer. All arbitrary carrier
models are preserved through exact raw-back/cache proofs. The source-fixed
upper endpoint4 is semantically Foo(Int) from original source, and only the
lower aggregate chain is needed for history. Revision.preserves excludes the
nonpoint root and newly exposed loose Foo from its preservation obligation,
while proving every old point descriptor unchanged. The actual PointKernel
reobserve constructor is used, with its new guard, not erased old steps.

These uniform certificates explicitly require current=replay(plan_n), original
source and all prior plans recorded. They do not assume or conclude these
histories exist for all n. Indexed source states, common-model induction,
future upper novelty and every install guard must still be constructed by
separate modules before any infinite-trace/Acc assertion is justified.

## Final status: actual uniform obstruction closed

The previously open bridges above were subsequently closed in the 240 family
and LooseIteration modules. Book/Frame/Fresh/Safety/Install/Round establish all
guards; Support/Patched/Stage preserve future-upper novelty witnesses; Iteration
constructs every reachable stage. Nontermination proves initial_no_acc and
no_saturation/no_statement for the actual PointSourceBoundary240. Thus the
finite-prefix caveats above describe intermediate stages, not the final result.
Research stopped on the closed obstruction; no semantic repair was implemented.
See the cycle240 question note for the exact scope and required decision.
