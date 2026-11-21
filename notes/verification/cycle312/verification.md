# C312 focused Lean verification

Lean 4.35.0, LEAN_NUM_THREADS=1. No repository-wide build, Rust run or CI assertion.

1. From lean/: lake build --wfail <the 29 added Yulang module names listed below>.
Build completed successfully (1502 jobs).

2. From lean/: lake env lean --trust=0 -DwarningAsError=true <each source or independent audit>.
PASS source Yulang/GeneralFiniteTypedWrites312.lean
PASS source Yulang/GeneralVersionedAliasCenters312.lean
PASS source Yulang/GeneralVersionedAliasChoice312.lean
PASS source Yulang/GeneralVersionedAliasHeadWrites312.lean
PASS source Yulang/GeneralVersionedAliasReadback312.lean
PASS source Yulang/GeneralVersionedAliasReport312.lean
PASS source Yulang/GeneralVersionedBinderReuse312.lean
PASS source Yulang/GeneralVersionedBinderTable312.lean
PASS source Yulang/GeneralVersionedBinderTargets312.lean
PASS source Yulang/GeneralVersionedCurrentFrame312.lean
PASS source Yulang/GeneralVersionedEqualChildCenters312.lean
PASS source Yulang/GeneralVersionedForwardedJoint312.lean
PASS source Yulang/GeneralVersionedForwardedWrites312.lean
PASS source Yulang/GeneralVersionedHarmlessRefresh312.lean
PASS source Yulang/GeneralVersionedHistoricalJoint312.lean
PASS source Yulang/GeneralVersionedHistoricalTransport312.lean
PASS source Yulang/GeneralVersionedIdentityCenters312.lean
PASS source Yulang/GeneralVersionedJointWriteExact312.lean
PASS source Yulang/GeneralVersionedJointWrites312.lean
PASS source Yulang/GeneralVersionedProtectedLookup312.lean
PASS source Yulang/GeneralVersionedProtectedName312.lean
PASS source Yulang/GeneralVersionedProtectedPeer312.lean
PASS source Yulang/GeneralVersionedRecursiveReducers312.lean
PASS source Yulang/GeneralVersionedReservedOther312.lean
PASS source Yulang/GeneralVersionedRootWrites312.lean
PASS source Yulang/GeneralVersionedSelectedJointHead312.lean
PASS source Yulang/GeneralVersionedSelectedJointWrites312.lean
PASS source Yulang/GeneralVersionedSemanticPeer312.lean
PASS source Yulang/GeneralVersionedSiteOrigins312.lean
PASS standalone Audit/Cycle312AliasChoice.lean
PASS standalone Audit/Cycle312Forwarded.lean
PASS standalone Audit/Cycle312JointWrites.lean
PASS standalone Audit/Cycle312ProtectedPeer.lean
PASS standalone Audit/Cycle312RecursiveReducers.lean
PASS standalone Audit/Cycle312Surface1.lean
PASS standalone Audit/Cycle312Surface2.lean
PASS standalone Audit/Cycle312Surface3.lean
PASS standalone Audit/Cycle312Surface4.lean
PASS standalone Audit/Cycle312Surface5.lean
29 modules, 169 explicit public declarations
215 declaration checks, including 3 axiom-free; nonstandard axioms: []

3. From repository root: tools/verify-lean.sh checkout d89b3bee3 --no-build, on 8b715ff94; all Lean changes frozen at that pin.
Independent git diff --check and exact same-publication barrel check before publication.

4. From lean/: lake env lean --trust=0 -DwarningAsError=true ../notes/verification/cycle312/probe.lean.
PASS: established C311 source fixture: nonleaf parent and route match forwarding; actual non-replay peer raw report obtained from historical alias in every live model.
'Yulang.Cycle312ActualProbe.root_forwarded' depends on axioms: [propext, Quot.sound]
'Yulang.Cycle312ActualProbe.route_forwarded' depends on axioms: [propext, Quot.sound]
'Yulang.Cycle312ActualProbe.current_raw' depends on axioms: [propext, Classical.choice, Quot.sound]
