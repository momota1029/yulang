# C311 Lean verification

Using Lean 4.35.0, LEAN_NUM_THREADS=1. Did not complete a repository-wide build.

1. From lean/: lake build --wfail <the 19 added Yulang module names listed in source results>.
Build completed successfully (2454 jobs).

2. From lean/: lake env lean --trust=0 -DwarningAsError=true <source or standalone audit> individually.
PASS source Yulang/GeneralLatePeerCurrent311.lean
PASS source Yulang/GeneralLatePeerDirectInstall311.lean
PASS source Yulang/GeneralLatePeerDirectPlan311.lean
PASS source Yulang/GeneralLatePeerFinalPeerPlan311.lean
PASS source Yulang/GeneralLatePeerFirst311.lean
PASS source Yulang/GeneralLatePeerFresh311.lean
PASS source Yulang/GeneralLatePeerGuard311.lean
PASS source Yulang/GeneralLatePeerJoint311.lean
PASS source Yulang/GeneralLatePeerMerge311.lean
PASS source Yulang/GeneralLatePeerRecursive311.lean
PASS source Yulang/GeneralLatePeerRoot311.lean
PASS source Yulang/GeneralLatePeerRouteInstall311.lean
PASS source Yulang/GeneralLatePeerRoutePlan311.lean
PASS source Yulang/GeneralLatePeerSource311.lean
PASS source Yulang/GeneralLatePeerTransfer311.lean
PASS source Yulang/GeneralPeerInstallationOrder311.lean
PASS source Yulang/GeneralVersionedAggregatePeer311.lean
PASS source Yulang/GeneralVersionedCenteredReplay311.lean
PASS source Yulang/GeneralVersionedPeerChoice311.lean
PASS standalone Audit/Cycle311ActualTransfer.lean
PASS standalone Audit/Cycle311LateRoot.lean
PASS standalone Audit/Cycle311Merge.lean
PASS standalone Audit/Cycle311PeerChoice.lean
PASS standalone Audit/Cycle311RecordedPeer.lean
PASS standalone Audit/Cycle311Recursive.lean
PASS standalone Audit/Cycle311Surface1.lean
PASS standalone Audit/Cycle311Surface2.lean
PASS standalone Audit/Cycle311Surface3.lean
PASS standalone Audit/Cycle311Surface4.lean

19 modules, 302 explicit public declarations
PASS: 340 declaration checks, counting targeted repeats, including 18 axiom-free.
Only propext, Classical.choice and Quot.sound; nonstandard axioms: none.

3. From repository root: tools/verify-lean.sh "$PWD" c73b9ce54 --no-build ran against eaea3c8c2. Full output in diff-*; only notes/logs changed afterwards.
Separate git diff --check and exact end-barrel checks run before publication.
