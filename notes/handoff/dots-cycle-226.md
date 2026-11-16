# Cycle226 — reachable relative packet support

Started 2026-11-16 22:36:14 UTC (scheduled22:30, delayed dispatch).
User's25min limit and parent22:55UTC deadline override historical55min text.
Fetched integration/m1-final a921616b3 and reread standing orders plus inbox
I-41/I-42 (ACTIVE). Local merge de231941c incorporated I42; no locally authored
plan/spec change. Verified existing work/dots-main5123fed6 includes220/222–225;
no duplicate recovery publication. Previous heartbeat225 was completed with its
combined report. No competing Lean build/writer observed.

## Results

Four new modules,48 constants audited. Auxiliary progress, not EvidenceNode.

* RelativeProvenance226: for every plan, ordinary head atom sources lie in its
  base slots plus only its own declaration's allocated p0/p1 input targets.
  A source absent from the observed pool but read by the relative head must be
  one of those targets. No assumption of arbitrary trace freshness.
* ReadProjection226: for every report and assignments agreeing on anchor/capture
  bounds and actual report origins, ProjectionModels is equivalent. Unlike224,
  unrelated base slots are not protected. Cross/merge/self-check sources use
  only capture/checked bounds plus local targets. Empty report support is empty
  and its projection is valid for every assignment, regardless of base slots.
* ReadPacket226: transports the exact total packet relative to two old-context
  models using this smaller read support; transfers journal Depends through
  installation. It retains all old constraints semantically. Other-declaration
  raw-head sources must already be in the actually observed support.
* ReachablePacket226: for InitialSource, point root arguments, ground roots,
  coverage, a reachable path and current Frame, total packet transport between
  two journal models needs only merge-atom sources plus the unchanged non-head
  packet sources. Rest/headSchema transport derives actual Agreement on both
  sides; CountedRawHead216 then discharges cross/self-check/projection. The new
  install_depends obtains Frame from actual Installable. No packet existence,
  Agreement or Overlap conclusion is assumed. Old/new live effects remain in
  the installation delta.

This removes raw projection/cross/self-check overprotection from the reachable
installation delta, rather than merely making those lists smaller. It does
not prove protected Overlap, whole-trace p0/p1 provenance, common-model
existence, or the unconditional V8 EvidenceNode. B4 still has that open field.
No new language decisions or candidate restrictions. No Yulang2 execution.

## Verification

Commands in lean/, with Lean4.35 toolchain:

- lake build Yulang.GeneralDictionaryRelativeProvenance226 --wfail: PASS1147jobs.
- lake build Yulang.GeneralDictionaryReadPacket226 --wfail: PASS1149jobs.
- lake env lean --trust=0 Audit/Cycle226Provenance.lean:
  CYCLE226-PROVENANCE-PASS:37 constants in3modules,exit0.
- lake build Yulang.GeneralDictionaryReachablePacket226 --wfail: PASS1337jobs.
- lake env lean --trust=0 Audit/Cycle226Reachable.lean:
  CYCLE226-REACHABLE-PASS:11 constants in1module,exit0.

Only changed modules built; job counts include the dependency graph/cache.
The audit scans every new-module constant and rejects dependencies outside
propext/Classical.choice/Quot.sound. Full repository gate not run, per standing
orders; no CI pass claimed. Intermediate compile errors (Bounds namespace,
source reduction and generated proof text) were corrected before publication.
No new proof holes, axioms or native_decide. git diff --check passed.
Audit.lean/README unchanged from verified5123fed6 freeze repair; old Lean
modules unchanged; Yulang.lean imports only appended. New audits are small
separate files. No modification of previous audit files.

## Publication and next work

Start heartbeat27611646; checkpoint07b8b853 published6files and its fetched tree
a45606e7 matched. Ten-minute heartbeat21461c4e. Final publication contains all
four modules, both audits, design/report and completed heartbeat; no held files.
Final remote SHA/tree verification is reported by the parent after API completion.

Next: provenance/semantic redundancy for non-head schema/effect p0/p1 sources;
then historical same-key extrema replay and protected Overlap for selected
Frames. Refresh support alone does not justify freshness, even after tightening
read bounds. See the design note for the exact remaining split. No new question
for the user. Usage quota unknown. Focused proof work began22:36 and final
publication/verification reserved before22:55, within19minutes wall time.
