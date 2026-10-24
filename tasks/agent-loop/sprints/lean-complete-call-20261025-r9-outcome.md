# LEAN-COMPLETE-CALL-20261025/r9 outcome — SOURCE_INPUT_BLOCKED / UNACCEPTED

Status: **SOURCE_INPUT_BLOCKED / UNACCEPTED**. The r9 implementation lane
stopped at its frozen source-input boundary. The candidate is unchecked and
unreviewed. No S/C proof author was launched. The unchanged Call A/B claims and
the complete Yulang semantics/type-inference goal remain OPEN.

## Scope and authority

- Contract: tasks/agent-loop/sprints/lean-complete-call-20261025-r9.md,
  SHA-256 6a2a2ce7cce845df7239b790709cdbfe24e15bbacc834d9d3027e9f697131811.
- Contract checkpoint: 4df64ba1581d9ffb4150c44f4548d7d9588dd8cb.
- Semantic baseline: 8656445efaadb63bb7919e0ef0155e7630a9748f.
- Worker: /root/call_implementation_r9, requested implementer / Luna high;
  observed model and effort UNKNOWN.
- The live agent completed and supplied a write-cessation receipt after freezing
  handoff revision 1. No descendants or scratch writers remain.
- Issued implementation cap: 1,800 seconds, charged in full; exact elapsed
  time UNKNOWN. S (1,200s), C (1,800s), Lean integration/checking, and review
  grants were not issued or spent.

## Candidate artifacts

| Path | Disposition | SHA-256 |
|---|---|---|
| notes/theory/lean/YulangClosure/CoreSyntax.lean | Changed; unchecked declaration restructuring | dff3e5851c9ef971ec404f9542d684074a13623bb0820c3a5e4d5da072783ece |
| notes/theory/lean/YulangClosure/ControlSyntax.lean | Changed; adds embedded Original delay force step | 1f937e4c51b79d1a2dc4a2291a1e3f5797403eae5975a53a42d574867a1690f0 |
| tasks/agent-loop/inbox/20261025-lean-call-execution-implementation-r9.md | Frozen handoff revision 1 | a64ff517628927aa249ed716449d282d86032f15570bb470e5e6b6d9554f0e65 |

All three hashes were recomputed from the shared worktree and match the
worker's final receipt. Other leased files match the r9 contract inputs.
CallExecution.lean was not created. No raw Call relation or frozen S/C
interface exists.

The handoff's ControlComposition.lean dependency row has a transcription
error. The handoff records
9a48a5f2ef15eb947478757e0fa74457579183ccdb90abf2518886590e33fc40;
the recomputed file hash and r9 contract hash are both
9a48a5f2ef15eb947478757e0fa74457579183ccdbab90f2518886590e33fc40.
This outcome records the corrected digest without editing the frozen handoff.

## Work and checks

The candidate separates the Value/Comp syntax mutual group from the
ValueTyped/CompTyped group and moves Function before its typing relation.
It adds a successor from force of an embedded Original delay into that delay's
actual Original body. These are candidate edits only; they establish no
elaboration, progress, preservation, simulation, coverage, or source/native
claim.

No Lean/Lake invocation, tests, Cargo/native command, proof-hole scan, or
independent review ran. The r8 CoreSyntax.lean failure is historical
diagnostic evidence, not verification of these bytes. The primary's
pre-dispatch agent_sprint.py check is workflow validation only.

## Exact source-input obstruction

The operational source distinguishes a Force effect view from its normal
result transport: §12.45, line 1245, requires View(v, force.effect, M) and a
separate transport to force.result; §12.52, line 1532, requires current
diagram re-observation and connection of View entry, body, and View exit.
Delay retains the body graph for future force (line 1531). Static labels and
dynamic view-occurrence identities are distinct (lines 1231–1236). The
typed-boundary realization draft makes the missing producer obligation
explicit: executable typed-view elaboration, including demanded forces, is an
input at §§388–415, and p_force is the forced thunk's current effect position.

The current formal representation has one ViewOccurrence.path on
TypedCall.Value.view; TypedCall.Comp.force has no Force plan or source label;
PortKind has no Force-specific position; CallView carries call interfaces and
adapter maps but no Force evidence. Comp.expose can store an effect/result
pair, but no source-derived constructor supplies that pair or proves its
mapping from the wrapped value. Existing force successors enter the body
without installing such an exposure. Metadata has return and suspension
operations, and failWorld is explicitly underspecified; it has no Force input
producer or Force-entry contract.

This is a formal input/representation obstruction, not a counterexample to
Yulang semantics. The source and its draft specify obligations for a realized
producer and consumer; the checked-in Lean fragment does not supply them.
Defining an arbitrary path map, conflating effect/result ports, inventing a
world transition, or choosing Force-view failure cleanup would manufacture
premises.

The primary froze the detailed producer/consumer questions and next acceptance
conditions in
tasks/agent-loop/sprints/lean-complete-call-20261025-force-view-interface-amendment.md.
That packet is frozen at SHA-256
8d7ad0d788d559d5efa3e7b75953221d8a7bd9586ffe09ac1f705fe6a3862406.
No code or semantics change is authorized by that gap packet.

## Remaining gates

- call_step_erasure (S): OPEN and unissued.
- call_raw_successor_coverage (C): OPEN and unissued.
- Call context preservation and bounded finite-prefix safety (A/B): OPEN.
- Original inference A/B, source/native correspondence, principality,
  termination, and the parent objective: OPEN.
- Independent review and production authority: NOT RUN / NOT GRANTED.

Next, Luna must freeze a source-derived Force evidence producer/consumer
interface in a separately versioned continuation. S/C remain gated until that
interface is implemented, checked in dependency order, and frozen.
