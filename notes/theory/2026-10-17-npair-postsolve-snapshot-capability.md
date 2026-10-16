# NPAIR post-solve snapshot capability: physical-storage blocker

Status: frozen candidate source audit and conditional capability construction;
not a reviewed theorem, implementation permission or production authority.
Assignment: `NPAIR-POSTSOLVE-SNAPSHOT-CAPABILITY-20261017`, revision 1.
Sprint: `npair-postsolve-snapshot-capability-20261017`, revision 1.
Author: `/root/npair_postsolve_snapshot_capability`, sole author; no descendants.
Requested model/effort: `gpt-6-sol` / high; observed: UNKNOWN / UNKNOWN.
Baseline supplied by Luna: `ac838c252a6567cd92c186ebf928348565e8004e`.

## Actual result and parent application

**The successfully returned candidate result cannot provide the requested
read-only current physical-slot resolver: the live physical bound vectors are
not retained.** This is a concrete storage/lifecycle blocker in the pinned
source, not a counterexample to the parent inference theorem.

`InferenceSession` owns `bounds: Vec<VariableBounds>` and
`effect_bounds: Vec<EffectBounds>` (`lib.rs:7682+`). Each contains four physical
lanes (`lib.rs:4036+`). `CandidateSolvedResult` contains only
`FrozenInferenceData` (`lib.rs:7596+`). Its complete field declaration
(`lib.rs:7554+`) and complete construction (`lib.rs:17749+`) contain neither
vector. `finish_observations(self)` reads them to compute projections
(`lib.rs:17516+`), then transfers selected fields into the returned data. The
untransferred session fields are destroyed on return. The resource-probe-only
branch even explicitly drops both vectors (`lib.rs:17685+`); the blocker does
not depend on that branch or configuration. The ordinary result also omits
them. No session reference is retained by the returned owner.

`GraphState` retains captured `Graph`s/routes; each `Graph` has symbolic nodes,
rows, `Bound`s and `EvidenceSnapshot`s (`candidate_scheme.rs:6–49,117+`). A
`Bound` records graph-node indices and a source `BoundKey`; these are not the
discarded physical lane arrays. `BoundEmission` retains its bound and
`PhysicalBoundSlot { owner, lane, index }` (`candidate_context.rs:464,483+`).
The descriptor is retained; its original target storage is not. Reading that
descriptor or matching a captured graph bound cannot check what occupies the
specified original physical slot. Reconstructing an equivalent relation would
not establish the requested physical-storage fact.

Apply this to `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`: the one-shot
structural suffix still lacks its enforced complete snapshot premise. The
new post-solve restriction removes the live-session continuation route from
the public wrapper but also loses the physical storage required by the check.
The proposed readiness implementation must wait for a Luna decision about
retention/ownership. No inference restriction, bypass or source-domain change
is justified. The original source occurrences, dependent witnesses, providers,
worlds, assignments, guards, continuations, interactions, Call demands,
residual lineages and futures remain distinct. F1/FK1, J1/J2 and all independent
parent gates stay OPEN. No `eta_op`, `realization_op`, adopted `At`, source
admission, N-Transport, subtraction or receive-consumer result follows.

## Returned ownership, mutation and quiescence

The actual successful-return chain is
`CandidateInference::solve_mode` (`shadow_apply.rs:274+`) → consuming
`InferenceSession::run_candidate` (`lib.rs:10441+`) → `execute(&mut self)` →
consuming `finish_candidate` → consuming `finish_observations` →
`CandidateSolvedResult`. The wrapper retains that result in its private
`solved` field (`shadow_apply.rs:76+`). An `Ok` result can retain conflicts;
`candidate_conflicts` exposes them, while graph export/fresh-use observations
refuse conflicts (`shadow_apply.rs:324–358`). Successful return is therefore
not by itself conflict-free evidence or successful source admission.

The inspected wrapper API observes retained data through `&self`; it does not
return a mutable session or resume the consumed session. The source does not
make the private result an intrinsically immutable Rust type: an owning module
could mutate ordinary fields through exclusive access if code were added.
Current shared access excludes ordinary exclusive mutation while the borrow
remains usable. Consuming the session excludes resuming that very session
through the returned public wrapper. These are precise ownership facts, not
proof that every retained processing/replay/restoration record denotes a
completed operation. No complete owner-checked quiescence predicate is supplied
by `finish_candidate`; its explicit assertions concern candidate mode,
finalization and the absence of closed types/schemes.

The newly pinned intrusion owner resolves the earlier representative-read
uncertainty locally. `State::values/effects` are ordinary `Vec<u32>` fields
(`candidate_intrusion.rs:10+`). `representative(&[u32], row)` (`:84+`) walks
parents with shared reads; `value_rep`, `effect_rep`, and `rep` (`:109–120`)
perform no path compression or other mutation. `begin(&self)` constructs an
owned undo record. `rollback(&mut self, ...)` (`:145+`) restores ordinary
fields and delegates effect rollback. Session extrusion retention, recapture,
settling and row merge (`:230+,236+,297+,317+,489+,521+`) require `&mut self`;
settling updates the cursor/dirty bit and merging updates forests/generation
under that exclusive session access. Those operations cannot interleave with
a usable shared borrow derived from the same owner in safe Rust. This audit
found no interior-mutation representation in this intrusion State or its
representative walk.

Effect/context rollback and evidence insertion likewise require exclusive
access (`candidate_effect.rs:278+`; `candidate_context.rs:572+,683+,737+,1780+`).
The `Cell` fields in `candidate_scheme::CaptureEvidenceMeter` (`:347+`) are
separate capture scratch, not retained `GraphState` representative storage.
Test instrumentation and unrelated counters are not evidence of mutation of
the relevant retained arrays. Conversely, no universal transitive immutability
claim is made for unpinned source/scope/term/HIR owners reachable from other
fields. Those owners were not opened. The physical-storage blocker is already
decisive, so no enlarged source audit or full continuation-completion proof is
attempted after it.

## Same-owner capability construction and resolver boundary

A same-lifetime parameter alone cannot distinguish two live results. A
schematic private handle can instead retain `owner: &CandidateSolvedResult`
plus its checked record index; every operation combining it with a snapshot
first checks reference identity against that snapshot's retained owner.
Constructors and fields remain private; free-standing IDs are not accepted.
Alternatively the handle can resolve only through its own retained owner,
without accepting a separate receiver. This is a conditional construction,
not an existing API.

For the identity-check construction, two distinct simultaneously live result
objects have distinct addresses: this owner is a non-zero-sized ordinary
object. Retained shared references prevent moving/destroying an owner while a
later handle operation remains usable. Address reuse after destruction cannot
create a simultaneous-live-owner collision. Equal HIR identity, raw ID,
endpoint, generation or lifetime does not substitute for this owner check.
All subordinate handles must be minted from this owner and checked at every
combination; an owner field on only the outer snapshot is insufficient.

Such an identity check could enforce same-result provenance for retained
records, but it cannot recreate missing physical storage or antecedents. A
physical resolver would need the actual selected owner's eight lanes:

| Row kind | Lane | Required original storage |
| --- | --- | --- |
| Value | ValueLowerRow / ValueUpperRow | `VariableBounds.direct_lower_rows` / `direct_upper_rows` |
| Value | ValueLowerAtom / ValueUpperAtom | `VariableBounds.exact_non_variable_lowers` / `exact_non_variable_uppers` |
| Effect | EffectLowerRow / EffectUpperRow | `EffectBounds.direct_lower_rows` / `direct_upper_rows` |
| Effect | EffectLowerAtom / EffectUpperAtom | `EffectBounds.exact_non_variable_lowers` / `exact_non_variable_uppers` |

It must reject a row-kind/lane mismatch, check row and slot indices, and compare
the actual stored operand and owning row with the admission/emission `BoundKey`
using the original producer's orientation. Preserve raw owner rows separately
from representative rows. The present returned result supplies none of these
original lane arrays. A read-only accessor over it therefore cannot implement
this check. No claim is made that retaining the arrays alone would establish
all producer orientation, continuation-completion or coverage obligations.

`BoundEvidence::admit` (`candidate_context.rs:683+`) explicitly marks
OwnerEmission/ExtrusionLink processing, ordinary-seed and missing antecedents;
FreshUse inherits antecedent coverage and adds
`ReplayUseAntecedentsNotRetained`. Neither the owner handle nor a complete
enumeration authenticates those missing facts. They remain unavailable unless
independently established, and must yield an explicit incomplete/reject result.

## Reuse, exact TODO and STOP

Reused: the prior `/root/npair_snapshot_borrow_enumeration` conditional
shared-borrow lemma, same-owner warning, evidence omissions and accounting
limits; Luna's revision-2 owner-interface obstruction and review disposition.
The exact intrusion pin now permits the local representative audit missing
there. Rejected: promoting that local audit to full immutable/quiescent
evidence, promoting `Ok` to conflict-free source success, treating captured
graph storage as the physical arrays, and treating enumeration as antecedent
authentication. Historical source/Call proofs are not used outside their
stated premises. Dependency authorship remains with the original authors;
native source authors/effective settings are UNKNOWN here.

**NPAIR-POSTSOLVE-PHYSICAL-RETENTION-20261017**, to Luna and owners
`InferenceSession::finish_observations`, `FrozenInferenceData`,
`CandidateSolvedResult`, `CandidateInference`: first decide and review whether
the actual physical `bounds`/`effect_bounds` can be transferred to a private
post-solve observation owner, preserving original row ordinals/lanes and
evidence associations, or whether this snapshot must instead be acquired
before storage destruction. Required input is this pinned lifecycle evidence;
proposed output is an unapplied ownership/API contract naming its complete
retained payload and quiescence condition. No code is authorized. Falsifier:
an alleged live-slot resolver accepts a descriptor without reading the
original retained row/lane/index and checking its operand against the evidence
key, or silently substitutes a captured graph/reconstructed relation.

**NPAIR-POSTSOLVE-EVIDENCE-COMPLETENESS-20261017**, to Luna and
`candidate_context::BoundEvidence::admit` / future structural validator owner:
retain explicit unavailable OwnerEmission/ExtrusionLink/FreshUse cases in any
API proposal. Falsifier: complete iteration or successful solve clears a
coverage gap without independently evidenced antecedents.

Four bounded stages: verify pins/authority; inspect consuming result lifecycle;
audit relevant intrusion reads/exclusive mutations and conditional owner
identity; apply the concrete storage blocker and freeze. The exact blocker is
the stop condition. Next work requires Luna's ownership decision; there is no
further leaf stage or implementation step authorized by this receipt. Fresh
review belongs to Luna; this producer cannot certify the combined result.

Checks: static source reads and actual SHA-256 comparisons only. No tests,
builds, probes, Cargo, source/compiler execution, Git, network, nested CLI,
children or production edits. Aggregate reads sometimes truncated; decisive
result declarations, transfer construction and intrusion representative/mutation
definitions were reread in bounded excerpts. Only this artifact and the one
assigned inbox are written; no scratch/generated paths. Resource/time and
final writer-stop receipt are in that inbox.

## Frozen direct dependencies

All ten actual pins matched before reliance. Prior artifacts' embedded older
dependency hashes remain historical provenance, not pins adopted in this audit.

| Path | SHA-256 |
| --- | --- |
| `tasks/agent-loop/sprints/npair-postsolve-snapshot-capability-20261017.md` | `3709fc3ee119b95583b2b92ce8c3aa7820e8ac8723b2f0441cc402b266433637` |
| `crates/yu-solver/src/lib.rs` | `2c1fff385e5270ef7b7eb5fc4d9ed5f6edb6a4c01886887b183401212c5f398f` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `7a57a93481095c6e7d4b8781810b1a5aa0d174e41ede29ac3f2b2b96bce10b0c` |
| `crates/yu-solver/src/candidate_context.rs` | `72da8a6e7b3f04ed3f7054b6151410c7d2b35f9f91b756ade1f6f008244c1ce6` |
| `crates/yu-solver/src/candidate_effect.rs` | `11a1477ff2c35c03dccb70bdc6121d89d3ced9fadb1921cb8cf8cd5c093b07fb` |
| `crates/yu-solver/src/candidate_scheme.rs` | `52b7281946de755003ee8f3b3d18cbc2df6cc6db5566b4e5ecf391b74a92640a` |
| `crates/yu-solver/src/shadow_apply.rs` | `bb1e63c2ea33bf0b6e7408bd015d2498a9aed4dd45e250a85433169c9da334bf` |
| `notes/design/2026-10-17-npair-snapshot-owner-interface.md` | `92c8934820604f895958bf8b2af773128def4c0007f4fb1ec0146eb416eb55f8` |
| `notes/theory/2026-10-17-npair-snapshot-borrow-enumeration.md` | `5c008735438e191d52c4255d6d4b91b5eb2f810deb661a85c27b0061d29e1cb7` |
| `tasks/agent-loop/inbox/20261017-npair-snapshot-owner-interface.md` | `c4f15c09cb08facaf5ac836551dfb49d984c24c8abca60614fc2bd55816f79c2` |
