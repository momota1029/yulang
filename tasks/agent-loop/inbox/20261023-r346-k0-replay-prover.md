# R346 proof handoff — frozen revision 1

Sprint: `R346`, contract revision 1, SHA-256
`7f2419fa4d589ec6bb7d8af769a3eeb94f5361332483321328a06c2558327391`.
Assignment/handoff ID: `R346-K0-REPLAY-COVERAGE`, revision **1**.

Parent: original unchanged Yulang2/Simple-sub source/native A/B; immediate
supplier is original audit N/D2 and `R345-N-REMAINDER`. Domain is exactly
R336 rev4 authentic ordinary K0, L0, R337 J, successful prefixes and the
contract's fixed-row/representative/endpoint ordinary OwnerEmission family.
Original quantifiers and all independent continuation obligations remain.
Baseline branch/commit from contract:
`research/simple-sub-intrusion` /
`a5edc8ee72b7fb1062b8d83d0753b1d43ec76702`; no worker Git observation.

Worker: prover `/root/r346_k0_replay_prover`; current NEW_TASK delivery is
the worker's launch receipt. Parent records session
`01a165ee-0212-7af3-8c99-1c1efcf367fe`, launch 2026-10-23 09:31:30 UTC.
Requested model/effort: `gpt-6.1-sol` / high. Observed effective
model/effort: **UNKNOWN / UNKNOWN**. No in-place model-switch claim.
Author: this worker. Primary `/root` supplied complementary source census;
historical authors are itemized in the frozen artifact. No descendants.

## Frozen deliverable and result

Artifact: `notes/theory/2026-10-23-r346-k0-replay-coverage.md`, revision 1,
SHA-256 **`f21a15eac621216366338ceeb454aec868554668a6cc4b8da903aa79d9d2fc7d`**.
Outcome class: **candidate**, with bounded source/native correspondence and
an explicit hand proof; independent review NOT_RUN by this producer.

The candidate proves the exact disjoint frontier product
`newLower × allUpper ⊎ oldLower × newUpper`, including empty frontiers and
same-key/same-RelationId attachment duplicates. It applies an induction over
ordinary attachment/physical admission to show existing physical keys still
receive distinct new fibers and every affected opposite key is rescanned.

It also proves a stronger exact-key fact: in the authentic monotone ordinary
history, a newly visited fiber tuple cannot already have its exact Replay
dependency key. Prior keys still receive an actual earlier batch/slot history,
with live operation/queue/frame ownership or exact terminal processing;
an old-key physical rescan visits no new pair. Equal child IDs do not merge
different parent dependencies or ack slots. Recipe/cache bits are not used
as completion evidence.

Progress publication occurs after all visits own their generated local-vector
slots, before operation insertion. The candidate accounts for that actual
local owner and the absence of reentrant generation; it does not claim an
operation already exists at the earlier cursor write or prove a failed-state
reuse/rollback theorem.

Each actual child follows `ReplayOperation` → `enqueue_item`/exact ack →
typed worklist → Transport/current/frame ack → Context/Dispatch → ordinary
Diagnostics/Acknowledgements/ReturnReady. `Queued` is not completion. The
actual driver reaches return only after queue/dirty exhaustion and every
frame-owned ack is consumed. R339's exact persistent two-bound witness
supports this family's cache skips/retirements independently of stamps;
R345 supplies distinct FunctionPort/whole-frame retirement under its reviewed
premises. No global fairness or solver-termination theorem is inferred.

Parent application: this supplies the particular temporal/fiber I-work
premise absent from R338/R339/R345 and applies their entailment results to its
actual consumers. Full N, completed-source-constraint inventory, all other
cache/source origins, transport/FreshUse/canonicalization, W/Z/S0/C/M,
effect/boundary semantics, principality, F1/FK1, original A/B and production
remain OPEN. No authentic compiler defect is established.

## Exact inputs and checks

Full direct dependency paths/hashes are frozen in the artifact's final table.
They were read/hash-checked before the handoff; salient pins are:

| Input | SHA-256 |
| --- | --- |
| R336 rev4 | `4bcbe71ec9f2372baca884e3db737c16fc19ad2a51103965ade5ca4c2ecf4973` |
| R337 J | `e14b8125a505c3001021396b8c6e949e3b0a58f61ecf2785f915dbdde65dfc62` |
| R338 proof / census | `f438939f99c212324a397f527d46d4a4ab565733e4b2e9e2ae55254e96ca9bf0` / `56174af37c13d2e6ac846b84c3fd71075bceefb8b05474c1f8b3d6d5b2c50ac9` |
| R339 proof / reviewed outcome | `8797013ab5ea77655629fce45031fb28e1c5557979c1f213b9268abd31080c87` / `07abaf5ee285917a4f49ce94fbf287b115dfcdbd20f8275bdcb6bcc3acec0701` |
| R345 proof / reviewed outcome | `85f8def9fe6e3c07b249c279d14976a428cf15c2d3eba089dbc4f5770e16f8df` / `a8b9b75d41be900060d7ba593bb77aaec738a67674654b6c823e92fac18ac8ce` |
| Primary R346 census | `1179312d8230616a0ac5cda45a1c29f08012bba9327f2f3601bb3179cfb5fdfd` |
| candidate_extrusion.rs | `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61` |
| candidate_context.rs | `33af2efb6ed782e4f143cccff03c62087e6ba8d0fbe90415846537fc2a08cec5` |
| candidate_effect.rs | `d156fdbf0300387a5aa036053a2cc7eeb6312a803aaf38838e30dd2731ca4945` |
| candidate_intrusion.rs | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| lib.rs | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |

The initial compact snapshot's stale `252a7247…` contract pin was reconciled
by Luna to `7f2419fa…` before any artifact write, with no scope change.
All other checked pins matched. Original user audit/TeX/aligned files are
context-only and user-owned; no write or Git claim applies to them.

Checks: direct read-only owner/caller inspection; manual product, admission,
dependency/ownership and entailment inductions; direct SHA-256 comparisons.
No tests, Cargo/builds, executable probes, code edits, Git, network/external
contact or descendant launch. No scratch files. The only new paths are the
artifact above and this exact inbox; no shared record was edited.

Reused historical proofs only under the stated K0/fixed-state premises.
Rejected: tests of assumed transitions, a bare recipe/dependency/cache key
as discharge, physical multiplicity as new fiber identity, and extension of
the local two-bound witness to foreign continuations or arbitrary ports.

## Next action, mutual TODOs and stop receipt

`R346-REVIEW`: Luna owns fresh non-contributor review of the frozen proof and
census; target falsifiers are an actual uncovered delta pair, key hit without
earlier slot history, head publication without local/operation ownership,
lost/reordered accepted ack, or reachable ordinary return with outstanding
queue/dirty work. Review must also challenge the authentic source census.

`R346-N-REMAINDER`: Luna owns the original N parent and the complete
source-constraint-to-live-or-entailed end-state inventory, starting with source
cache suppression before OwnerEmission and origins outside this family.
Required inputs: the accepted bounded predecessors plus this artifact only
after review. Proposed output: exact owner/consumer correspondence or an
authentic missing necessary interaction; a coverage gap is distinguished
from absence of algebraic entailment and from a source-qualified defect.

`R346-IMPLEMENTATION`: `NO_SAFE_CODE_SLICE`; no provisional or production
edit is needed by the established candidate. A review-discovered mismatch
returns to Luna for a minimal exact-owner packet and falsifier before code.
These TODOs grant no new lease, dependencies or resources.

Coherent deliverable stop condition reached. Full allocated **3000 seconds**
charged conservatively; no renewal or carryover. Parent launch to final hash
check at 09:40:45 UTC was 555 seconds; the handoff/freeze adds only the current
bounded write/hash step. Exact active CPU time is UNKNOWN. Worker-local first
clock was 09:35:06 UTC. The final write is this handoff; afterwards only its
hash read and reporting occur. **WRITES STOPPED at revision-1 submission**;
no descendants or unresolved descendant leases. No worker remains computing
while review waits. Pending independent review and Luna adjudication; suitable
only for a non-authoritative research preservation checkpoint until then.
