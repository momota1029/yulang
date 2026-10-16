# Draft handoff: native negative-port producer contract

Sprint: `npair-native-port-formation-20261017`, revision 1.
Assignment: `NPAIR-NATIVE-PORT-CODE-CONTRACT-20261017`, revision 1.
Outcome: unapplied implementation-readiness proposal; independent review pending.
Author/owner: Luna `/root`; sequential lane after Astra proof STOP.

## Frozen source evidence consumed

- Sprint contract: `3af4ef163a3555d037fa559db8abd2b4c741605dac64453589b7cbd5b69898e9`.
- Proof: `a7be614af3b432e785fb64d2580ee30de30c448ba5d332e5c40162cb4578ce4f`.
- Proof handoff: `b2d420b0b528f1a6776d6f6372542de5f6304208220d65abc4d052ea22afed45`.
- Adopted NPAIR: `0a73aaf7016e86dd5babbdd5482b05a793764418bc003607207ef0375ee46006`.
- Adoption receipt: `d94e24656854fd2d67ed0f600619349c728dfafa26ca6e312f1faa6d3f3532fa`.
- Existing readiness contract: `36d9792d7a5bb4d06beeb4a1c62df28d38ff171fc324783061c2219a970ce064`.
- Obstruction proof: `2b526b92ef78b8514a81592b303e4db2310dedd13483c74bcfb4bd53798f0a8f`.
- Retention closeout: `674e67dc9f8a3484c58a2b706b8e634ed8b3ffa80495618bb3706d6fdd110087`.
- Applied retention proof: `198046b6eb398734cf657ab03f05e171f8be568c1e8feb31115b9adc46d5f1ff`.
- `candidate_effect.rs`: `44ee33d077c61c9dea6359299ca49218afc6ca1b5b6807690838309b25c731c9`.
- `candidate_source.rs`: `efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38`.
- `candidate_context.rs`: `72da8a6e7b3f04ed3f7054b6151410c7d2b35f9f91b756ade1f6f008244c1ce6`.
- `lib.rs`: `2c1fff385e5270ef7b7eb5fc4d9ed5f6edb6a4c01886887b183401212c5f398f`.

## Proposal summary and limits

The proposed private producer keeps one fresh flexible row for a concrete-only
negative port and stores source Permission separately as a typed annotation
path. It builds the complete recursive Function pair, keeps both ordinary
formal links at 43/44, and leaves root computation effects on FormalEntry
45/46. Source preflight and current pair/effect-port refusal stay intact. No
native `At`, transport, consumer, subtraction, test or compiler change is
authorized. Multiple-symbolic `C_sym`, explicit-empty reachability and full
source admission remain open.

The design is Draft and is not ready for implementation until fresh sequential
review completes and the user separately approves the exact code change. No
compiler or test lease was opened by this handoff.

## Review sequence and receipts

Fresh read-only reviewers, one at a time, each with the sprint contract and
frozen pins:

1. `compiler_referee`, maximum 120 seconds: lowering, exact candidate patch,
   both formal edges, four Function children, refusal gates, atomicity and
   accounting.
2. `architect`, maximum 120 seconds: ownership/lifetime, fresh row identity,
   permission record lifetime, reservation, rollback and bytes accounting.
3. `spec_auditor`, maximum 120 seconds: adopted NPAIR/source domain,
   permission/inflow distinction, `C_sym`, computation effects, J1/J2 and
   output scope.

Each reviewer starts only after an ACTIVE receipt and prior reviewer STOP. Luna
adjudicates findings; no reviewer certifies their own work. Reviewer outputs
and receipts will be added here only after their STOP and exact hashes are
known. Sprint parent remains OPEN regardless of clean review.

Design SHA-256: `2ebb6e4c629e520a1017a20fc5cd52f4e0bbfcdb621456e0927e1a639760dc73`.

## Author receipt

Only this design and this handoff were authored in the Luna lane. The design is
the sole substantive output of this assignment. The proof author STOPPED before
this lane began. No tests, probes, builds, Cargo, compiler execution, expected
output edits or source code changes were performed. The unrelated modified
`tasks/agent-loop/sprints/authentic-source-and-forward-handler-20261017.json`,
three UNKNOWN historical reservations and quarantined board lease remain
untouched. Luna retains sole Git integration ownership.

## Revision 2 correction receipt

Revision 1 design SHA-256: `2ebb6e4c629e520a1017a20fc5cd52f4e0bbfcdb621456e0927e1a639760dc73`.
Revision 1 handoff SHA-256: `ebc6727e49d0d3f4146cef05274d29688bc46daad11949be68da5f89ef6a2533`.
Revision 1 compiler review STOPPED with two major findings; the full finding
is preserved in Luna's current-state record. Revision 2 appends explicit
supersession text to both leased outputs, preserving revision-1 bytes as a
verifiable prefix. The corrected design separates the current internal pair
guard from unchanged source preflight, gives the bounded negative predicate,
threads child paths through both value and effect construction, and makes each
Permission self-contained after the source action lifetime. It remains an
unapplied proposal with no compiler/source/test authority.

New design SHA-256: `14a7e2a3a876ef25de48a191eac88c4483b9fb69a82e3c434fbe115793b62754`.
New handoff SHA-256: pending final freeze.

Revision-1 compiler review is not review of revision 2. Required remaining
sequence within the original cap: compiler delta review 60s, fresh architect
review 120s, fresh spec review 120s. Luna will freeze both corrected hashes
before assigning the compiler delta reviewer; later reviewers receive the
complete effective revision 2. No further author allocation follows.

## Revision 3 handoff delta (design label 2.1)

Revision-2 handoff SHA-256: `74cfeb6c0fc8fff4177e66f86af57e720b52e60d933e88e28ea63e37a8fc3f0e`.
The revision-2 compiler delta review closed both prior major findings and STOPPED
with one minor ordering contradiction. Luna corrected only the pseudo-code
order, preserving the current sequence: argument value, result value, argument
effect, result effect. Every operation now uses its child path and restores the
caller path before propagating errors. The two major closures remain in force;
the minor is corrected pending review.

The exact correction stays inside the two original Markdown leases. It adds no
compiler, source-admission, test or expected-output authority. The next fresh
reviews are architect and spec auditor, sequential, each capped at 115 seconds.
A compiler review allocation is not reopened for this correction. Total sprint
charge remains bounded at 2100 seconds; no further author time follows.

New design SHA-256: `a6b6f37218408b334922c19ff6065bd8bd607294201ec2b371f1376e800c41ce`.
New handoff SHA-256: pending final freeze.
