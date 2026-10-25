# FORCE-SOURCE-REALIZATION-20261025/r8

Status: **FROZEN BY LUNA; staged authorization.** Contract SHA is recorded in
`current.json`. This is a new 5,400-second envelope; no r6/r7 budget carries.

## Original goal, authority, and parent gates

Original goal: complete Lean proofs of Yulang semantics and type inference for
the original accepted source domain. No quantifier, source restriction, expected
output, or accepted semantic rule changes in this sprint.

The accepted abstract finite-success lemma is
`YulangClosure.ForceAdmin.abstract_observe_counted_run_iff`, exact file hash
`620994e5e7383c267a19d5bea93f35d8d82d2db76a03893449bd821250669c97`.
Its r7 outcome is CLEAN for that parameterized proposition only (outcome hash
`b89cbb133006aaae4563789460466ddc790df1460418f124dee36d86b5558d29`). O-NORM
and O-RESULT remain OPEN. The source-authoritative paper is
`docs/yulang-operational-type-safety-ja.tex` hash
`a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`.

Other frozen dependencies:

- N report `tasks/agent-loop/inbox/20261025-force-admin-adequacy.md`:
  `1a0df86f0e14177b287d59d2afab598f89dfc99e403a014d25e069cd3b1833ab`.
- R report `tasks/agent-loop/inbox/20261025-force-return-rows.md`:
  `de1ef24c6cd62c0280dce47e1cf823234f30c8dc471e3a6cab7f8b5130497966`.
- Corrected mapop report `tasks/agent-loop/inbox/20261025-force-source-mapop-correction-r5.md`:
  `203d55dc462046f0616eba027198c68224182fdf4ab03bf19ccb87548c691b8b`.
- r7 contract `tasks/agent-loop/sprints/force-admin-result-discharge-20261025-r7.md`:
  `4b23812951ce23c8868f85a4138c35f4235d0b66339b6a14fdad3f3adf6b1663`.

Baseline receipt carried from the current research branch: `9b945b0bb175e8e0919d388dc720babbdf0c2464`; `.git` is read-only, so Luna will not inspect or mutate Git in this sprint. All authors must report the baseline as inherited, not independently verified.

## Three propositions and exact source-stage outputs

### N1 — concrete whole-packet instantiation

Target proposition: `whole_packet_instantiation_realizes_source`. Construct the
source-owned packet/binder representation and derive concrete capture-avoiding
beta and whole-packet specialization equations. Cover profiles, families, rows,
latent ports, identity/lineage and interpretation; establish exactly one
specialization at each applicable coordinate and preservation of the ordered
wrapper equation. Relate the concrete operation to r7's arbitrary fixed `beta`
and `inst` only by explicit hypotheses proved from source constructors.

Initial exact source lease:

- `tasks/agent-loop/inbox/20261025-force-packet-specialization.md`

Conditional Lean lease, **NOT ISSUED** until frozen source output receives
independent CLEAN review:

- `notes/theory/lean/YulangClosure/ForcePacket.lean`

Grant: 600 seconds source construction; then, only after Luna opens the phase,
up to 900 seconds Lean proof. One assignment, one writer at a time. Stop and
return if source constructors do not determine a claimed specialization law.

### R — Force result relation and rows

Target proposition: `force_result_relation_realization`. First derive the
source-required relation connecting actual returned packet, forced thunk's
result-profile subtree, latent suffix, and result transport. Then derive its
exact finite Flow-row domains/images and fresh occurrence allocation from the
source decorator/Delay-Force construction. Demonstrate that the rows realize
the relation, rather than selecting a convenient row batch. Compare alternate
row presentations only after deriving the required relation. If accepted source
rules do not determine the equation, return the exact unresolved equation and
which source owner/authority must decide it. No arbitrary callback, permission
edge, Ret-only argument, or assumed `ForceReturnRows` witness.

Exact source lease:

- `tasks/agent-loop/inbox/20261025-force-result-relation.md`

No Lean path is leased for R in this sprint.

Grant: 1,500 seconds source construction and adversarial derivation. No
extension or semantic decision authority.

### N2 — decorated encoding and raw coverage

Target proposition: `decorated_admin_encoding_and_raw_coverage`. Define a
lossless source-indexed encoding for the abstract observation shells and prove
its event/wrapper projection. Independently enumerate and derive every raw
administrative successor/error case, preserving counted step lengths and
metadata; malformed type applications, invalid references and raw locals must
remain distinct from success. Identify latent barriers and show they are not
entered by shallow observation. Consume only the frozen, independently reviewed
N1 packet interface; do not infer source encoding or correctness from r7's
abstract theorem. Keep terminal Delay/canonicality and termination as separate
premises unless their source proofs are supplied in-scope.

Exact source lease, staged and initially **NOT ISSUED**:

- `tasks/agent-loop/inbox/20261025-force-admin-raw-coverage.md`

Conditional Lean lease, **NOT ISSUED** until Luna grants the staged assignment,
its source result receives independent CLEAN review, and its direct N1 interface
is frozen:

- `notes/theory/lean/YulangClosure/ForceAdminRaw.lean`

Grant when issued: 500 seconds source construction; then, only after Luna opens
the phase, up to 700 seconds Lean proof. The N2 assignment starts only after an
N1 source interface is frozen and Luna validates dependencies/resources. It may
run alongside R if the two-author concurrency limit permits.

## Schedule, proof and review seams

Begin with at most two concurrent source authors: N1 and R. Three quarantined
legacy UNKNOWN assignments retain their reservations. Luna plus these three
reservations and two authors uses the six-assignment local envelope; no fresh
reviewer starts until an author STOP releases a slot. N2 is staged and does not
own a path until explicitly launched. Never overlap writers.

Each frozen source-stage artifact gets a fresh eligible nonauthor source review
(up to 300 seconds each); only accepted source interfaces unlock their
conditional Lean phases. Proof artifacts get fresh proof review (up to 300
seconds each). Luna serializes Lean checking: 400 seconds aggregate, one
process, one CPU, 1,024 MiB, at most 120 seconds per invocation, installed Lean
4.35.0. No tests, builds, Cargo/native commands, Git, compiler edits, expected
output changes, or scratch files. Exact reviewed hashes must match checked bytes.

The three source propositions are chosen because they discharge separate
blockers on O-NORM and O-RESULT. N1 and R are independent; N2 depends on N1's
frozen packet interface but not Force-result rows. Apply r7's abstract lemma
only after concrete `H/beta/inst` and encoding premises are established.

## Resources and acceptance

Fresh cap: **5,400 seconds** total, within the 7,200-second sprint envelope.

- N1: 600 source + conditional 900 Lean.
- R: 1,500 source.
- N2: staged 500 source + conditional 700 Lean.
- Independent source reviews: 300 x 3 = 900.
- Independent proof reviews: 300 x 2 = 600.
- Luna serialized Lean checks: 400.
- Luna adjudication/current/outcome: 200.

Total: 5,400 seconds. Unissued conditional grants are not spent. Unknown
elapsed time charges the full issued grant. No Astra assignment. At most two
active/reserved new author assignments at once; reserve capacity for review
and integration. No descendants.

Acceptance is proposition-specific: a frozen derivation with exact constructors,
quantifiers, hashes, independent CLEAN review and, for Lean phases, successful
Lean 4.35 kernel check plus reported axioms. A missing source equation may be a
useful blocker only if it gives the exact required premise, source owner and a
falsifier. Source characterization alone never becomes a theorem. No parent gate
closes automatically.

## Stop conditions and parent application

Stop a lane on a falsified constructor premise, contradictory accepted source
rule, missing owner evidence that cannot be derived, or exhausted grant. Keep
the original source domain and paper unchanged; surface any genuine semantic
choice to Luna without selecting it implicitly. If a source-stage review blocks,
no dependent Lean phase starts. Other independent lanes continue within the
same envelope.

O-NORM remains OPEN until lossless source encoding, concrete beta/whole-packet
instantiation, raw error coverage and the separate termination/guarded
observation obligations all close. O-RESULT remains OPEN until the exact
source-derived Force-result relation, Flow rows and occurrence allocation are
proved and connected to the operational relation. Force realization, Call S/C,
parent operational/type safety and the full original semantics/type-inference
goal remain OPEN.

Luna owns current state, adjudication, all phase activations and Git integration.
A worker cannot acquire another path, extend its grant or start a nested team.
At each freeze, Luna records hashes, author STOP receipt, spent resources and
next source/Lean/review gate in `current.json` and the unique sprint outcome.
