# Sprint local-use-existing-map-retention-20261017

Status: adopted by Luna after sprint-end selector delta; revision 1.
Branch: `research/simple-sub-intrusion`.
Administrative baseline: `c2ca891da23d791dfa661c7745864ef3613a32df`.
Compiler baseline: source `candidate_scheme.rs` SHA-256
`2ce5d664bdce1417379cd80767bc53643b6e40740a9fe7e942c24c2009da351e`; exact
byte snapshot is leased at
`tasks/agent-loop/snapshots/20261017-candidate_scheme-pre-local-use-retention.rs`.
Authority: adopted NPAIR §§2–4 only for semantic boundaries; CLEAN-reviewed R1
only within finite-query retention premises; CLEAN-reviewed Draft candidate
only as planning evidence; `rules/design-authority.md` and
`rules/goal-driven-sprints.md`.

## Original goal and outcome

Continue the original `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` path
without changing its source domain or quantifiers. This sprint examines the
already-existing structural maps created by `FreshUse` and their lifetime at
`GraphState::commit_local_use`, then prepares a concrete, reviewable candidate
for retaining only the correspondence justified by those current maps.

This narrower work can advance lifecycle safety without asserting any missing
negative-pair source evidence. It must not create permission-to-inflow, At,
provider, selection, closed-world absence, subtraction, or a receive consumer
from family/row equality, bundles, bound snapshots, or source origin alone.
The old R1 is a logical sufficient-condition result; this sprint must establish
which actual existing maps/objects fit within a more concrete structural query
subset and where their referents remain owned.

Success evidence:

1. A frozen constructive source-to-map lemma identifies the exact queries
   expressible by present `FreshUse` maps, the mapped values and stable owners,
   what is dropped at commit, and which NPAIR queries remain unanswerable.
2. After the proof freezes and receives fresh independent compiler_referee
   review, Luna writes a concrete candidate code contract and exact patch
   proposal into a design artifact only. It may show the proposed Rust delta,
   source ownership and accounting but does not edit compiler sources.
3. Fresh architect and spec-auditor reviews assess that exact candidate and
   retain all semantic/production limits. A reviewed result becomes concrete
   material for the user approval gate; it is not code authorization.

## Two sequential lanes

1. Sol/high prover, cap 360s, at most six substantive stages. Exact outputs:
   - `notes/theory/2026-10-17-local-use-existing-map-retention.md`
   - `tasks/agent-loop/inbox/20261017-local-use-existing-map-retention.md`
   Inspect actual `FreshUse` fields, construction, restoration, ownership and
   commit route. Define finite structural queries supported by existing term,
   row, effect-operand, context, bundle, evidence and scope maps. Prove only
   faithful map lookup after retention when its source/object IDs still resolve.
   Separate owned from external coordinates and copied from anchored rows.
   Identify lifetime/rollback/accounting facts from current owners. Do not
   promote map presence to source-typed NPAIR evidence. Apply R1 only to this
   structurally justified subdomain; keep all absent descriptor/At/provider/
   consumer facts OPEN. Stop if a query needs new compiler fields or semantics.
2. After the proof author confirms STOP and the fresh compiler_referee finishes
   within 120s, Luna/high, cap 600s, writes only:
   - `notes/design/2026-10-17-local-use-retention-code-contract.md`
   - `tasks/agent-loop/inbox/20261017-local-use-retention-code-proposal.md`
   The proposal may include a source diff as prose or a fenced patch for the
   existing `LocalFreshRoute` / `FreshUse` lifecycle, but it must state that the
   code is unapplied. If current map lifetimes cannot justify safe retention,
   record the exact blocker and stop without manufacturing fields. Do not write
   `crates/yu-solver/src/candidate_scheme.rs` or any other compiler source.

## Review and approval boundary

Fresh reviews are sequential: compiler_referee 120s on the proof; architect
120s on the exact patch proposal, lifecycle/rollback and resource effects;
spec_auditor 120s on NPAIR semantics, scope and authority boundary. Each reviewer
must STOP before the next begins. A blocking proof finding pauses dependent
proposal acceptance. No review closes whole `rho_u`, source/native adequacy,
actual consumer, soundness, principality, or the parent.

Any new internal representation or architecture decision must first be stated
with its alternatives, independently reviewed, and explicitly approved by the
user under `rules/design-authority.md`. This sprint produces a reviewable
proposal only; it cannot satisfy or bypass that approval. Only after the user
approves the exact implementation contract may Luna open a separate exact-path
code sprint. Negative preflight remains untouched; no subtraction or residual
publication; no consumer borrowing from Catch.

Fresh envelope: 1560 seconds — proof 360, proposal author 600, reviews 360
(three sequential 120s caps), coordination 120, reserve 120. One author at a
time; Astra 0; no code, tests, Cargo, builds, probes or execution. No budget
carryover. Preserve three historical UNKNOWN reservations and the quarantined
board lease. The next dispatcher boundary is a proof obstruction, representation
approval, new dependency/lease, review finding or sprint end.

## Frozen dependencies and exact write limits

- R1 artifact `notes/theory/2026-10-17-npair-use-certificate-retention.md`,
  SHA-256 `c5c069798cd5822918e09438ac7e82e627d562ba0b13f8233ca5709e43f9c922`;
  handoff `tasks/agent-loop/inbox/20261017-npair-use-certificate-retention.md`,
  SHA-256 `4ef908c919d1e94b1c65960d31df730b0620980382f725a5c6bab75585099514`;
  compiler_referee CLEAN only for conditional finite-query R1.
- Reviewed Draft candidate `notes/design/2026-10-17-npair-native-architecture-candidate.md`,
  SHA-256 `1d2a4d0f603d0548d3aa6cd6938e4795714aabc4d72eb11b785dcd2c8858b13d`;
  handoff `tasks/agent-loop/inbox/20261017-npair-commit-retention-architecture-repair.md`,
  SHA-256 `ccbd92cd8b6c0185de5c23d7ab7b9a2ba51510cf33609092559945639f2cbd21`;
  architect/spec CLEAN only within finite-query Draft scope.
- Adopted definition SHA-256
  `0a73aaf7016e86dd5babbdd5482b05a793764418bc003607207ef0375ee46006`; adoption
  receipt `d94e24656854fd2d67ed0f600619349c728dfafa26ca6e312f1faa6d3f3532fa`.
- Prior closeout:
  `notes/progress/2026-10-17-npair-commit-retention-repair-closeout.md`.
- Current source baseline exact bytes must be verified against the contract pin
  before the primary writes the snapshot; only the snapshot, proof artifact,
  proof inbox, proposal artifact, proposal inbox, sprint contract and
  `current.json` are leased. No source files, tests, fixtures, expectations,
  rules or other worker paths may be written.

Luna owns adjudication, current-state synchronization, explicit-path Git staging
and non-forced pushes. Preserve the unrelated dirty
`tasks/agent-loop/sprints/authentic-source-and-forward-handler-20261017.json`.
