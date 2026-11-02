# Sprint R267 — consumer-lineage temporal closure

Status: admitted revision 6 under the unchanged Yulang inference soundness and
Rust goal. Luna's admission is recorded in
`tasks/agent-loop/history/20261102-r267-r6-admission.md`.  Branch `yulang3`;
fixed baseline `8d646ac2ed171e13a529e25e035fc75f91678b0b`.

## Original obligation and outcome

Preserve the full accepted source domain, original parent theorems and
quantifiers, Simple-sub A/B, independent satisfying assignments, shared
witnesses, F1/FK1 and foreign continuations. Parent/A/B delta remains zero.
The unchanged edge is inference soundness → R70 copy correspondence →
`R71-RAW-CANONICAL-FIBER-COVERAGE-1`. R5 independently reviewed VD267 and
removed only the local Value discharge-time mismatch. This continuation targets
the source-required Value canonical-candidate and ordered opposite-input join
that R5 left open.

R265's reviewed source-native evidence names the actual Replay → Context →
Function-port consumer but leaves TEMP265/Z265 and the accepted-source
occurrence/canonical-candidate/consumer join open. Attack those two obligations
together. Preserve R265's TEMP265/Z265 text and definitions. At an actual
source-generated occurrence, retain the source Value/occurrence, parent/copy
identities, canonical candidate, every selected physical slot, raw/canonical
keys, exact ordered Replay inputs and RelationIds, FiberTransforms/evidence,
scope/use identities, merge history, and all relation-local residual cuts.
Derive the actual opposite inputs and each later `P_v(q)` consumer observation.
Then prove the temporal simulation across every applicable path or construct
a fully accepted-source occurrence whose named consumer requires a lineage
absent from all transports after complete same-class slot and history
accounting.

Apply a completed result at the unchanged R70/R71 edge. Otherwise freeze the
first missing source constructor/consumer join or exact failed TEMP265/Z265
equation. A source-shaped sketch, bucket/endpoint equality, unequal ContextIds,
assumed discharge or unjoined abstract occurrence is not success or a
falsifier. No premise may be inserted as an assumption and no original
quantifier may be weakened.

ENTRY-WF, R70 drain/eventual Diagnostics, Q262-EPISODE, other R71 permitted-
history/rollback obligations, diagnostic adequacy, successful-helper
coverage, full soundness, A/B, F1/FK1 and foreign continuations remain OPEN
unless separately discharged. No semantic or production change is granted.

## Read authority

Revisions 2 and 3 stopped before technical dependency or source-body reads
because required operational references were missing. Revision 4 stopped at
identity reconciliation before technical hashing. All four grants remain
charged. Revision 4 receipt: `tasks/agent-loop/history/20261102-r267-r4-identity-stop.md`,
SHA-256 `74adc5e61dafb218cf073ac5af241595b90b9a5e4353286d40faa71abc75f545`.

The authority is divided into operational instructions and proof/source
dependencies. All listed files are read-only. No other path may be searched,
opened or used. In particular,
`notes/theory/2026-11-02-source-owner-coincidence-r255.md` is explicitly
excluded. If a listed document makes another path mandatory for this packet,
stop before opening it and notify Luna for a contract revision.

### Operational instructions

These govern role, process and assignment handling; they are not proof or
source evidence. Read each exact file:

- `AGENTS.md`, SHA-256
  `446ce61f7352a949b6da5ec2912587ea8e7b0841571677531e1cbf7da90b8d57`;
- `AGENTS.pre-sprint.md`, SHA-256
  `99ae7bbda0a8907a48f762420d996e145e9870ad9794ea0dc608770131182882`;
- `rules/goal-driven-sprints.md`, SHA-256
  `f2e01e3c33dc13d6c5cb77a66e7c5f0de15f08669f5a47fef0d6cb5c914da3a5`;
- `notes/design/2026-10-16-goal-driven-sprints.md`, SHA-256
  `2dfeb555c913d3142078de535ee4b7f68e9a27f2b91a5f0bb82d4d867db4fc4e`;
- `tasks/agent-loop/README.md`, SHA-256
  `0f829876325565f3c42fbf1950d01deef8c6fda4e92989f668ce1adada41efd6`;
- `tasks/agent-loop/current.json` as read-only current assignment state (it is
  mutable; do not treat it as proof evidence or follow paths not listed here);
- `rules/orchestration-budget.md`, SHA-256
  `119c89cb9d02a5e8e1be27ac27a5eb30277be0039437b3e341f60a186b413ce5`;
- `rules/orchestration-budget.pre-sprint.md`, SHA-256
  `a0a114b589e8920af8e8fd871d15f63d68b735fc1a553f5a89952b1eab8489e5`;
- `rules/agent-orchestration.md`, SHA-256
  `ce6b6553809b9f9f6a6091a728204448c86e4e297b7326a73b90a4b3215d70c9`;
- `rules/agent-orchestration.pre-sprint.md`, SHA-256
  `5d5c3e73c65dc280a4a66e698feb73acc7c874dd70df42eb8c341aaedf422e4f`;
- `rules/research-lab.md`, SHA-256
  `1ffdabce7cc65d4e463e9a50a7a572c2974809bed415071b57a23efed8eb3228`;
- `rules/research-lab.pre-sprint.md`, SHA-256
  `3f70daf755fd6af59959fa48a35aa2d5153639621cc18edc58934246f2aabb69`;
- `rules/design-authority.md`, SHA-256
  `e4055100f6e75b9c8a6294ec6c68643d8677d7b35b45e430450f7e2c2ad97eb1`;
- `rules/compiler-engineering.md`, SHA-256
  `4567cc0f6997c116114cba3322563cb0ddbe5c73ab3403e5272f0e638cb73ed9`;
- `rules/git-concurrency.md`, SHA-256
  `0992b73aea3fdd9a53c624b6010e1eeaa97d308f8f9e18698b9115d1b4cf8d09`;
- `.agents/skills/yulang-sprint/SKILL.md`, SHA-256
  `b6f4a50703928020607edebe1c8b138fb98a0378220f00b7c190dba9fc068515`;
- `.agents/skills/yulang-proof-portfolio/SKILL.md`, SHA-256
  `84c5f100f31264453db5097d6b6f146252e417a791e95e84ea4c03671d6f4161`;
- `/home/momota1029/.codex/skills/yulang-proofs/SKILL.md`, SHA-256
  `db55dfb7568805ac6b6372fe8bc05cc00731ae5b5ed33c6af72007a7ce885810`;
- `.codex/config.toml`, SHA-256
  `30114114cfa88801836b4a42f5fdde9d72694f6536da3d8d910952fc92b6b0c2`;
- `.codex/agents/prover.toml`, SHA-256
  `62663176e171c315c06f63612339c179ecf140bb721e5d2b0c631e2236834254`.

The compiler-engineering rule's reference to broad architecture does not grant
an open-ended read. This packet proves current solver constructors/consumers
against the task-specific approved Simple-sub principles already listed below;
it makes no architecture, semantic, API, or production decision.
`docs/yulang3-architecture.md` is not a direct dependency because this packet
does not change that broad architecture; the task-specific approved
Simple-sub principles govern its proof obligation. The compiler-engineering
rule's trigger for a design-debt audit after two materially different proof
attempts is not met: R267-1 through R267-4 stopped before attempting a proof; revision 5 supplied
reviewed local evidence. No source-input-join attempt has yet been made.

Read-only hash gate: use `sha256sum` on only the exact listed paths below; do
not invoke `python` for hashing. R255 has 36 entries; validate every listed
hash before source-body reads and again at freeze. Hashing creates no scratch
files.

Spawn task name, contract identity, and current-state identity are all
`sol_r267_source_input_join` / `/root/sol_r267_source_input_join`. The new
worker must read this contract, then wait for Luna to compare the live runtime
identity with that exact value. Before Luna sends
GO, do not open another file, read technical/source material, or write either
leased output. If the runtime identity differs, stop without further reads or
writes.

### Packet and proof/source dependencies

These are the complete direct technical dependency list. The revision-1 through revision-5 contracts are admitted only as superseded
assignment history; their incomplete read-authority lists have no force over
this revision. Their stop receipts record that no source was read and no result
was produced.

- this R267 revision-6 contract;
- `tasks/agent-loop/sprints/consumer-lineage-closure-r267.md`, SHA-256
  `5902b752eb54c88517e8b8a9b388ad459b8198ec5ad5054d16666fe857a04f19`;
- `tasks/agent-loop/history/20261102-r267-read-authority-stop.md`, SHA-256
  `1e0c53dcccf9f12155c914b34cae75ee27a7964d3d520d7a856304c89f451c56`;
- `tasks/agent-loop/sprints/consumer-lineage-closure-r267-r2.md`, SHA-256
  `65d45775e132d693caf5e7ea0709d3d81647586040a210e8cf3c7d80cfc4127f`;
- `tasks/agent-loop/history/20261102-r267-r2-read-authority-stop.md`, SHA-256
  `b92424db181aa8e03f1619834d242c97abd5d3a5765fc54fa116a57a818c8ced`;
- `tasks/agent-loop/sprints/consumer-lineage-closure-r267-r3.md`, SHA-256
  `39016a8483f76a1d005e13d24e188e89826f5f562e84c1de2a397b4ecef829c7`;
- `tasks/agent-loop/history/20261102-r267-r3-read-authority-stop.md`, SHA-256
  `0192ae462e84c4de2c2aa64b0795b5d171490ce52e53a898e3b52ca1031791da`;
- `tasks/agent-loop/sprints/consumer-lineage-closure-r267-r4.md`, SHA-256
  `aedf39f4a462f3093eeed61d0adab269b7c7beb6630c1d4692b4b7ce67defc3e`;
- `tasks/agent-loop/history/20261102-r267-r4-identity-stop.md`, SHA-256
  `74adc5e61dafb218cf073ac5af241595b90b9a5e4353286d40faa71abc75f545`;
- R267-r5 provenance clarification
  `tasks/agent-loop/history/20261102-r267-r5-provenance-clarification.md`, SHA-256
  `a37a17de572be2fbcf7a1cb69e44cb026be2f12a5e90b94d3814211acb22b258`;
- R267-r5 contract `tasks/agent-loop/sprints/consumer-lineage-closure-r267-r5.md`, SHA-256
  `54d53b708f65e189d4efd91a049ea800483bcec4ba4e7e8f3df5f71e4a6411ad`;
- R267-r5 theory `notes/theory/2026-11-02-consumer-lineage-closure-r267.md`, SHA-256
  `ba60efeb5a83a314a876e4c7efb61132524a556f2a42ddceb996e434c7e204dd`;
- R267-r5 handoff `tasks/agent-loop/inbox/consumer-lineage-closure-r267.md`, SHA-256
  `bb7d41a3cf310a84c63016e0101f5061d4bb7de08e1c4c401416fa92379600f7`;
- R267-r5 independent review
  `tasks/agent-loop/history/20261102-r267-r5-vd267-independent-review.md`, SHA-256
  `c3ec91872a44899144ab81d5cce9bdf96ed4cd557554259e9e2025a215257cf2`;
- `.codex/agents/compiler-referee.toml`, SHA-256
  `c8a7e39d20aa823798561bc361804eca36cc7ba0c9cdc42e01205bd77b811c8d`;
- R255 pin manifest `tasks/agent-loop/sprints/source-owner-coincidence-r255.md`,
  SHA-256 `f6138d36052934093328e34c01102fc9155ea9d8a0ccfd19182af6e7e2d946ef`;
- R265 contract `tasks/agent-loop/sprints/consumer-lineage-simulation-r265.md`,
  SHA-256 `2062a88a9ce130155bf794683325c942dd1dca3cd79b9fccf845bb23e12e0237`;
- R265 theory `notes/theory/2026-11-02-consumer-lineage-simulation-r265.md`,
  SHA-256 `c3b76e132ff8894181735bbd723cd329728af9b61fe4f7e0845a364e28fd11f0`;
- R265 handoff `tasks/agent-loop/inbox/consumer-lineage-simulation-r265.md`,
  SHA-256 `680e176e1e4ef36bb4b8093a1665370c47b038c9e1778dc7717d086c266e74bb`;
- R265 independent review
  `tasks/agent-loop/history/20261102-r265-independent-review.md`, SHA-256
  `cb1fb316dcf06c3f1cf1f754cdc4664841d593a735f8754390b66fc2fab4d993`;
- R70 original contract `tasks/agent-loop/sprints/ordinary-extrusion-invariant-20261019-r70.md`, SHA-256
  `4fa363c4dcbd97450b16dd2afb8b1bf2889f9faf00168d444205fe3633bee5cf` (historical target only; no new authority);
- R70 theory `notes/theory/2026-10-19-r70-ordinary-extrusion-invariant.md`, SHA-256
  `648b594fdf1cd989e7399db00f396c65ec82cc1b4d3585bcb68ce21b316021e7`;
- R70 reviewed closeout `notes/progress/2026-10-19-r70-closeout.md`, SHA-256
  `a93b2e5d38c03511c768dd704e57f3b616a1dafc591fe62a4155d64a06bbf4d8`;
- approved occurrence principles
  `notes/design/2026-10-11-yulang-inference-top-level-principles.md`, SHA-256
  `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`;
- approved occurrence association
  `notes/design/2026-10-12-intrusion-value-type-association.md`, SHA-256
  `531a9efae0ab7e03bfbd2f41cd7da86078e2fc8e67675d2c5c941972409f4e89`;
- R71 contract `tasks/agent-loop/sprints/raw-canonical-fiber-coverage-20261019-r71.md`,
  SHA-256 `a6bd6aa1ab369f77b728014cd51693b11c5b3f97f85aab392d6488c8834ac1fb`;
- R71 theory `notes/theory/2026-10-19-r71-raw-canonical-fiber-coverage.md`,
  SHA-256 `620947cece53ca60a7f8a2388a398f53850b835c79afd546bfdcfd10349a876e`;
- R71 closeout `notes/progress/2026-10-19-r71-closeout.md`, SHA-256
  `4b5f57b27d5bfbb0b3e4f7cfa86c03488f5d02f995c7f861dbe29e0d448edd3b`.

The R255 manifest has 36 pinned entries in total, of which exactly these 14
are Rust/HIR source paths authorized for source-body reads:

- `crates/yu-solver/src/lib.rs`
- `crates/yu-solver/src/candidate_context.rs`
- `crates/yu-solver/src/candidate_intrusion.rs`
- `crates/yu-solver/src/candidate_scheme.rs`
- `crates/yu-solver/src/candidate_source.rs`
- `crates/yu-solver/src/shadow_apply.rs`
- `crates/yu-solver/src/candidate_extrusion.rs`
- `crates/yu-solver/src/candidate_effect.rs`
- `crates/yu-solver/src/term.rs`
- `crates/yu-solver/src/candidate_scope.rs`
- `crates/yu-solver/src/candidate_value_graph.rs`
- `crates/yu-hir/src/shadow.rs`
- `crates/yu-hir/src/module/local_source.rs`
- `crates/yu-hir/src/module.rs`

Validate all 36 manifest hashes before the first source-body read and again at
freeze. Read the manifest in full, but only the 14 exact paths above may be
opened as Rust/HIR source. The other manifest entries do not become technical
dependencies merely because they are pinned there. No wildcard/glob searches. R230 notes, the R261 quarantined handoff, and all
R263/R264/R266 quarantined outputs are excluded.

## Source-input-join objective

Use a consumer-directed provenance reconstruction. Start from an actual reached
Value Replay→Function consumer and establish why its source occurrence requires
a particular canonical candidate. Preserve its authentic demand root, source/use
identities, exact ordered Replay inputs and RelationIds, pair/source/scoped
payload, every selected physical slot and raw prefix, aliases, merges, transform
witnesses, and the exact opposite inputs. Join this backward requirement to an
accepted source occurrence and actual transport paths.

R5's reviewed VD267 establishes only that retained Value relations have
`P_t(r)=K(r)` and removes the local Value discharge-time mismatch. It does not
prove candidate necessity, source reachability, matching opposite inputs, Effect
temporal simulation, complete source coverage or parent closure. Reuse VD267
only within its review. Do not assume R261/R262 results, infer necessity from
bucket membership, or collapse source/scoped/evidence identities. Success must
apply at unchanged R70/R71; a falsifier needs a fully accepted-source reached
consumer whose required lineage is absent after all competing paths are
accounted. Otherwise return the first exact missing equation and owner.

## Lanes, leases and resource envelope

Sole producer: fresh registered `prover`, requested Sol/high, unique identity
`/root/sol_r267_source_input_join`, no descendants. Maximum 540
seconds over three substantive stages; no reset or extension:

1. Work backward from the actual Value Replay→Function consumer. Derive why
   its source occurrence requires a particular canonical candidate, preserving
   ordered Replay inputs, demand root, source/use identities and retained
   dependencies.
2. Meet that requirement with the actual source occurrence and every selected
   physical slot, raw prefix, alias, merge, transform and opposite-input path.
   Prove the correspondence or freeze the first missing constructor equation.
3. Apply only a justified result at original R70/R71, then freeze exact hashes,
   remaining premises, source-pin gate and cessation receipt.

Only these new R6 outputs are leased; R5 outputs remain frozen history:

- `notes/theory/2026-11-02-consumer-lineage-source-input-join-r267.md`
- `tasks/agent-loop/inbox/consumer-lineage-source-input-join-r267.md`

Previous R267 assignments have 6,300 seconds fully charged. Allocate the final
900 seconds as 540 seconds for this producer, 300 seconds for a fresh
independent `compiler_referee` review after freeze, and 60 seconds for Luna
adjudication and integration. Total R267 allocation is exactly 7,200/7,200
seconds; there is no reset, extension or additional grant. The reviewer identity
is `/root/r267_source_input_join_review`, task name
`r267_source_input_join_review`, requested gpt-6.1-sol/medium, with no
descendants. Review canonical-candidate necessity, complete ordered-input
ancestry, source/scoped identities and the R70/R71 application; return
INCOMPLETE if the 300-second limit leaves claims unchecked. R266's separate
7,200-second envelope remains fully charged. No Astra, code/source edits,
tests, Lean, builds, probes, Cargo, scratch/cache, generated outputs,
runtime/quarantined reads or Git. Implementation remains
**NO_SAFE_CODE_SLICE**: R5 review found no approved-clause violation.
