# Sprint R267 — consumer-lineage temporal closure

Status: admitted revision 2 under the unchanged Yulang inference soundness and
Rust goal. Luna's admission is recorded in
`tasks/agent-loop/history/20261102-r267-r2-admission.md`. Branch `yulang3`;
fixed baseline `8d646ac2ed171e13a529e25e035fc75f91678b0b`.

## Original obligation and outcome

Preserve the full accepted source domain, original parent theorems and
quantifiers, Simple-sub A/B, independent satisfying assignments, shared
witnesses, F1/FK1 and foreign continuations. Parent/A/B delta remains zero.
The unchanged edge is inference soundness → R70 copy correspondence →
`R71-RAW-CANONICAL-FIBER-COVERAGE-1`.

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

### Packet and proof/source dependencies

These are the complete direct technical dependency list. The revision-1
contract is admitted only as superseded assignment history; its incomplete
read-authority list has no force over this revision. The stop receipt records
that no source was read and no result was produced.

- this R267 revision-2 contract;
- `tasks/agent-loop/sprints/consumer-lineage-closure-r267.md`, SHA-256
  `5902b752eb54c88517e8b8a9b388ad459b8198ec5ad5054d16666fe857a04f19`;
- `tasks/agent-loop/history/20261102-r267-read-authority-stop.md`, SHA-256
  `1e0c53dcccf9f12155c914b34cae75ee27a7964d3d520d7a856304c89f451c56`;
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

The R255 manifest specifies exactly 36 Rust/HIR source paths and their hashes.
Validate every hash before the first source-body read and again at freeze. The
manifest may be read in full, but only those exact 36 paths may be opened as
source. No wildcard/glob searches. R230 notes, the R261 quarantined handoff,
and all R263/R264/R266 quarantined outputs are excluded.

## Lanes, leases and resource envelope

Sole producer: fresh registered `prover`, requested Sol/high, unique identity
`/root/sol_r267_consumer_lineage_r2_7e90d3f`, no descendants. Maximum 1,200
seconds over three substantive stages; no reset or extension:

1. State TEMP265/Z265 verbatim and derive their exact transport/consumer
   equations at the actual source occurrence join.
2. Construct the accepted-source occurrence join and account for all
   competing physical slots, aliases, merges and temporal residual paths;
   prove the simulation or construct the accepted-source missing-lineage
   witness.
3. Apply the result at original R70/R71 and freeze hashes, exact remaining
   premises, source-pin gate and cessation receipt.

Only these outputs are leased:

- `notes/theory/2026-11-02-consumer-lineage-closure-r267.md`
- `tasks/agent-loop/inbox/consumer-lineage-closure-r267.md`

The previous R267 assignment's 1,200 seconds are fully charged. Retain the
original, undispatched 300-second independent `compiler_referee` review
reservation; do not add another reservation until this producer freezes.
This revision adds at most 1,200 producer seconds, making the R267 total
charged/reserved 2,700 of its 7,200-second envelope, with 4,500 unallocated.
R266's separate 7,200-second envelope remains fully charged. No Astra,
code/source edits, tests, Lean, builds, probes, Cargo, scratch/cache,
generated outputs, runtime/quarantined reads or Git. Implementation remains
**NO_SAFE_CODE_SLICE**: R265 review found no approved-clause violation.
