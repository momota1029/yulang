# Sprint `npair-constructor-owned-replay-certificate-20261018`

Status: CANDIDATE pending Luna's fresh author receipts. Branch `research/simple-sub-intrusion`; baseline `7087de449`. Parent `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` remains OPEN. Preserve original quantifiers, source domain, fixed-c, F1/FK1, N-Transport, Call, soundness, principality, termination, and production boundaries. Astra0; no rollover.

## Fixed outcome

For both actual same-source FreshUse routes, authenticate a constructor-owned chain of evidence through captured source, imported snapshot, FreshUse admission and concrete physical fiber, exact Replay constructor and fibers, actual Function consumer C and all four port admissions. Require explicit identities for `p`, copied `p1`, Replay upper `h`, Replay child `q`, and consumer `C`. Never infer a path from matching metadata or incoming-edge counts.

Before source edits, produce and independently review this owner map. Numeric coordinates stay `NOT OBSERVED` until the exact fixture runs.

| Evidence | Primary owner | Required relation |
|---|---|---|
| Captured source | `Capture::bound` in candidate scheme | source relation, complete BoundKey, captured snapshot |
| FreshUse transport | prepare/restore path | imported antecedent, mapped relation `p1`, term/scope/input maps, actual Transport child |
| Physical output | `candidate_extrusion.rs:446–599` (read-only) | admission→emission→row/lane/index and value physically stored there |
| Restored fiber | `candidate_context::bound_relations` | complete destination BoundKey and relation membership |
| Replay | `candidate_context_begin_replay` and recipe registry | exact lower/upper/child, both input fibers, retained recipe |
| Consumer | `candidate_function_port_admit` | actual C, field, typed endpoint, operation, child scope/transformer |

First decide from actual constructors whether p1→h exists or p1=h by relation identity. FreshUse and Replay may independently contribute to one shared q; do not force them into a single incoming ancestry spine. If no p1→h path is retained, state that exact gap and derive a constructor certificate for the shared conclusion before implementing a replacement. Root/term equality never substitutes for relation identity.

## Lanes, leases and budget

**Proof — Sol/prover, 720s.** Write only:
- `notes/theory/2026-10-18-constructor-owned-replay-certificate.md`
- `tasks/agent-loop/inbox/20261018-constructor-owned-replay-proof.md`

Use the previous CLEAN conditional proof and frozen review as inputs, then map every equation to the actual constructor owners above. Establish the shared-conclusion/FreshUse/Replay topology or identify the first absent owner record. State exact fixture coordinates as unobserved until runtime. No parent theorem closure unless the exact original obligation is proved.

**Implementation — Luna/implementer, 1920s including 360s protected runtime; authoring cap 1560s.** Write only:
- `crates/yu-solver/src/candidate_context.rs`
- `crates/yu-solver/src/candidate_scheme.rs`
- `crates/yu-solver/src/shadow_apply.rs`
- `crates/yu-solver/src/tests/candidate_graph_call.rs`
- `crates/yu-solver/examples/research_scoped_formal_replay.rs`
- `notes/progress/2026-10-18-constructor-owned-replay-certificate.md`
- `tasks/agent-loop/inbox/20261018-constructor-owned-replay-impl.md`

Source-owner mapping and its early independent review must be CLEAN before writing checker code. Then use explicit constructor references; authenticate the physical slot's actual index content and full bound membership; verify all four port-child scoped flows and identity/stamp_input/protect_body equations; add separate actual-record mutations for snapshot, slot content, fiber membership, dependency kind, endpoint, and flow. Preserve solver semantics. No new storage unless checked accounting, rollback, and review are in scope.

**Independent reviews, 600s:** source-owner map review 120s before code; final frozen proof/compiler delta review 480s after author STOP. Reviewers are fresh and do not edit. **Primary integration 120s; reserve 240s.** Total cap 3600s: proof720 + implementation1920 + review600 + primary120 + reserve240. No rollover.

## Exact runtime commands

Only after the frozen proof and implementation receive CLEAN reviews, run once, sequentially, with each timeout <=120s and full primary-owned stdout/stderr/exit metadata:

1. `timeout 120s env YU_CALL_REPLAY_OBSERVER=1 cargo test --offline -p yu-solver --features shadow-apply-candidate authentic_demand_capture_tests --lib`
2. `timeout 120s env YU_CALL_REPLAY_OBSERVER=1 cargo test --offline -p yu-solver --features shadow-apply-candidate candidate_graph_call --lib`
3. `timeout 120s env YU_CALL_REPLAY_OBSERVER=1 cargo run --offline -p yu-solver --features shadow-apply-candidate --example research_scoped_formal_replay`

Logs: `tasks/agent-loop/runtime/20261018-replay-fiber-consumer.{helpers,graph,example}.{stdout,stderr}.log` and `.meta.json`. No retry after failure.

## Dependencies and stop conditions

- Previous conditional proof CLEAN: `notes/theory/2026-10-18-replay-fiber-consumer-certificate.md`, SHA `691a537b441bff0947b47886f423199e9558740778d81e50858eedd85e3e3614`.
- Previous compiler review BLOCKING/MAJOR findings: `notes/progress/2026-10-18-replay-fiber-consumer-closeout.md`.
- Unapproved candidate snapshot: commit `1958cf20e`, review/state checkpoint `7087de449`; exact frozen path hashes are in `tasks/agent-loop/inbox/20261018-replay-fiber-consumer-impl.md`.
- PR #11 policy merge: `27a7e00d4b581f18987bb2a3cbf2e492789c2293`; no authority or semantics changed.

Stop if owner mapping cannot distinguish relation identities, physical fiber data is unavailable, shared conclusion proof is unsound, pins drift, a negative authenticates, a command fails, or budget is uncertain. Candidate passes and conditional proofs do not close parent conditions.

## Revision 2 — physical slot provenance lifecycle (2026-10-18)

Rev2 supersedes only the implementation lease and physical-slot evidence method
above. The original outcome, source domain, fixed-c, proof map, solver semantics,
review gates and total 3600s cap stay unchanged. Rev1 remains immutable history;
its CLEAN owner-map review authenticates the constructor topology only, not the
new slot lifecycle. Parent closure remains 0.

The exact physical-vector owner is `candidate_insert_bound_with_evidence` in
`candidate_extrusion.rs`. Add this one implementation write lease. Prefer a
fixed-size per-emission record of the BoundKey actually read back from the
addressed physical slot and the validation phase. Do not copy either bounds
vector or add a parallel registry. `candidate_context.rs` owns record type,
accounting, and later comparison. The constructor must read all eight lane
variants through their actual vector/index and compare the observed endpoint
and complete BoundKey against the admission. An input argument copied into a
record is not physical-slot evidence.

Before selecting constructor-only versus freeze-time validation, inspect and
record whether every rollback that truncates/reuses physical slots also rolls
back the corresponding evidence emission. If append-only slot identity and
paired rollback are established, the constructor readback may be retained. If
not, add a single freeze-adjacent validation hook in `lib.rs` while vectors are
still live; lease `lib.rs` only for that hook, then retain the freeze-time read
result for post-solve verification. Never claim the discarded post-solve
vectors were directly inspected. Include slot reuse, out-of-range indices,
missing/replaced records and pre-freeze content changes in mutations.

Implementation assignment may write the existing seven paths plus
`crates/yu-solver/src/candidate_extrusion.rs`; `crates/yu-solver/src/lib.rs` is
conditionally leased only if the lifecycle audit requires freeze-time checking.
No other path is added. From the 1560s authoring ceiling, allocate at most 180s
to the lifecycle audit, 900s to implementation and mutations, and retain 480s
for repairs. Runtime360, review480, primary120 and reserve240 remain protected.
Do not reset any spent time; if remaining authoring capacity is insufficient,
stop at the exact missing evidence.

Fresh final review must check actual addressed slot reads for each lane,
out-of-range and different contents, rollback/reuse, evidence loss or
replacement, freeze-time change where applicable, correct complete BoundKey
comparison and unchanged insertion/solver behavior. It must also retain the
existing fresh-use, fiber, Replay and four port-flow checks. Runtime remains
forbidden until frozen proof/compiler review is CLEAN. The rev1 proof map's
`candidate_extrusion.rs` hash is historical; final review checks the revised
owner against current source. No proof statement or parent theorem is inferred
from the new implementation record.

## Revision 3 — conservative resource restart, same compiler outcome (2026-10-18)

Rev3 preserves the rev2 scope and exact implementation lease set. The previous
3600s envelope is now **retired and charged in full for accounting** because
part of the implementation audit was not metered. This is a conservative
reservation, not a claim that 3600s elapsed. No old time rolls over. A fresh
3600s tranche is granted, for a total accounting ceiling of 7200s:

| Fresh allocation | Seconds |
|---|---:|
| Luna implementation authoring | 1800 |
| Sol source/lifecycle proof | 600 |
| Fresh final independent review | 480 |
| Protected runtime commands | 360 |
| Luna integration/state/Git | 180 |
| Reserve | 180 |

The 1800s authoring tranche has hard stage grants: lifecycle audit 180s,
implementation 900s, actual-record mutation evidence 480s, coherent freeze
240s. Record monotonic start/end at each boundary. An unmetered or interrupted
stage consumes its entire grant; never infer remaining time from “time since
resume.” No automatic extension. The implementation author must ACK rev3 and
its remaining grant before any write. Runtime stays unavailable until fresh
final proof/compiler reviews are CLEAN.

The added Sol proof assignment writes only:
- `notes/theory/2026-10-18-constructor-slot-lifecycle.md`
- `tasks/agent-loop/inbox/20261018-constructor-slot-lifecycle-proof.md`

It audits the pinned pre-edit source at rev3 opening and proves or refutes the
lifecycle needed to trust slot readback: every physical row append's owning
route/checkpoint, every path that can truncate/reuse its lane, paired candidate
evidence rollback (including non-transactional paths), and whether a
constructor-time observation remains valid through freeze. Follow concrete
owners and exact branches; state the first counterexample if any. This is
source/lifecycle evidence for the certificate only, not a new language rule,
parent theorem proof, numeric fixture result or production approval. Cap 600s;
no Astra, code writes, tests, Cargo or runtime. The final reviewer must be fresh
and must not be this proof author or implementation author.

Existing conditions, constructors, solver semantics, source domain, fixed-c,
quantifiers, production boundaries, runtime commands and no-rollover rule are
unchanged. Parent theorem closure stays 0 unless independently established in
its original scope; neither new lease nor resource tranche counts as progress.
