# FORCE-VIEW-SOURCE-OWNER-20261025/r1 — source producer investigation

Status: **FROZEN by Luna**. Branch: research/simple-sub-intrusion. Baseline:
57fbf68f79581349f994bf0db9cd9235d8edd298. This is a read-only source
investigation with one handoff output. It makes no language or implementation
decision and grants no compiler, Lean, or production authority.

## Parent and bounded claim

The unchanged parent is the complete Lean proof of Yulang semantics and type
inference in notes/theory/lean. The immediate prerequisite is the Force/View
producer gap recorded by r9. The target is to determine whether accepted
source-owned construction already supplies a concrete producer-to-consumer
derivation for Force of a nested or captured View-wrapped thunk, including
distinct force.effect and force.result positions, dynamic occurrence identity,
current owner/world inputs, and Ret/Req/Fail/Bad behavior.

Return exactly one of:

1. A source-derived producer-to-consumer derivation with every field and
   inference identified; or
2. The exact missing definition and original source owner, plus the smallest
   unresolved semantic question if accepted sources do not determine it.

Separate an absent executable construction from ambiguity in accepted
behavior. Draft-only behavior cannot be adopted by this packet.

## Frozen inputs

| Input | SHA-256 |
|---|---|
| docs/yulang-operational-type-safety-ja.tex | a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b |
| notes/design/2026-10-02-typed-boundary-realization-draft.md | 1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb |
| tasks/agent-loop/sprints/lean-complete-call-20261025-force-view-interface-amendment.md | 8d7ad0d788d559d5efa3e7b75953221d8a7bd9586ffe09ac1f705fe6a3862406 |
| tasks/agent-loop/sprints/lean-complete-call-20261025-r9-outcome.md | 66d5f30ee3323b33b6943b5817ee48cdd69e20bfd793ea65b08df125567a7579 |
| notes/theory/lean/YulangClosure/CoreSyntax.lean | dff3e5851c9ef971ec404f9542d684074a13623bb0820c3a5e4d5da072783ece |
| notes/theory/lean/YulangClosure/ControlSyntax.lean | 1f937e4c51b79d1a2dc4a2291a1e3f5797403eae5975a53a42d574867a1690f0 |
| crates/yu-core/src/shadow_typed_evidence.rs | dabcbd07b2d1baace0227cb94164db871fdadc1089b1854b396dfb464d26ce95 |
| crates/yu-hir/src/shadow.rs | b964bab6dcdb7ebeca9f964c134ac8fb041c928c20ce0a895fea6b6af0fbb93e |

The typed-boundary draft is explicitly Draft and grants no full source
realization implementation authority. The operational source cites it as a
candidate definition, not proof that an executable producer exists. Start
from these frozen inputs and follow only their exact source-owner references.
If a dependency changes, stop and return the changed path and hash to Luna.

## Exact task and falsifier

Trace one nested or captured View-wrapped thunk through:

1. Delay creation and storage of its body and latent graph.
2. Creation of force.effect and the distinct force.result correspondence.
3. Later current-world re-observation and dynamic View occurrence creation.
4. Force entry, body execution, event-time observation, and normal result.
5. Req suspension and continuation reconstruction.
6. Fail and malformed raw Force / Bad behavior.

For each transition, label facts as directly supplied by accepted source,
constructed by an identified producer, derived by a rule, or still assumed.
Track static syntax labels separately from dynamic view/owner identities. Track
the Force exposure separately from complete Call Views and preserve literal
typed suffix behavior where the source requires it.

The two Rust source owners are inspection targets, not presumed producers:
crates/yu-core/src/shadow_typed_evidence.rs and
crates/yu-hir/src/shadow.rs. Establish whether they construct a source
judgment/evidence record or merely consume assumed ports and report unresolved
premises. Identify the exact upstream owner that could supply missing data.
Do not infer authority from a shadow/test carrier.

Independent falsifier: an accepted nested/captured View-wrapped thunk requires
a force port, occurrence, owner, mapping, or lifecycle operation that no cited
producer supplies without an extra premise. If the record uses an arbitrary
adapter map, endpoint type equality, or a nondeterministic world relation as
the missing construction, it has not closed the obligation.

## Role, lease, and resource

- One author: Sol/high researcher, maximum 600 seconds.
- Exact output lease: tasks/agent-loop/inbox/20261025-force-view-source-producer-investigation.md.
- Luna adjudication reserve: maximum 300 seconds.
- One fresh independent reviewer after freeze: maximum 300 seconds.
- Fresh total cap: 1,200 seconds; no r9 balance carries over. Astra: 0.
- No concurrent author is needed. The researcher must not spawn descendants.

This is a read-only audit apart from the single leased handoff. Do not modify
compiler, Lean, design, contract, current-state, or other task files. Do not run
builds, tests, Lean, Cargo, native commands, or Git. No semantic adoption,
self-certification, proof claim, or production approval is permitted.

## Handoff and stop conditions

Freeze revision 1 of the exact leased output with source locators, dependency
hashes, a complete producer/consumer trace or exact obstruction, facts versus
assumptions, the smallest remaining premise and its owner, the independent
falsifier, checks not run, actual worker/model observations, resource use, and
an explicit write-cessation receipt.

Stop if the source requires a new semantic choice, a changed dependency,
another output lease, or any executable/compiler work. Return the exact issue
to Luna. Do not invent a producer, narrow the supported source domain, or
authorize the next formalization/implementation step.

## Gates after this packet

S call_step_erasure and C call_raw_successor_coverage remain OPEN. They may be
considered only after Luna adjudicates this source result, freezes an
authorized Force producer/consumer interface, grants any exact representation
work, and checks that interface in serialized dependency order. Call A/B,
Original inference A/B, source/native correspondence, principality, termination
and the full parent remain OPEN.
