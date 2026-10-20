# Sprint R144 candidate — production extrusion entry validity

Status: **CANDIDATE; no proof lease or resources granted.** Revision 6.
Branch `research/simple-sub-intrusion`; baseline
`e23eb3cd6628aa27e7693c2a93fe13659cc2e4f6`. Luna is primary, authority owner
and sole Git integrator. Candidate follows R143 closeout and dispatcher
selection of `R70-ENTRY-WF-1`.

## Parent and fixed outcome

Preserve the original inference/evaluator objective, source domain and
independent quantifiers. The parent remains `R70-ORDINARY-EXTRUSION-ENTRY-RETURN-1`;
Simple-sub A/B remain OPEN 0→0 and R50 remains NOT ADOPTED. R143 established a
finite successful-public-return barrier but does not establish valid extrusion
entry data retroactively. R70's operation body result remains conditional on
its entry predicate.

Fixed outcome: derive that **both actual production `candidate_extrude`
call branches in `dispatch_live_item` receive the structural state required by
R70's existing conditional entry-to-return theorem**, from real initialized
sessions and source/task constructors. The covered domain includes every non-test candidate entry under the
`shadow-apply-candidate` feature that can reach either call branch:
`CandidateInference::solve`, `solve_scoped_experiment`,
`solve_operation_v1_research`, and the public
`solve_receiving_residual_experiment`. Keep scoped-enabled and operation-v1
mode constructors distinct. The receiver
assembly has distinct scheduling history: it omits `active_roots/active_uses`
and routes Module actions through `route_internal`; prove its constructor path
separately. Any additional reachable production root must be named and pinned. Prove
constructor preservation for the entry envelope or identify the first
constructor that lacks a needed supplier. Do not replace a missing argument
with a premise merely by naming it. Keep mode quantification explicit and
separate ordinary-only conclusions from scoped-path conclusions.

The entry invariant must cover the admissible initialized session/graph; correct
Value or Effect row kind and range; valid endpoint and term view; candidate
mode and scoped branch; active processing context; current typed-worklist/drain
owner; effect view/member, incidence and term lineage; and replay-head/child
ownership. Preserve raw source slots and establish the canonical fibers and
transported evidence required at the exact raw transport point. State successful
capacity/identity assumptions explicitly, without hiding structural or owner
validity behind them.

This packet does not re-prove `candidate_extrude`'s full worklist simulation,
prove source/native correspondence, infer soundness/principality, establish
termination, or close R70. Any missing branch remains UNFINISHED/OPEN. A
counterexample must be reachable from an actual constructor and one of the two
production call sites; arbitrary well-formed structs and direct test-only
callers do not count.

## Caller and constructor closure

Start at all four named candidate entry constructors in `shadow_apply.rs`,
including public receiver-experiment initialization and assembly.
Follow each reachable source-action path through both
`dispatch_live_item` branches at `lib.rs:12565–12593` into
`candidate_extrude`. Trace each field of the entry invariant back through:

- `shadow_apply.rs`, `lib.rs`, `term.rs`: public mode, collection/session
  initialization, row/term constructors, typed task and drain dispatch;
- `candidate_source.rs`, `candidate_value_graph.rs`, `candidate_call.rs`:
  accepted source scheduling, identities, formals and source-produced calls;
- `candidate_scheme.rs`: captured graphs, fresh uses and retained Local/module
  routes;
- `candidate_receiver.rs`: public receiver-experiment initialization, retained
  source-action assembly, direct Module routing and omitted SCC active roots;
- `candidate_scope.rs`: scope transformer and effect-scope/input-route
  constructors used by scoped source and replay paths;
- `candidate_effect.rs`, `candidate_extrusion.rs`: effect views/captures and
  the two production entry call branches;
- `candidate_intrusion.rs`, `candidate_context.rs`: merges, context imports,
  attachment, replay heads and child ownership.

Use the frozen R70 entry premise and R142/R143 reviewed results only within
their exact scopes. Any further constructor/helper needed by the proof is a
stop condition: return to Luna for a sequential revision and fresh prospective
review before using it.

Required constructor-preservation output: a table with entry field, initial
supplier, preserving constructors/transitions, exact dispatch use, and any
residual premise. In particular, retain raw originals while checking whether
all required canonical fibers are represented at the exact raw evidence
transport source after prior merges.

Falsifier: a production-reachable call has a wrong-kind/out-of-range or stale
reference, invalid/invisible/ill-polarized term, invalid view/member/incidence
or fiber chain, unsupported transported evidence, or replay-head/child owner
not justified by its constructor history.

## Authority and review gates

Initial implementation status: **NO_SAFE_CODE_SLICE**. Read-only proof/source
audit only; no code, tests, builds, compiler execution, observers,
instrumentation, semantic changes, expected-output edits or production
promotion. A constructor-authentic violation stops this packet and requires a
separate exact repair amendment.

Exact outputs:

- Contract: `tasks/agent-loop/sprints/extrusion-entry-validity-20261020-r144-rev6.md`.
- Theory: `notes/theory/2026-10-20-r144-extrusion-entry-validity.md`.
- Proof handoff: `tasks/agent-loop/inbox/20261020-r144-proof.md`.
- Progress: `notes/progress/2026-10-20-r144-closeout.md`.

Before activation, obtain fresh prospective compiler/source and spec/authority
reviews of this exact contract SHA and complete pin set. After proof and parent
application freeze, obtain fresh independent final reviews. Reviewers must not
author the proof. CLEAN receipts certify only the finite entry-validity result;
R70's operation-body theorem, entry/fiber coverage beyond this bridge, R71,
R72/R73, Simple-sub, inference/evaluator and production remain open.

## Proposed resource envelope

Proposed hard cap **1,800 active seconds**, zero Astra, no carryover:
preparation/direct pin validation 180; prospective reviews 120; constructive
proof 900; Luna complementary constructor audit 180; final reviews 240;
closeout 180. Unknown lane time is charged at its full reservation. No renewal.
Preserve three legacy UNKNOWN identities, board quarantine and held R104 lease.
No proof producer starts before CLEAN prospective reviews, refreshed pin
validation and explicit Luna activation.

Stop on a new unpinned constructor, dependency drift, a defect needing repair
authority, a broken invariant, exhausted budget or user STOP. Only Luna writes
`current.json`, adjudicates and integrates exact paths. Routine Git needs no
separate user permission.

## Frozen direct dependency manifest (baseline/live SHA-256)

```text
838d862dd34fe2b2bd70c5d92c5ce9af0aa98f10f8b6a8eddf313ae798686543  crates/yu-solver/src/shadow_apply.rs
c75bf47b3d0d87e99d4365a587e6b90d5d05d05c335db16880cb2943b8b25985  crates/yu-solver/src/lib.rs
f3a0c3875ba1ba8c80ee48a405faf3dad22b57cba8930394f99181201bc58f60  crates/yu-solver/src/term.rs
cbc39315f4243b0bae1db74976cf94282bc94cd28b9eb463699c085f421065f7  crates/yu-solver/src/candidate_source.rs
19da9779e3e7866f5891e019e1cd343136ae0115bd1c47a02a7e7ee0cdfa80e0  crates/yu-solver/src/candidate_value_graph.rs
e038ad0dfc4b12bd0d513d6cd6b34cee6b2b062d8b33368bc1c0dcdef980d479  crates/yu-solver/src/candidate_call.rs
2e64dc8781189b4da21c30f4d1b3208aaef48ca247cae55fb7e77e68b5857850  crates/yu-solver/src/candidate_scheme.rs
6112343b4014c67dcb7d814a46412b3af3e1d12183924e891df4817a59f58da0  crates/yu-solver/src/candidate_effect.rs
fc0d948d884a406746066f3df8db257d5c6686505166b330bef839a9b9e2f35d  crates/yu-solver/src/candidate_extrusion.rs
8a1f531be9fb5e5f160bf4f75c6eb98bbc35ce0a30acaf06424c531840504ba4  crates/yu-solver/src/candidate_intrusion.rs
002b9d86e26cfda6fdf094ea4d161501849a7127d55c2d147d408a781b9fd28d  crates/yu-solver/src/candidate_context.rs
9fdb36b4bbd66d702fbd3fcfaf593bfbc5dce0c52ff3252442aeb998bbb52c2a  crates/yu-solver/src/candidate_scope.rs
620b09011ec4dc4bfa71998e2b6fc1498b9299b3056662fdaa80b17376ba23c3  crates/yu-solver/src/candidate_receiver.rs
4fa363c4dcbd97450b16dd2afb8b1bf2889f9faf00168d444205fe3633bee5cf  tasks/agent-loop/sprints/ordinary-extrusion-invariant-20261019-r70.md
648b594fdf1cd989e7399db00f396c65ec82cc1b4d3585bcb68ce21b316021e7  notes/theory/2026-10-19-r70-ordinary-extrusion-invariant.md
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81  notes/design/2026-10-11-yulang-inference-top-level-principles.md
25f019b0d96d8fefe5a7332458226cada068b6d4a07462138c4b3634441b0fdd  tasks/agent-loop/sprints/replay-completion-20261020-r142-rev1.md
5f1715db8ccef8777f89d9b64e8625efead68974be53beb8f55a84a86a014a2c  notes/theory/2026-10-20-r142-replay-completion.md
cbaa0c7e79ca9c04b4325b8358ec17664deb51eb4dc620be0c7e242041b44c26  tasks/agent-loop/inbox/20261020-r142-proof.md
900fb928cd8f1960d90ec7d6fdaac503aebe38e12848f5429f35719f0e91b16e  notes/progress/2026-10-20-r142-closeout.md
e189a89f4a9974492ceb6999ff5c3d890aa5250882c014fb3a9f1c9608a7b5c5  tasks/agent-loop/sprints/public-replay-publication-20261020-r143-rev1.md
36625135b5311ab9f0f9491c03b26c3417a8bcd0e52e0bf0e4de6cc391e1a6be  notes/theory/2026-10-20-r143-public-replay-publication.md
04e953149bbde970587162258af2a014bc077702f08ec5913d1fd3b01b38452f  tasks/agent-loop/inbox/20261020-r143-proof.md
96c1a7e7b7858f6d3ec5d0b5560e1a29048781cf2ba99b1368ad8fc47f899370  notes/progress/2026-10-20-r143-closeout.md
```

Rev1 SHA-256: `7b1d5e1110e74cbc5776505546e1a197a50c3435243b5256ff7cd0cc228ca8a5`.
Rev2 SHA-256: `d875a2e424b8d7c0b8eb3d8947a320aab87dd1bd7ee7253f995653a682f0cc31`.
Rev2 added `candidate_scope.rs`; rev3 added `candidate_receiver.rs` and
spelled out the ordinary, scoped-enabled, and receiver-assembly roots.
Rev3 SHA-256: `608e2c8a05e5cd45bf9613ec443cbff5e85c350e3b0b1717c6823ef8ede5face`.
Rev4 SHA-256: `9f879b2de08122c0cf2baf5964da613200bfeff11aa6dfa48f986a980f949cf3`.
Rev5 SHA-256: `3ba7a0cab46d5c3317fcf00d93c7d04c676715ce18b334069788684c6bb81eff`.
Rev6 fixes the exact output path and removes duplicate revision provenance.
The manifest is pinned to the stated baseline and live bytes; any further
required dependency needs another sequential revision and fresh prospective
review. No lease or resource grant is implied.
