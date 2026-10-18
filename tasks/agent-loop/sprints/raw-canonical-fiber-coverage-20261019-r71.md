# Sprint R71 candidate — raw/canonical bound-fiber coverage

Status at candidate evaluation: **NOT ACTIVATED; no work granted**. Activation, resources and exact leases belong in `tasks/agent-loop/current.json`. Luna owns the goal, candidate, dispatch, leases, review, adjudication and Git. Branch: `research/simple-sub-intrusion`; baseline candidate checkpoint: `f375fd737`.

## Fixed outcome

Prove or falsify a production-reachable coverage invariant at the R70 `candidate_extrude` Bound-copy seam. For each source bound selected from a physical row slot, distinguish (a) physical owner/side/item/slot, (b) the raw `BoundKey` retained as the evidence transport source, (c) the canonicalized child Visit key and (d) contextual fibers/provenance attached to raw and canonical keys after prior representative merges. Establish one of:

1. the exact raw source key has the fibers required by the copying operation;
2. an existing constructor/merge transport supplies those required fibers at the raw key; or
3. a production-reachable constructor-derived trace shows a required fiber is unavailable to the actual copy path.

Use a commuting-diagram invariant over physical slots, raw evidence keys, canonical keys and copied-bound emission. Include third-party rows whose references can be affected by merges, actual transport order, legitimate empty fiber lists, scoped/unscoped behavior, and recorded `MissingOriginAssociation` gaps. Do not infer fiber equality from endpoint equality or manufacture an identity alternative.

An inconsistent hand-built state is not a falsifier. A concrete failure is an implementation coverage result only; it is not automatically a source-unsoundness, evaluator, principal-type, Simple-sub A/B or parent counterexample. R70's reviewed conditional extrusion invariant is a reusable premise, while its all-path ENTRY-WF premise remains unproved. Keep general ENTRY-WF and later drain/ack outside this packet.

## Exact routes and owners

Entry route: the two `lib.rs::dispatch_live_item` calls at the frozen R70 baseline (`lib.rs:12572,12585` at R70 review), into `candidate_extrude`. The key seam is `candidate_extrusion.rs` selected physical slot construction and `Work::Bound`; physical insertion/readback and fiber/origin transport are in `candidate_extrusion.rs` / `candidate_effect.rs`; raw-to-canonical fiber transport is in `candidate_context.rs`; representative merge and third-owner handling are in `candidate_intrusion.rs`. Exact current pins below control; cited line numbers are locators only.

The proof lane must derive the actual attachment/lookup semantics from constructors, including where canonicalization mutates or retains raw bound keys, whether every physical bound slot is represented in context evidence, and what merge/canonicalization transports do for owners other than the merged row. The attack lane should minimize a reachable alias/merge trace or identify why candidate cases remain unreachable. Luna's map must trace physical-slot → evidence lookup → copy transport → copied physical emission at the two callers.

## Authority boundary

Approved top-level principles §§1–3 remain normative. In particular §1.1(2) requires occurrence-associated parent/copy identity retention. R70's closeout adjudicates the distinction: that parent identity requirement is normative; concrete Yulang storage/index/replay details are implementation evidence. This candidate makes no semantic change and grants no compiler/code/test/evaluator lane. Parent, Simple-sub A/B, R65/R66/R67, R50 and the annotated-Lambda consumer-placement question retain their existing states.

## Outputs and proposed envelope (not granted)

- Constructive coverage proof, 900s: `notes/theory/2026-10-19-r71-raw-canonical-fiber-coverage.md`; `tasks/agent-loop/inbox/20261019-r71-proof.md`.
- Complementary alias/merge countertrace, 300s: `notes/progress/2026-10-19-r71-fiber-countertrace.md`; `tasks/agent-loop/inbox/20261019-r71-research.md`.
- Luna physical-slot/evidence/transport owner map, 500s: `notes/progress/2026-10-19-r71-fiber-owner-map.md`; `tasks/agent-loop/inbox/20261019-r71-implementation.md`.
- Fresh compiler review 200s; fresh spec review 200s; Luna integration/closeout 300s. Total proposal 2,400s, Astra 0, no carryover.

No tests, builds, probes, benchmarks, source execution, code edits, expected-output changes or production admission are proposed. Check static source correspondence and exact pinned bytes only. If code repair appears necessary, stop and route a separate exact code lease to Luna after review; it is not authorized here.

## Candidate activation gate

This file is not authority to start. Before activation, Luna must compare these exact pins at `f375fd737` and current live bytes, reconcile all writers/leases from current runtime, confirm the R70 packets and closeout are frozen/pushed, verify exact non-overlapping output assignments and resource grant, and obtain the selector's acceptance of this exact candidate hash. Unknown writers keep quarantined leases. No reviewer starts before all author outputs are frozen.

## Direct dependency manifest

Hashes are direct SHA-256 pins at candidate baseline `f375fd737`:

`7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`  `notes/design/2026-10-11-yulang-inference-top-level-principles.md`
`4fa363c4dcbd97450b16dd2afb8b1bf2889f9faf00168d444205fe3633bee5cf`  `tasks/agent-loop/sprints/ordinary-extrusion-invariant-20261019-r70.md`
`648b594fdf1cd989e7399db00f396c65ec82cc1b4d3585bcb68ce21b316021e7`  `notes/theory/2026-10-19-r70-ordinary-extrusion-invariant.md`
`25f6a370ae1aa2d7a623a8aa0eaede979248d85b8c03c894fbf8f7850775e8db`  `tasks/agent-loop/inbox/20261019-r70-proof.md`
`6bb29d09fbf1440c964899815b95e06244cdd9ccc67ddf0dbe76d2016ec15b8e`  `notes/progress/2026-10-19-r70-extrusion-countertrace.md`
`4fbb70a13a205f4b0cef9990d7ad630c0bc956a611ebcdf4461a2886e1bd90e8`  `tasks/agent-loop/inbox/20261019-r70-research.md`
`c1b9a890d829edb77b065a09672b320c9fbe326e3d68c04a27d2fcf324dbd3a0`  `notes/progress/2026-10-19-r70-extrusion-owner-map.md`
`7987dd2e1018eec7d8bdbcadac8925e56007772f4709fc6dd98d8f5d6d7f1c1a`  `tasks/agent-loop/inbox/20261019-r70-implementation.md`
`a93b2e5d38c03511c768dd704e57f3b616a1dafc591fe62a4155d64a06bbf4d8`  `notes/progress/2026-10-19-r70-closeout.md`
`ff2c149bd71c783f874c150404bf199084858df631c21899d3abf53a258655bb`  `tasks/agent-loop/inbox/20261019-r70-closeout.md`
`fc0d948d884a406746066f3df8db257d5c6686505166b330bef839a9b9e2f35d`  `crates/yu-solver/src/candidate_extrusion.rs`
`6112343b4014c67dcb7d814a46412b3af3e1d12183924e891df4817a59f58da0`  `crates/yu-solver/src/candidate_effect.rs`
`42f89dcf5fa6d7095db1e220c89308a2a35f4e74b05c3e8821d4fb2e3e32b0ca`  `crates/yu-solver/src/candidate_context.rs`
`8a1f531be9fb5e5f160bf4f75c6eb98bbc35ce0a30acaf06424c531840504ba4`  `crates/yu-solver/src/candidate_intrusion.rs`
`8738c1b1699228b1a4dfd30af7e03d0afb100ca6124d23037c645246d888dc50`  `crates/yu-solver/src/candidate_value_graph.rs`
`9fdb36b4bbd66d702fbd3fcfaf593bfbc5dce0c52ff3252442aeb998bbb52c2a`  `crates/yu-solver/src/candidate_scope.rs`
`66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c`  `crates/yu-solver/src/candidate_source.rs`
`d4ff8a9e98eb667a5eb85aff9c0feec1f0227e86257bb56892493ac1d04a9278`  `crates/yu-solver/src/candidate_scheme.rs`
`2300400e87d0a487225f207d414ac71fa4f21c6f80279fea4f793e43c7809aee`  `crates/yu-solver/src/lib.rs`
`f3a0c3875ba1ba8c80ee48a405faf3dad22b57cba8930394f99181201bc58f60`  `crates/yu-solver/src/term.rs`
