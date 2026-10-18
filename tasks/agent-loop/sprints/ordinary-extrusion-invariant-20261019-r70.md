# Sprint R70 candidate — ordinary extrusion operation invariant

Status: **CANDIDATE NOT ACTIVATED — no work granted**. Luna owns the fixed parent goal, candidate, exact leases, adjudication and Git. Branch: `research/simple-sub-intrusion`; baseline: `880ad63704a9c041eb00c2caf5d1ca0dd97dbd5b` (R68 source-law wait pushed).

The original type-inference and evaluator goal, source domain, quantifiers and approved source meanings remain unchanged. Simple-sub A/B remain OPEN 0→0; R50 remains NOT ADOPTED. R69 and the annotated-Lambda consumer-placement decision remain pending and are independent of this packet.

## Fixed outcome

Prove or falsify a conditional **entry-to-return operational invariant** for successful calls to `candidate_extrude(initial, polarity, level)` from the two actual `dispatch_live_item` branches in `lib.rs` under `shadow-apply-candidate`. Do not generalize to direct test-only callers. The entry envelope must state the admissible initialized graph/session, endpoint and term/view validity, `candidate_graph` presence, `scoped_enabled` branch, active processing context, successful capacity/error assumptions, and typed-drain/worklist ownership. Cover anchor reuse; one row memo per `(kind-qualified endpoint, polarity, target level)`; fresh row allocation at target level; parent retention; selected-side copying; all four variance-correct Function ports; effect-view/tail remapping; incoming allowances; transported bound evidence; output/group retention; and the operation's final initialized-allowance replay loop.

Derive every claimed entry condition from those exact callsites and pinned constructors, or label it as an explicit unproved precondition. A conditional theorem may assume successful capacity/identity operations, but that assumption cannot hide missing structural validity, owner identity, mode, or queue invariants. If the entry premises cannot be justified or a transition cannot preserve them, report a partial invariant and leave this operation target OPEN.

The state relation must track source mutation, the operation-local row/structure/view maps, pending structural and bound work, newly installed bounds and their evidence, retained parent/output records, retained `ReplayOperation` children, actual typed-worklist transfers, and the returned endpoint. Distinguish children stored in the operation, transferred to the outer typed worklist, later drained, and acknowledged. The final loop may transfer a prefix and leave remaining children owned by the `ReplayOperation`; it does not synchronously drain the outer worklist. Trace the actual outer consumer to its handoff owner, but do not claim complete solver-drain termination. The pinned source audit is secondary historical evidence; exact implementation claims must be tied to the current pinned owners. The approved level-based requirement is the only normative claim in scope; Yulang effect, evidence, parent, and replay behavior are proved as current implementation properties unless a separately approved rule is identified.

A constructive result must give an explicit worklist simulation invariant and derive only input-sensitive bounds actually supported by it. Separate map/work discovery from bound-fiber/origin products, replay-child construction and transfer, term interning, and later drain work. A falsifier must give a concrete static transition trace showing a lost obligation, wrong kind/polarity/level, broken sharing, unsupported mutation assumption, or repeated work violating a stated bound. Distinguish structural preservation from complete source/evaluator correctness.

## Authority and non-goals

Use the approved Simple-sub ordinary level-based extrusion requirement in top-level inference principles §§1–3. The Simple-sub paper/source audit is secondary historical evidence; it does not adopt its implementation mechanically or discharge Yulang-specific effect, admission, parent, replay, or source obligations. The staged solution-relation package is a proof tool with no implementation authority. No source-law choice, representation/API change, production route, code repair, test, build, probe, benchmark, expected-output change, or evaluator implementation is included. If a concrete implementation violation of an established approved clause is shown, stop at that clause and request a separately reviewed Luna code lease; otherwise return `NO_SAFE_CODE_SLICE`.

## Method, lanes and resources (proposed; not granted)

- Constructive worklist proof: 900s, `notes/theory/2026-10-19-r70-ordinary-extrusion-invariant.md` and `tasks/agent-loop/inbox/20261019-r70-proof.md`.
- Complementary transition counter-reading: 300s, `notes/progress/2026-10-19-r70-extrusion-countertrace.md` and `tasks/agent-loop/inbox/20261019-r70-research.md`.
- Luna/high owner map and actual nested-consumer trace: 500s, `notes/progress/2026-10-19-r70-extrusion-owner-map.md` and `tasks/agent-loop/inbox/20261019-r70-implementation.md`.
- Fresh compiler review 200s; fresh spec review 200s; Luna integration/closeout 300s. Proposed cap 2,400 seconds, Astra 0, no carryover.

The fixed owner map must distinguish structural Function reconstruction, row/bound writes, effect-view remapping, origin/fiber transfer, parent retention, retained replay children, typed-worklist transfer, and later drain/acknowledgement. Replay children are stored under a retained `ReplayOperation`; the final loop can transfer a prefix to the caller's typed worklist and retain the rest, but does not drain that worklist synchronously. The owner map must trace the actual `lib.rs` typed drain and intrusion settlement only far enough to identify handoff/acknowledgement ownership. Any reachable helper/consumer owner within that boundary not in the frozen manifest blocks activation. Reviewers must be fresh and independent from authors. No proof/test result closes the original parent by itself.

## Direct dependency manifest

The hashes below are direct SHA-256 pins computed at baseline `880ad63704a9c041eb00c2caf5d1ca0dd97dbd5b`. This candidate is not a lease or worker launch.


`547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed`  `notes/design/2026-09-29-scc-intrusion-redesign-charter.md`
`0068fe7c17d3e575377279a867ce757098771e3ac2c9c7b332099493e823479c`  `notes/progress/2026-09-30-simple-sub-paper-mlsub-audit.md`
`f9645c5fe148f92e5fc0107222063562c3b35e8c55709fbe3d5d13f663cac800`  `notes/design/2026-10-03-staged-extrusion-solution-relation.md`
`7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`  `notes/design/2026-10-11-yulang-inference-top-level-principles.md`
`c1aedc8d21eb9c7014c86922542767c43b5eb95479ab76153fa3d1778a0454bd`  `notes/theory/2026-10-10-simple-sub-kind-qualified-graph-construction.md`
`8342602b14610e46ed4d26c94f477ba8557226417a63b99e4279e1d999969922`  `notes/progress/2026-10-10-kind-qualified-graph-review.md`
`f234b87510c7d8f2b4841bca9a53985a007d6d1d71587b5aa9a015243287c077`  `notes/theory/2026-10-15-extrusion-current-cut-activation-construction.md`
`cb1ffafb226d1b8443c6d6f3206b5205fc2ec760137e58e16b964f659d67797c`  `notes/theory/2026-10-15-extrusion-initialization-replay-invariant.md`
`efa7900907acd9a6c1da70fa841918e6aba3ed7977a1cece1c624259e49be8a3`  `notes/theory/2026-10-15-extrusion-parent-source-correspondence.md`
`ac668953145e809b486a080ec97c3f9c6c45b22d7914dbfd48ece61cdb796f05`  `notes/progress/2026-10-15-extrusion-initialization-replay.md`
`fc0d948d884a406746066f3df8db257d5c6686505166b330bef839a9b9e2f35d`  `crates/yu-solver/src/candidate_extrusion.rs`
`8a1f531be9fb5e5f160bf4f75c6eb98bbc35ce0a30acaf06424c531840504ba4`  `crates/yu-solver/src/candidate_intrusion.rs`
`6112343b4014c67dcb7d814a46412b3af3e1d12183924e891df4817a59f58da0`  `crates/yu-solver/src/candidate_effect.rs`
`42f89dcf5fa6d7095db1e220c89308a2a35f4e74b05c3e8821d4fb2e3e32b0ca`  `crates/yu-solver/src/candidate_context.rs`
`d4ff8a9e98eb667a5eb85aff9c0feec1f0227e86257bb56892493ac1d04a9278`  `crates/yu-solver/src/candidate_scheme.rs`
`f3a0c3875ba1ba8c80ee48a405faf3dad22b57cba8930394f99181201bc58f60`  `crates/yu-solver/src/term.rs`
`2300400e87d0a487225f207d414ac71fa4f21c6f80279fea4f793e43c7809aee`  `crates/yu-solver/src/lib.rs`
`8738c1b1699228b1a4dfd30af7e03d0afb100ca6124d23037c645246d888dc50`  `crates/yu-solver/src/candidate_value_graph.rs`
`9fdb36b4bbd66d702fbd3fcfaf593bfbc5dce0c52ff3252442aeb998bbb52c2a`  `crates/yu-solver/src/candidate_scope.rs`
`66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c`  `crates/yu-solver/src/candidate_source.rs`


## Candidate activation gate

Before any work starts, Luna must confirm this exact fixed outcome is supported by the pinned approved level/polarity rule and that all nested consumers are covered. The packet passes only if its manifest matches the frozen launch snapshot, the selector accepts this exact candidate, current runtime/state is reconciled, and each author/reviewer has an exact non-overlapping lease. The proposed 2,400-second envelope is not granted by this file.
