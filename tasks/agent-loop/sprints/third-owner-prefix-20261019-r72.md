# Sprint R72 candidate — annotated recursive helper source case

Status: **CANDIDATE; not activated, no leases or resources granted.**
Revision 2 (selector-required manifest/outcome refinement). Branch
`research/simple-sub-intrusion`; baseline
`4916ef65306af1acec50df4cdab1d28f9ab0fa9f`. Primary and sole Git owner: Luna.
The exact source input is fixed below; static constructor eligibility is part
of the bounded outcome, not assumed from a test or fixture.

## Original parent and bounded outcome

Parent: the unchanged computation-forwarding preservation claim in
`notes/theory/2026-10-15-computation-forwarding-preservation.md` §§1, 6–7,
with its shared satisfying assignment, direct current-formal Name arguments,
arbitrary finite prefixes, repeated calls, simultaneous receiving entries,
and independent foreign-continuation obligations intact. The Simple-sub A/B
claims and full inference/evaluator obligations stay OPEN 0→0; R50 is NOT
ADOPTED.

This packet constructs or falsifies one source-qualified candidate history;
it cannot close the parent theorem. Use exactly this ordinary-mode source:

```yu
act io:
    our tick: int -> int

my outer (q:[io] int) = {
    my loop (x:[io] int) = {
        my direct = loop x
        my helper (y:[io] int) = loop y
        helper x
    }
    loop q
}
```

Outcome A: derive one actual constructor history with (1) a
third-owner physical slot and its occurrence-specific evidence, (2) a
genuinely source-qualified alias-changing merge, (3) a later production
`Work::Bound` lookup and copy, and (4) the independently justified consumer
obligation and provider-lineage correspondence for the copied relation.
Record the original raw key, physical owner/side/item/slot, canonical aliases,
source occurrence, exact work order and each consumer endpoint.

Bounded negative outcomes are explicit: (B) the exact source is rejected by an
authentic constructor, with its earliest rejection and owning premise; or (C)
the exact source is admitted and its relevant constructor prefix is traced,
but the requested third-owner/merge/copy pattern does not arise in this case.
Outcome C is case-specific non-applicability, not a general impossibility
claim or a source counterexample. Do not combine fixtures or invent initial
rows.

The result is conditional source/native evidence for this candidate only. A
case-specific exclusion or missing-fiber observation does not refute the
parent or establish a general coverage theorem. R53's operational lemmas may
be reused only with their actual premises, successful-prefix conditions,
indices, joint maps and scope instantiated in this source; its callable-local
argument and concrete group/capture conclusions do not transfer by analogy.
R55's direct-Name input is complementary evidence, not a substitute history.

## Authority, owners and source/native path

Top-level inference principles §§1–3 govern. Preserve ordinary Simple-sub
generation, accumulation, propagation, levels, occurrence-qualified
extrusion/intrusion and generalization. Do not enable the R50 scoped experiment,
change accepted source behavior, or promote candidate mode to production.

Static map must distinguish syntax/HIR local Lambda construction, annotation
resolution and direct formal Names (`yu-hir/src/module.rs` and
`yu-hir/src/module/{local_source,source_annotation}.rs`, `candidate_source.rs`),
ordinary `solve_mode(false,false)` and Apply admission (`shadow_apply.rs`),
formal/call registration and endpoint authentication (`candidate_call.rs`),
Function/endpoint construction (`term.rs`), source SCC qualification
(`candidate_value_graph.rs`), Local capture/FreshUse
(`candidate_scheme.rs`), production extrusion dispatch (`lib.rs`,
`candidate_extrusion.rs`), physical insertion/evidence and representative
merge (`candidate_effect.rs`, `candidate_intrusion.rs`, `candidate_context.rs`),
and the later actual consumer. Inspect `candidate_scope.rs` if the selected
consumer/transport operation uses it; otherwise show the ordinary-mode branch
that excludes scoped transformations. Separately label candidate-mode execution,
production-owner code and unproved reachability/completion. Inspect at least
two implementation owners; if there is no safe proof-independent code slice,
record `NO_SAFE_CODE_SLICE` with the owner-specific reason. This packet grants
no compiler, test, expected-output, semantic or production writes.

## Lanes and exact outputs

- Constructive proof/source lane, 600 seconds: `notes/theory/2026-10-19-r72-third-owner-prefix.md` and `tasks/agent-loop/inbox/20261019-r72-proof.md`.
- Luna source/native owner map and implementation correspondence, 500 seconds: `notes/progress/2026-10-19-r72-third-owner-prefix-owners.md` and `tasks/agent-loop/inbox/20261019-r72-implementation.md`.
- Fresh independent compiler/source review, 200 seconds; fresh independent spec review, 200 seconds; Luna adjudication/integration, 300 seconds.
- Total proposed envelope: 1,800 seconds; Astra 0; no carryover. Exact worker IDs, current-session receipts and actual model/effort observations must be recorded only after supported launches.

No tests, builds, probes, parser/solver executions, measurements, instrumentation,
code changes, semantic changes or expected-output edits. Static source reads,
dependency pin checks, proof derivation and frozen artifact review only. The
primary applies any bounded result to the unchanged parent and leaves every
unstated premise OPEN.

## Stop, review and activation gate

Stop at the fixed history or earliest authentic obstruction, 1,800 seconds,
any material authority/dependency/lease change, or user STOP. Unknown writers
retain leases and reserved resources. Freeze proof and owner outputs before
fresh review; authors cannot review their own results. Luna alone adjudicates,
updates current state, stages explicit paths, commits and pushes.

Direct dependencies below are SHA-256 pins at the stated baseline. They must
match current bytes and the frozen contract before activation. The selector
must accept this exact contract hash and candidate before Luna grants the
envelope. Candidate status alone authorizes no worker.

## Direct dependency manifest

```text
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81  notes/design/2026-10-11-yulang-inference-top-level-principles.md
d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79  notes/theory/2026-10-15-computation-forwarding-preservation.md
4fa363c4dcbd97450b16dd2afb8b1bf2889f9faf00168d444205fe3633bee5cf  tasks/agent-loop/sprints/ordinary-extrusion-invariant-20261019-r70.md
648b594fdf1cd989e7399db00f396c65ec82cc1b4d3585bcb68ce21b316021e7  notes/theory/2026-10-19-r70-ordinary-extrusion-invariant.md
a6bd6aa1ab369f77b728014cd51693b11c5b3f97f85aab392d6488c8834ac1fb  tasks/agent-loop/sprints/raw-canonical-fiber-coverage-20261019-r71.md
620947cece53ca60a7f8a2388a398f53850b835c79afd546bfdcfd10349a876e  notes/theory/2026-10-19-r71-raw-canonical-fiber-coverage.md
4b5f57b27d5bfbb0b3e4f7cfa86c03488f5d02f995c7f861dbe29e0d448edd3b  notes/progress/2026-10-19-r71-closeout.md
527b7ac19e446f964c234cf832db8daa0046d893d73d8078c007d7277d4c20d2  notes/theory/2026-10-19-r53-ordinary-mixed-capture.md
0ebbc5e0e0b1c85b3f89e9017d9759fc3c8cfec80aced22457ed2fdc5867b258  notes/theory/2026-10-19-r55-original-name-attack.md
d1aa7f1a1af5da50a78e012540e9c0f01878a3ec13bb43d2565f75ae279895a4  notes/progress/2026-10-19-r55-original-name-owners.md
c40ebde1755d300c83aafba0a81a85d19ed5200dfc2163ab72c8a3bb08baf29a  crates/yu-hir/src/module.rs
66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c  crates/yu-solver/src/candidate_source.rs
8738c1b1699228b1a4dfd30af7e03d0afb100ca6124d23037c645246d888dc50  crates/yu-solver/src/candidate_value_graph.rs
d4ff8a9e98eb667a5eb85aff9c0feec1f0227e86257bb56892493ac1d04a9278  crates/yu-solver/src/candidate_scheme.rs
fc0d948d884a406746066f3df8db257d5c6686505166b330bef839a9b9e2f35d  crates/yu-solver/src/candidate_extrusion.rs
8a1f531be9fb5e5f160bf4f75c6eb98bbc35ce0a30acaf06424c531840504ba4  crates/yu-solver/src/candidate_intrusion.rs
42f89dcf5fa6d7095db1e220c89308a2a35f4e74b05c3e8821d4fb2e3e32b0ca  crates/yu-solver/src/candidate_context.rs
6112343b4014c67dcb7d814a46412b3af3e1d12183924e891df4817a59f58da0  crates/yu-solver/src/candidate_effect.rs
2300400e87d0a487225f207d414ac71fa4f21c6f80279fea4f793e43c7809aee  crates/yu-solver/src/lib.rs
30cbf8b9a3ab11e9448d2ea5aa47ee40aa3d80d0ee2bceec1e1b1abb6b1393d3  crates/yu-solver/src/candidate_intrusion_tests.rs
d685b44e43a1bca796a0299b2b19117d562245788206ede229b879801f94f6b5  crates/yu-solver/tests/candidate_computation_source_plan.rs
ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5  crates/yu-hir/src/module/local_source.rs
b8462b66eac24a48b6fc5e931a3d8b7c38c19bb8b2f1a7cdc4ecd9a8a7a1117f  crates/yu-hir/src/module/source_annotation.rs
5bbcf27d51906814ba38b2cca2066807d285d0b1817f0ea6e04d70c4a5c8a5cb  crates/yu-solver/src/shadow_apply.rs
e038ad0dfc4b12bd0d513d6cd6b34cee6b2b062d8b33368bc1c0dcdef980d479  crates/yu-solver/src/candidate_call.rs
f3a0c3875ba1ba8c80ee48a405faf3dad22b57cba8930394f99181201bc58f60  crates/yu-solver/src/term.rs
9fdb36b4bbd66d702fbd3fcfaf593bfbc5dce0c52ff3252442aeb998bbb52c2a  crates/yu-solver/src/candidate_scope.rs
```
