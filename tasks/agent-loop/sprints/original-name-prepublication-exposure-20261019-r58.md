# Sprint original-name-prepublication-exposure-20261019-r58 — annotation before first provider capture

Status: ACTIVE after primary approval; revision 1. Approval receipt is recorded in `tasks/agent-loop/current.json`.
Branch / baseline: `research/simple-sub-intrusion` / `13e1e65da38e64992bc53f9e7f2cd2e12696ee3d`.
Primary: `/root`, session `current-conversation-2026-10-19-r58`.
Authority: original `notes/theory/2026-10-15-computation-forwarding-preservation.md` §§1,6–7; `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1,1.1–1.2,4–5; `notes/design/2026-10-11-yulang-inference-top-level-principles.md` §§1–5; reviewed bounded R57 result. R50 remains NOT ADOPTED.
Contract revision / SHA-256 / primary approval receipt: revision 1; SHA-256 is recorded in `tasks/agent-loop/current.json`; primary approval followed clean baseline, all 22 dependency pins matching, source-domain gate confirmation and live writer/lease reconciliation, before any worker writes.

## Original outcome and success evidence

Original parent: computation-forwarding preservation §§1,6–7, with original quantifiers and source domain unchanged. Parent forwarding preservation and Simple-sub A/B remain OPEN 0→0. This sprint isolates one source-constructor gate; it does not narrow or close the parent.

Exact candidate module (one top-level module):

```yu
act io:
    our tick: int -> int

my forward (t:[io] int): [io] int -> [io] int = t
my outer (q:[io] int) = forward q
```

The candidate retains an explicitly annotated Computation formal `t`, a resolved direct formal-Name body, a whole-current-formal argument `q` to `forward`, and a first-order whole-function annotation. The resolved `io` declaration is part of the candidate identity. Original formal permission, whole-function argument annotation and whole-function result annotation are separate source positions; equal printed rows do not identify their native endpoints. The open incoming effect `E` stays open: `[io]` permission is not a closed cap on the formal's incoming effect.

Fixed question: **Does definition-level annotation processing expose or change eligibility of the original direct-Name provider closure before its first authentic capture, and what exact owner transition establishes that?**

Success evidence is one of:

1. A source-qualified trace that identifies module action scheduling and execution, queued work/drain order, actual annotation compatibility premise, exact original Function/AE/Name/RE endpoints, levels and nongeneric metadata, every physical write, and the first authentic `forward` capture/FreshUse; then establishes whether the annotation action has already changed or exposed that closure; or
2. A precise constructor-specific exclusion showing why this annotated top-level definition cannot enter the original parent domain.

A compatibility failure, failed constructor prefix, emitted-but-not-executed `Action::Annotation`, endpoint equality by spelling, source provenance alone, or retained-but-unadmitted bound is not a successful exposure witness. If compatibility, schedule order or physical provenance cannot be established from static owners, freeze that exact obstruction. Do not execute a parser, solver or compiler to fill the gap.

R57 established only bounded successful ordinary constructor-prefix preservation through a second same-provider Local capture. It did not establish full solve success, all-source preservation, top-level definition annotation order or this pre-publication transition. Use R57 only within those limits. R55's missing completeness seam identifies module `Action::Annotation` and local `Action::LocalAnnotation`; this sprint investigates only the exact definition-level `Action::Annotation` candidate above.

## Two continuing lanes

- Sol/high proof/source-domain lane: trace exact parent membership and the annotation-to-first-capture transition; attempt the prescribed counterexample/exclusion check; apply only an authentic result to the parent and name the next missing owner. Exact outputs: `notes/theory/2026-10-19-r58-provider-publication-exposure.md` and `tasks/agent-loop/inbox/20261019-r58-proof.md`.
- Luna/high primary read-only source-owner lane: independently map HIR formation/resolved `io`, source action emission and execution/scheduling, annotation compatibility/action owners, physical writes to original rows/levels/metadata, and first capture/FreshUse. Exact outputs: `notes/progress/2026-10-19-r58-provider-publication-owners.md` and `tasks/agent-loop/inbox/20261019-r58-implementation.md`.
- Astra: none; the named risk is an exact source/schedule/physical-owner trace, not a bounded core proof requiring Astra.
- No compiler implementation slice is approved. Both productive lanes are read-only investigations of the same fixed gate with disjoint outputs. No code, semantic changes, tests, parser execution, solver execution, builds, runtime, probes, measurements, expected-output/diagnostic changes, or production promotion.
- Related in-envelope steps may refine constructor-domain evidence, action/execution order, endpoint ownership and authentic-capture qualification. Any changed source, added annotation constructor, new dependency, or semantic premise returns to Luna before dependent writing.
- Parent application must preserve original quantifiers/domain and distinguish source typing, native correspondence, implementation and production. Even an authentic exposure or case-specific exclusion does not close parent §§6–7 or Simple-sub A/B by itself.

## Permissions and resources

Exact output leases are the four paths listed above, plus this contract for Luna only. No wildcard, scratch or generated-file leases. Read dependencies are the manifest below. Current state, task ledgers and unpinned sources are not silently added as mathematical dependencies.

Resource cap: 1800 seconds aggregate: Sol 600; Luna source-owner audit 500; fresh compiler referee 200; fresh spec auditor 200; Luna integration 300. No carryover. Actual durations/CPU/RSS are recorded only when observed. No descendants. Reviews begin only after author lanes stop and all targets freeze. Reviewer identities must be fresh relative to R58 authors; requested and observed model/effort remain separate, UNKNOWN when unavailable.

No tests/builds or process probes are allowed. Static reads, line/owner tracing and SHA-256 checks only. Stop on goal outcome, exact obstruction, failed source-domain gate, changed dependency/authority, budget, user STOP or session end. Unknown writers retain quarantined leases and reserved resources.

## Frozen seams and handoff

Frozen manifest SHA-256 dependencies:

```text
d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79  notes/theory/2026-10-15-computation-forwarding-preservation.md
a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18  notes/design/2026-10-10-annotation-effect-hygiene-integration.md
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81  notes/design/2026-10-11-yulang-inference-top-level-principles.md
7766aff08cedde1ebc796b8927cd1d44f459df72a632e0c0d35d4bfcd28d335e  notes/theory/2026-10-15-computation-formal-permission-construction.md
38d42183fdc4f2c0136112d8b305816241d8f449367b473e4de3a5135dc49895  notes/design/2026-10-10-local-self-recursive-binding.md
db5e8115e3f853e7831ffaf525e4c794bdca9892a18d7fb153f395451f94a40b  notes/theory/2026-10-19-r55-original-name-core.md
4c292a24c7fba19c40587fcc2cb9374fdbff3dd7059533548e4e1be1420546d1  tasks/agent-loop/sprints/original-name-core-20261019-r55.md
9603acbd00419111821aa0e808258d5b744f5afc0b2d8601be2cc7ffd8f883ff  notes/theory/2026-10-19-r57-original-name-two-capture.md
b8fb35aa130304ab459b1c8ead188c5ebd6c86bb177420842f279a1d17f4c5a9  tasks/agent-loop/sprints/original-name-two-capture-20261019-r57.md
b61c52cc4afa02b98828df76cc8182d15a60cb5d240dde4a73085f50ae08e0ce  notes/progress/2026-10-19-r57-original-name-owner-trace.md
ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5  crates/yu-hir/src/module/local_source.rs
c40ebde1755d300c83aafba0a81a85d19ed5200dfc2163ab72c8a3bb08baf29a  crates/yu-hir/src/module.rs
b8462b66eac24a48b6fc5e931a3d8b7c38c19bb8b2f1a7cdc4ecd9a8a7a1117f  crates/yu-hir/src/module/source_annotation.rs
66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c  crates/yu-solver/src/candidate_source.rs
6112343b4014c67dcb7d814a46412b3af3e1d12183924e891df4817a59f58da0  crates/yu-solver/src/candidate_effect.rs
d4ff8a9e98eb667a5eb85aff9c0feec1f0227e86257bb56892493ac1d04a9278  crates/yu-solver/src/candidate_scheme.rs
fc0d948d884a406746066f3df8db257d5c6686505166b330bef839a9b9e2f35d  crates/yu-solver/src/candidate_extrusion.rs
8a1f531be9fb5e5f160bf4f75c6eb98bbc35ce0a30acaf06424c531840504ba4  crates/yu-solver/src/candidate_intrusion.rs
42f89dcf5fa6d7095db1e220c89308a2a35f4e74b05c3e8821d4fb2e3e32b0ca  crates/yu-solver/src/candidate_context.rs
8738c1b1699228b1a4dfd30af7e03d0afb100ca6124d23037c645246d888dc50  crates/yu-solver/src/candidate_value_graph.rs
5bbcf27d51906814ba38b2cca2066807d285d0b1817f0ea6e04d70c4a5c8a5cb  crates/yu-solver/src/shadow_apply.rs
2300400e87d0a487225f207d414ac71fa4f21c6f80279fea4f793e43c7809aee  crates/yu-solver/src/lib.rs
```

R58 output hashes, live receipts, and review hashes are appended only after each exact artifact freezes. Independent compiler and spec reviewers check source-owner correctness and authority conformance, respectively; no author self-review. The closeout receipt records the bounded before/after result, remaining parent premise, all output/dependency hashes, worker cessation and omitted dynamic evidence. Luna owns current-state synchronization and Git. Inspect exact outbound paths/range before any commit or non-forced push.

Next dispatcher consultation: at this sprint's close, or earlier only for a material counterexample, source-domain failure, authority/dependency/lease/resource change, integration seam or goal replanning. Parent remains OPEN until the complete original obligation is discharged.
