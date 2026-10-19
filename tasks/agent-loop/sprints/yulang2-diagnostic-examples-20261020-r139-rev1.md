# Sprint R139 — unchanged curated Yulang2 diagnostic examples

Status: CANDIDATE pending prospective independent review and Luna activation.
Branch/baseline: research/simple-sub-intrusion /
0e7a71b23b86390390e608282b217ef354930e86.
Primary and sole Git integrator: Luna.
R138 is closed unfinished. R135 brace semantics remains undecided and is outside this packet.

## Goal and fixed outcome

The user goal is proof-backed Yulang inference/evaluation with frequent primary-owned commits and pushes, while broadening unchanged Yulang2 Web-demo sample coverage. This sprint takes two unchanged examples from the curated Yulang2 Web Playground Error Examples category:

1. Type Mismatch — annotated int initialized with true.
2. Parameter Provenance — an integer argument flows to a function formal whose body demands Bool by using it as an if condition.

The source bytes are copied from the pinned Yulang2 source templates below. They must remain byte-identical. R139 adds shared Y3 fixtures, CLI coverage, Web selectors and WASM smoke assertions. These examples are expected to be rejected by type inference before runtime construction; they are compatibility examples, not newly successful evaluation cases. Success requires rejection at the candidate type-conflict stage. Parser errors, unsupported lowering, missing-definition/runtime failures, fuel exhaustion, or accepting either program falsify the outcome. Diagnostic wording, ordering, identity and spans are not frozen.

The source provenance is Git blob e6bec9fe44d673ccbf98af078ef4562c9267ef6c at repository revision a58eefc31e22141574b6f20c6a5748151c6d79f1: /home/momota1029/rust/yulang2-oracle-capture/web/playground/src/main.ts, SHA-256 baa040dcd9ac837864b4dd0d8ac6c79bfffc3fe2466bcda43b8db14305dcaf90. The external repository worktree is dirty; use only the pinned Git blob. Do not modify or clean that checkout.

Exact decoded source templates:

~~~yu
// A type annotation makes the expected type explicit.
my answer: int = true
~~~

SHA-256: 9e5f99a3b96452f8775ab5657f489443430afcc4a5f85b048425e5b9400e3f2f

~~~yu
// The argument is an int, but the body uses value as a condition.
my choose(value) = if value:
    "yes"
else:
    "no"

choose 42
~~~

SHA-256: ed3339fe27331014efdc1a698c156a9b3bca04b8879ce9343b66cac0ec6e9a07

No brace syntax is added. R132/R133/R135 histories are not reclassified. The R135 decision remains pending; R139 neither selects nor supersedes it. All inference/evaluator/Simple-sub A/B, source/native and production gates remain OPEN.

## Source-to-proof obligation

The finite derivation connects each unchanged HIR source to the existing candidate conflict and preparation boundary:

- Type Mismatch: the source annotation supplies an Int endpoint while the initializer's Boolean literal supplies Bool; candidate conflict prevents graph publication.
- Parameter Provenance: the one-argument PatternCallTail header introduces the authentic choose formal; condition lowering adds a BoolNegative demand for that formal; the 42 call argument supplies Int, yielding an incompatible demand on the same original formal. Module preparation returns the conflict before RuntimeProgram construction or evaluator execution.

Inspect current producer, propagation and consumer owners, including plain_binding_header, LocalSourceForm::If in candidate_source.rs, candidate conflict reporting/preparation and execute. Distinguish direct annotation conflict from argument-to-formal provenance. This finite source correspondence is not general type soundness, principality, completeness or production-admission proof. Existing open obligations retain their original owners.

## Exact lanes and output leases

Constructive proof lane: configured prover, requested Sol/high, zero descendants. Leases:

- notes/theory/2026-10-20-r139-yulang2-diagnostic-examples.md
- tasks/agent-loop/inbox/20261020-r139-proof.md

Luna owns the implementation lane serially and remains the only committer and pusher. Exact implementation leases:

- web/playground/examples/yulang2-type-mismatch.yu
- web/playground/examples/yulang2-parameter-provenance.yu
- tools/inference-playground/tests/cli_yulang2_diagnostic_examples.rs
- web/playground/src/main.ts
- web/playground/index.html
- web/playground/smoke-test.mjs
- tasks/agent-loop/inbox/20261020-r139-implementation.md

No compiler, parser, solver, runtime, semantic, expected-output or design-authority edits are leased. If either source fails before the type-conflict stage, freeze evidence and return the exact owner gap; do not patch compiler files under this packet.

Independent prospective spec/authority and compiler/source reviews must both be CLEAN before Luna activates author lanes. Freeze all proof and implementation outputs and direct dependencies before fresh final spec/authority and regression/source review. Prospective reviews each reserve 60 seconds; final reviews each reserve 90 seconds. Reviewers cannot be authors or coauthors. Luna adjudicates findings before verification.

## Direct dependencies at baseline

Baseline is the live Y3 worktree HEAD above. Every following SHA-256 must match both that Git tree and live bytes at activation and before integration.

~~~text
baa040dcd9ac837864b4dd0d8ac6c79bfffc3fe2466bcda43b8db14305dcaf90  /home/momota1029/rust/yulang2-oracle-capture/web/playground/src/main.ts (pinned Git blob e6bec9fe44d673ccbf98af078ef4562c9267ef6c)
153a23ecaa68fd150d8bd0cc0316f3723e1cb5d98a6e3026aadef2bfd08fd907  crates/yu-hir/src/module.rs
d9f516993c579ae8f4dd905abb8400ffc0769072a904a4b4c8d4ffbefcde6442  crates/yu-hir/src/module/local_source.rs
cbc39315f4243b0bae1db74976cf94282bc94cd28b9eb463699c085f421065f7  crates/yu-solver/src/candidate_source.rs
2e64dc8781189b4da21c30f4d1b3208aaef48ca247cae55fb7e77e68b5857850  crates/yu-solver/src/candidate_scheme.rs
e038ad0dfc4b12bd0d513d6cd6b34cee6b2b062d8b33368bc1c0dcdef980d479  crates/yu-solver/src/candidate_call.rs
838d862dd34fe2b2bd70c5d92c5ce9af0aa98f10f8b6a8eddf313ae798686543  crates/yu-solver/src/shadow_apply.rs
b404eacf20e30a59affb2ac49afab2d489d50ce25510bfd93b90352e4379ed3c  crates/yu-solver/tests/candidate_conditionals.rs
75b38435f4634ee35b3e14a54fb4d021b78bda834b4fd53965302a73309e0100  tools/inference-playground/src/main.rs
a0769f77feac552304f0516b0742637f51660c0bb8bf9391d18ae0f9de5e2473  tools/inference-playground/src/lib.rs
09fecc7c8b8a152ec49d939517d3dcd4951fad48a2909c1faee15bf95cc7a773  tools/inference-playground/tests/cli_demo_identity.rs
ba647e27df494d15e4bf8edbfc82e4cb8a506b62396c649a26ae6212a0fdea2d  web/playground/src/main.ts
9edd1341444f4ff15a12733313202d3255d6b470b4736a52d85708591d0d5a03  web/playground/index.html
8ec96d938a0b3f3286f9de26743204c0a944eff26ea6bd892c6a598a6d8e216d  web/playground/smoke-test.mjs
b4d68db12c1845f23b5c8a3231249952470868d22d9489a8590270a57de77a3f  web/playground/examples/yulang2-identity-island.yu
f10e7e57cdfc165436a89326c9f069f19aa0afd24cea80b2b570463fcc553487  web/playground/examples/yulang2-ordinary-islands.yu
~~~

Hashes establish bytes only, not the source claim.

## Verification and resources

No worker runs tests, builds, compilers, solvers or runtimes. After clean final reviews Luna runs one serial CLI command, then one Web command, stopping on first failure:

1. timeout 120s cargo test -q -p yu-playground --test cli_yulang2_diagnostic_examples
2. timeout 240s npm --prefix web/playground run check

The CLI test asserts both fixtures fail with a type-conflict classification, empty stdout and no syntax/lowering/selection/runtime failure. WASM smoke checks both selected error examples are rejected at the same candidate type-conflict boundary, while preserving all existing smoke expectations. It does not freeze exact diagnostic details.

Single reserved envelope: 2,100 seconds, zero Astra, at most one heavy process; tests/builds are serial.

~~~text
Preparation and corpus/pin validation 180s
Proof 600s
Implementation 540s
Prospective and final independent reviews 300s total
Verification 360s (CLI 120s + Web 240s)
Closeout and integration 120s
Total 2,100s
~~~

Preserve all UNKNOWN legacy workers, reservations and quarantined paths. Account actual elapsed time; no previous sprint, Astra or UNKNOWN time carries over. Stop on any pin mismatch, source rejection before the candidate conflict, new semantic/source authority need, overlapping writer, unknown descendant, review finding not repaired within allocation, first verification failure or cap boundary.

## Integration boundary

On success, record a finite diagnostic-example compatibility result, clearly distinct from successful evaluation examples and every parent theorem. On failure, record the exact stage and leave the examples unsupported; do not change their bytes or treat an earlier parser/lowering error as the intended type error. Only Luna updates compact state, stages explicit intended paths, inspects the full outbound range, commits and pushes non-forced. Closeout preserves R135's pending decision and every original inference and production gate as OPEN.
