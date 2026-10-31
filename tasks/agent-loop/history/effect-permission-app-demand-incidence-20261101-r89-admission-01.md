# R89 admission — source App-demand incidence

Sprint: EFFECT-PERMISSION-APP-DEMAND-INCIDENCE/20261101-R89
Admission revision: 01
Branch/baseline: yulang3 / e56d1b618c2025859f5ab912d7ba3168634aaaed (origin/yulang3 at admission)
Contract: tasks/agent-loop/sprints/effect-permission-app-demand-incidence-20261101-r89.md (sha256 c036d191f2748d971862aab638ac92bd7147ac8ff27289a68e35ed1d7c23e45b)
Input manifest: tasks/agent-loop/sprints/effect-permission-app-demand-incidence-20261101-r89-inputs.json (sha256 86727cb01dc42a4b51148e1dff9c75a4f37af01c7862a56afa18eed25ca2a256; 33 pinned inputs)
User authority: continuing Rust/Lean goal; preserve original source semantics, effect hygiene, and quantifiers.

## Prior outcome and reason for R89

R88 is closed as a bounded source-incidence obstruction, not parent closure. Independent review passed the exact missing-incidence result. Its Lean candidate failed the primary direct check and remains unaccepted; R88 used its full 2/2 invocation cap. The source result locates the owner behind the missing bridge in the primary App/Call constructor path. See tasks/agent-loop/inbox/effect-permission-source-joint-lift-r88-review.md (sha256 41dde35dcea564d100d06d941f0ae6779028f6f0b610847e648d49d2578379e1).

R89 follows the exact producer chain named by the dispatcher: candidate_source recipe input -> shadow_apply Apply branch and DirectionalIntroduction -> candidate_call retained provenance -> candidate_context_seed slot 0. The work asks whether those actual fields identify the original App witness telescope, full Call checks, qualification, and value/effect obligations. A symbolic ID or Boolean is not semantic evidence.

## Exact source pins

The source lane has read-only scope over the four manifest-pinned files below. All are pinned as current working-tree bytes; candidate_context.rs is a dirty working version and remains read-only.

- crates/yu-solver/src/candidate_call.rs — 32230 bytes, sha256 fdc39e01fa3665b4dc14e167973de63b275eb0280b831e340b6cdcee5ed0fc3f.
- crates/yu-solver/src/candidate_context.rs — 265778 bytes, sha256 a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905.
- crates/yu-solver/src/candidate_receiver.rs — 292001 bytes, sha256 6004fd4252d15d8c99ac0e9f97582347a0de94946f497c0e29520d872e77dae2.
- crates/yu-solver/src/candidate_source.rs — 212009 bytes, sha256 96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a.
- crates/yu-solver/src/shadow_apply.rs — 276524 bytes, sha256 c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a89a78cf72ff.

Proof scope is limited to the two exact output paths in the contract and pinned existing source definitions/R88 results. No source file, dependency, build target, checker, compiler behavior, or semantics may be changed.

## Live roster and state

At admission no R89 lane is live. The immediately preceding roster showed R88 proof, R88 source, and R88 independent review completed; the dispatcher completed its recommendation. R88 STOPPED dispositions and terminal paths were archived by receipt before this admission. Existing UNKNOWN workers, FROZEN leases and QUARANTINED paths remain unchanged. No capacity override was applied and no path lease was released.

Primary exact leases are recorded in tasks/agent-loop/current.json. Proof call cap starts at 0/2. The source lane is read-only on its four pinned inputs and writes only its assigned handoff. No worker starts a nested team.

## Resource and environment boundary

Total 3,600 seconds: proof 1,400; source 1,000; independent review 700; primary 500. Astra 0. At most two direct Lean invocations, each no more than 120 seconds with Lean 4.35.0, -j1 -M1024, one thread. Each exact flattened input requires primary preflight and frozen candidate review. No Lake, build, tests, temporary source/output file, cache, project copy, worktree, environment or /tmp write. No unrelated dirty path is staged.

## Fixed success and open limits

Deliver either the actual source/native incidence equation plus a clean checked App inversion and theorem/axiom audit, or the exact first missing source supplier with dependent fields plus the clean checked App inversion. No assumed source/native bridge or local law restating the goal. Preserve one original witness and all source clauses. A/B, complete source/native joint lift, Rust implementation and production remain OPEN absent their separate evidence.
