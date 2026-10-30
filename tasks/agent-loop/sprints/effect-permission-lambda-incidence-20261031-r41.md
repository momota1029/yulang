# EFFECT-PERMISSION-LAMBDA-INCIDENCE / R41

Status: primary-admitted bounded construction sprint. This packet extends only
the registration-to-Function argument-effect incidence through graph capture and
one exact module FreshUse. It grants no provider-arrival, Catch-residual,
subtraction, source-wide hygiene, whole-language, or production conclusion.

## Goal and exact missing edge

The R40 READ2 report and independent PASS establish that the admitted
`candidate_scheme.rs` FreshUse bodies reconstruct `Node::Function.children[1]`
and retain exact module-use routing, but do not establish that the original
computation-formal registration identifies that captured Function child.
R41 must retain that registration-labelled incidence at Lambda construction,
preserve it through graph capture, and demonstrate its exact child image under
FreshUse. Distinct registrations remain distinct even when their symbolic tails
or mapped rows coincide.

The `{signal | e}` / `{write | e}` witness remains a falsifier for any consumer
that treats shared row/tail-image equality as registration authority. Do not add
an equality-only permission consumer or make an actual-defect claim from the
conditional witness.

## Frozen baseline and dependencies

- Git baseline: `41a446c9e37d1cb9a4f88f7d8832f831d76cfd40` (`origin/yulang3` matched at admission).
- R40 report: `tasks/agent-loop/inbox/effect-permission-module-use-r40-read2.md`, SHA-256 `29ef9e594a9175299410db966f15e5689781568b6ca998055668aec152f58627`; independent PASS is recorded in `tasks/agent-loop/history/effect-permission-module-use-20261031-r40-read2-review.md`.
- `crates/yu-solver/src/lib.rs`: `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07`.
- `crates/yu-solver/src/candidate_context.rs`: `57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e`.
- `crates/yu-solver/src/candidate_scheme.rs`: `31ae5b9466a0f7bbd501c81e4401049ad9782636ba57ed89e8232e9149e8b707` (dirty admitted baseline; preserve every pre-existing byte/hunk).
- Read-only constructor dependencies: `candidate_source.rs` `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a`; `candidate_call.rs` `fdc39e01fa3665b4dc14e167973de63b275eb0280b831e340b6cdcee5ed0fc3f`.
- R39 finite constructor model: `notes/theory/lean/YulangClosure/ComputationPermissionEntryR39.lean`, SHA-256 `748cd52ff7962962940a3767ffa6a0b2d8def16d80e65e682282d1fa2b79560e`.
- Lean pin: `notes/theory/lean/lean-toolchain` = Lean 4.35.0. No Lake build/cache is authorized.

## Rust implementation lane

One writer: `/root/r41_rust`, Luna/high implementer; at most 1,400 seconds.
Write only:

- `crates/yu-solver/src/lib.rs` — `admit_lambda_fact` and directly necessary
  declarations only;
- `crates/yu-solver/src/candidate_context.rs` — retained passive provenance
  declarations/constructor only;
- `crates/yu-solver/src/candidate_scheme.rs` — capture, graph metadata,
  FreshUse child-image mapping and checked byte accounting only;
- `tasks/agent-loop/inbox/effect-permission-lambda-incidence-r41-rust.md` — sole
  handoff.

Read-only inputs may include the exact pinned dependency files above and the
R40/R39 reports. If implementation requires another source owner or any extra
write path, stop and return to Luna for a contract amendment. Preserve labels
for all registrations; do not use canonical row, spelling, family or tail
equality as a substitute. Account for the added retained allocation and its
failure path. No source tests, compiler tests, builds, Cargo, Lake, environment,
target, cache, worktree, scratch file or Git operation.

## Lean construction lane

One writer: `/root/r41_proof`, registered `lean_prover`; at most 1,400 seconds.
Write only:

- `notes/theory/lean/YulangClosure/LambdaArgumentEffectIncidenceR41.lean`;
- `tasks/agent-loop/inbox/effect-permission-lambda-incidence-r41-proof.md`.

State and prove the finite constructor/capture/freshening obligations needed by
the Rust handoff: a registration label names a particular Function node and
child index 1; capture preserves that association; freshening maps that child
through the exact use; distinct registration labels survive a shared row image.
Apply the result only to R39's retained-entry construction and the R40
structural FreshUse mapping. Keep the source/native correspondence premise
explicit; do not claim this finite model is a verified Rust interpreter or
closes the original source theorem. Preserve the original conditional witness.

Use the installed pinned Lean 4.35.0 executable with a bounded read-only stdin
check and complete `#check @` / `#print axioms` output for every theorem. Keep
all checker input in memory; no `.olean`, Lake cache, build, test, scratch or
environment. At most 1 CPU, 1 GiB, 120 seconds per invocation.

## Independent review, integration and stop gate

After both writers freeze and stop, one fresh reviewer gets at most 1,000
seconds and the sole write
`tasks/agent-loop/inbox/effect-permission-lambda-incidence-r41-review.md`.
The reviewer must check source constructor-to-label identity, capture and
FreshUse direction, accounting/failure behavior, theorem types/full axioms,
conditional shared-tail counterexample, omitted boundaries, and isolation of
the new Rust delta from the pinned dirty baseline. No worker self-certifies.

Luna has at most 1,000 seconds including review adjudication, shared-state
updates and up to 500 seconds for a coherent reviewed checkpoint. Only Luna
may stage explicit paths, commit and push. If the independently reviewed Rust
delta cannot be separated from unrelated dirty bytes, commit the reviewed Lean
and research artifacts alone and retain the source delta uncommitted.

Total sprint reservation: 4,800 seconds. No carryover or automatic renewal.
No Astra lane. If a lane blocks, continue the other. Stop at the first missing
constructor or theorem premise; do not infer provider arrival, Catch subtraction,
or broader language safety.
