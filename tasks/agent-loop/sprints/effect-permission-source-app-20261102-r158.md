# R158 original App admission and effect correspondence

Status: ACTIVE under the standing Rust/Lean goal.
Baseline: `78728e6774e97ca84ae3008888c2d1028ebb744c` (`origin/yulang3`).
Keep the original soundness/effect-hygiene goal, source domain, quantifiers,
semantics and production gates fixed. Budget: 2400 seconds aggregate.

## Fixed inputs and outcome

R157 is complete and pushed. The source-only Rust observer at `shadow_apply.rs`
SHA `99d67895c250e5d79fb774728867fe2fc88c4dc22df9bfc38ac9fd1aeb0908e5` is
independently reviewed PASS; it has not been compiled or tested. The Lean
`SourceAppAdmissionR157` candidate SHA
`98cf8e4948ce1f9a72ebdcca7d5d2488b052df33c62947e067b10a616af5c00f` and
handoff SHA `c4ffed123a67939bd5914b2c227a916f3f69718290933dd3a15c6357bd951ca9`
are independently reviewed PASS for source-only evidence; seven roots remain
unchecked. The prior sprint's dispatcher incident and exclusion are recorded in
`tasks/agent-loop/history/20261102-r157-dispatcher-boundary-incident.md`.

Proof outcome: construct the lawful descriptorFormation/admission law at the
original App binder, or freeze the exact missing constructor implication. The
construction must preserve all Local premises, both finite Checking judgments,
both arbitrary operands, descriptor/interface choices, exact occurrence and
conditional singleton-formal origin. Apply any useful lemma to the original
source obligation; a restatement of App preservation as a premise is not
progress.

Rust outcome: establish source-native correspondence for the exact App binder
and its two operands through committed `candidate_call.rs` and immutable-HEAD
`candidate_scheme.rs`, then determine whether an approved end-to-end Rust slice
exists. If not, return an owner-specific `NO_SAFE_CODE_SLICE`. Do not read the
dirty worktree scheme or any quarantined runtime path or blob.

## Exact assignments and boundaries

- Lean prover writes only
  `notes/theory/lean/YulangClosure/SourceAppAdmissionR158.lean` and
  `tasks/agent-loop/inbox/effect-permission-source-app-r158-lean.md`. Continue
  the seven R157 candidates, inspect actual source constructors, preserve all
  choices/premises, and record theorem types plus first remaining source law.
  No Lean/Lake/checker invocation or generated output in this packet.
- Rust source lane reads only `crates/yu-solver/src/candidate_call.rs` and
  immutable-HEAD `crates/yu-solver/src/candidate_scheme.rs`; writes only
  `tasks/agent-loop/inbox/effect-permission-source-app-r158-rust.md`. It may
  cite the reviewed R157 observer, but cannot inspect current dirty receiver,
  scheme or quarantined runtime files. No Rust code, tests, Cargo/build, or
  Git commands.
- Primary owns this contract and `tasks/agent-loop/current.json`. Fresh
  independent Lean review attacks quantifiers, witness choices and hidden
  assumptions. Fresh compiler review attacks operation identity, FreshUse map,
  Apply occurrence, polarity and exact BoundKey correspondence. No worker
  commits/pushes.

## Limits and stop conditions

No source/test/build execution, Lean, Cargo, Lake, checker, format, worktree,
target/cache or toolchain/dependency change. Do not read unrelated paths,
quarantined paths or immutable blobs. Parent soundness, whole effect hygiene,
source/native closure and production remain OPEN. STOP on a missing source law,
counterexample, review rejection, lease/resource conflict or unknown writer.
Next dispatcher trigger: sprint outcome, source-law obstruction, or a material
authority/dependency/resource/integration change.
