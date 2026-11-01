# R156 source-admission and effect-hygiene continuation

Status: **ACTIVE** under the standing user-authorized Rust/Lean goal.
Baseline: `f1490e4892e2a3319da485c4339aaa2e4c391a92` (also `origin/yulang3`).
Parent: original Yulang inference/source soundness and effect hygiene. Preserve
the original source domain, A/B claims, quantifiers, semantic authority,
production gates and expected outputs.

## Fixed evidence

- R153 source-only Rust checkpoint is pushed. Its observer additions are
  uncompiled and untested; no claim of solver behavior or production follows.
- R154/R155 receiver/scheme worktrees contain held diffs. Do not read, stage,
  compile or change them in this sprint. Runtime `machine.rs` and `receiving.rs`
  remain quarantined to UNKNOWN_WRITER; do not read or change them.
- The ordinary-admission test `r106_named_result_function_is_captured_freshened_and_consumed`
  is already present in pushed `candidate_effect.rs`. It checks structural
  capture, FreshUse and consumer export, but has not run and is not a soundness
  or complete effect-hygiene proof. Do not duplicate it or weaken its assertions.
- R104's flattened syntax gate passed historically with complete type/axiom
  output. R105's flattened bridge gate failed before its declarations because
  flattening leaked `Contracts.Step` into another module. R106's module-faithful
  batch stopped on an output allowlist rejecting Lean's transient
  `.olean.tmp.7`; neither failure is evidence against the bridge theorem.
- `OriginalEffectHygiene` is a proved constructor/consumer component, not the
  whole effect-hygiene theorem. Arbitrary `LocalAdmissions.logical`, a Prop
  definition, or a candidate observer does not supply source admission.

## Bounded outcomes

### Rust source path

Read-only audit the pushed ordinary-admission test and committed readback APIs
to determine whether an exact operation-origin → capture → FreshUse → actual
consumer link can be checked without a production API change. Report an exact
usable API path or the first missing constructor/readback relation. Do not
reinspect the held receiver/scheme diffs or quarantined runtime paths. No Cargo
run is authorized while the held crate diffs are present in the worktree. Any
new Rust code requires a separate exact lease and independent review after this
audit; no semantic repair is presumed.

### Lean effect-hygiene path

Using the frozen R104/R105 bridge and R112/R114 admission candidates, map exact
module imports and theorem roots for `SourceLogicalOwnerBridgeR105`,
`SourceScopedAdmissionR112`, `SourceAdmissionTransportR114`, and
`OriginalEffectHygiene`. Identify the first original source law still missing
for applying their checked components to effect hygiene.

Prepare a module-faithful, bounded Lean validation plan that preserves module
command scopes, source bytes, imports and theorem declarations. It must explain
and safely handle Lean's transient `.olean.tmp.<pid>` files, use only the
existing Lean 4.35.0 installation, and write outputs only beneath one unique
`/dev/shm` root capped at 2 GiB. No Lake/default build, persistent cache,
flattening, retry, source edit, toolchain/dependency change or extra environment.
Execution requires a fresh independent review of exact hashes and runner.
Report complete theorem types and transitive axiom lists for every executed
root. Stop at the first module error, timeout, memory guard or cleanup failure.

## Resource, review and integration boundary

Read-only Rust and Lean map assignments are bounded to 900 seconds each. The
Lean runner plan and Rust conclusions receive fresh independent source-grounded
review before any code change or Lean invocation. Primary owns exact leases,
admission, execution, outcome records, explicit staging, commit and push. No
Cargo invocation is included. Keep all gates open unless the exact evidence
closes them; module compilation alone does not close original admission,
effect hygiene, source/native correspondence, A/B, soundness or production.

STOP on a missing import/source identity, a test path requiring an invented
solver premise, an accessor that cannot establish the requested join, a
review rejection, resource/cleanup failure, or any need to read an unknown
lease. Preserve unrelated dirty and quarantined paths.

## R156 lane receipts and disposition

- Rust readback audit completed read-only. `candidate_operation` retains the
  exact `SourceOperationDeclaration`, owner and operation occurrence in
  `ViewOrigin::Operation`, and `CandidateSourceCall` exposes native invocation
  and application `Term`s for each exact Apply. `CandidateGraphFreshUse`
  exposes its occurrence and effect rows; `CandidateGraphRow` exposes only
  identity/kind, with no link to the native `Term`. The graph has no
  source-operation origin to final consumer join. Thus the existing public
  observations cannot establish the requested whole chain. The current
  `source_provider_observation` is module-callee-specific, while
  `answer = first id 1` consumes the function through the outer Apply and the
  operation-originated effect is inside the inner `first` function. Do not
  relabel it as `Contribution` or infer consumption from export reachability.
- Lean map completed read-only: the exact imported DAG contains 27 modules
  and 61 authored theorem roots across R104, R105, R112, R114 and
  `OriginalEffectHygiene`. R104's prior flattened syntax result does not
  validate R105's module scope; R105/R112/R114 remain unchecked, and the
  previous R106 module-faithful run stopped at the transient `.olean.tmp.7`
  output allowlist. No Lean invocation is admitted by that consumed review.
  The first source-side admission gap is deriving the normalized App payload
  from an authenticated original App derivation while preserving its chosen
  descriptor/interface, both source operands, all Local premises,
  descriptor formation, both finite Checking judgments and optional
  singleton-formal origin. Lambda admission also needs its shared anchor,
  body derivation, complete body consumer and computation Checking premises.
  Effect hygiene additionally needs concrete original `Kernel.atom` laws for
  receipt, capture, body, shallow residual, latent, rigid operation and raw
  continuation, tied to current authority/incidence.
- Both read-only workers have stopped. R156 is complete as an audit only;
  no code, compilation, tests or theorem closure resulted. The next Rust step
  requires a fresh independent review and exact lease for a minimal readback
  relation joining the captured operation-origin effect to the native Apply
  invocation/application Terms and then to the actual consumer. The next
  Lean step requires a fresh independent review of the module-faithful runner
  before any invocation.
