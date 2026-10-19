# Sprint R117 — catch payload projection and warning ownership

Status: CANDIDATE pending rev2 pre-spec review and Luna's exact lease grant.
Branch: `research/simple-sub-intrusion`; baseline: R116 reviewed CLI pass,
warning-owner audit complete, integration pending.
Contract revision: 2. Rev1 is preserved byte-for-byte at
`tasks/agent-loop/sprints/effect-static-runtime-projection-warning-audit-20261019-r117.md`.
Rev2 resolves the proof/runtime file overlap, verification timeout accounting,
and residual warning count raised in the rev1 audit.

## Original outcome and success evidence

Parent goal remains broad, proof-backed inference/evaluator progress: rotate
bounded work across all six effect-hygiene fronts, advance method/role proofs,
and make ordinary/effectful surface execution usable early. This sprint advances
one effect front and one bounded integration-cleanup outcome. It does not spend
another sprint on effect storage/fiber analysis or duplicate-handler priority.

Proof front: static-to-runtime projection for the exact R116 effectful source.
Trace its original operation-arm payload binder from LocalSource construction,
through candidate endpoint/name resolution, into runtime arm binding and body
lookup. Success is a conditional source-corresponding bridge that establishes
whether all stages use the same authentic binder and lexical environment, plus
the exact remaining premise if one edge is missing. Reuse R116's reviewed public
CLI observation; do not rerun it or infer general permission equivalence.

Exact source, no final LF, SHA-256
`f3b8173cc77bc99e0d50b0d3dac60de7702eaae2d8874fd875d5ade97a76a059`:

```yu
act io:
    our tick: int -> int
    our other: int -> int
my main = catch io::tick 7 { io::tick(p), _ -> p }
```

The static/runtime falsifier is a changed binder ID, a reconstructed
name-based association, a body lookup outside the originating catch environment,
or a consumer that selects a different arm/binder. Keep all six original effect
parents OPEN, along with R100-P2 and the original evaluator/Simple-sub A/B claims.

Implementation outcome: audit the exact 17 warnings from the R116 authorized
Cargo run and make only the five owner-local changes independently identified
as behavior-preserving: remove unused `replace_admission_root`; gate the
test-observation locals `requested`, `graph_row`, and `completion` consistently
with their `cfg(test)` consumers; gate test-only `freshen_candidate_graph` with
`cfg(test)`; remove redundant stored `OperationV1Plan.callback_apply` while
keeping its required local and `plan.link.callback_apply`. Exact compiler
owners are HIR `module.rs`, solver `candidate_scheme.rs` / `candidate_context.rs`,
and playground `runtime/program.rs`.

Preserve intentional method/role association provenance, all operation/license/
handler evidence fields, and the solver's retained endpoint evidence. Do not add
warning suppressions. Record the remaining 11 intentional warning instances in
`tasks/current.md` by exact owner. Do not require a warning-free build.

## Authority and immutable inputs

No language semantic change, expected-output change, diagnostic change, or
production behavior change is authorized. Effect authority remains bounded by
the approved charter and R116's exact effectful fixture; this is an identity and
consumer correspondence proof, not a new handler-selection/permission rule.

Reuse R116 contract rev3 SHA-256
`0b9653736e84baa63a04a74bbc0b23742c17941be38b4cceede4cb91d0393ea5`, its
effectful fixture, and CLI result (2 passed, exact `7\n`, empty stderr).
Reuse R116 effect authority/evidence: primitive visibility theory
`7b27f8cf1d8024e249cc7d8a433c77438e3f59e5543cfc46a96a1af278eb3f56`; primitive
handler report `8d97124d8aafb618f116745754aecd123ac6f3d69f922b788f8d233a9c8f3ef6`.
R116 warning-owner audit is a frozen read-only receipt in this conversation;
its classification is copied above. The five safe cleanup candidates have no
semantic authority burden beyond their source-local configuration/def-use
evidence.

Exact proof pins:

```text
crates/yu-hir/src/module/local_source.rs 3014628f861840ca8e716b3baf8e6a3c9dd736b1bad318b32e7a7b195ddf8786
crates/yu-hir/src/shadow.rs 9f7a80055076a01cbd99a3eb9c5bc8c3f0db512f2e84032a53af0eacdad2375b
crates/yu-hir/src/source_identity.rs 7f0ba057a28ec8c42d2b08bcbe698ee9b422819bfde8ea43ce184457ea586bb3
crates/yu-solver/src/candidate_source.rs 66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c
crates/yu-solver/src/candidate_effect.rs 6112343b4014c67dcb7d814a46412b3af3e1d12183924e891df4817a59f58da0
tools/inference-playground/src/runtime/program.rs 7bc27580711d3ef09044e324541904ef3388aca8e3b4f3a72437b1e04dc0210a
tools/inference-playground/src/runtime/machine.rs fa8dab7f7146f528ad354f336cdfe6e41a728505f9c3dd80c6df64e843dc5b46
tools/inference-playground/tests/cli_approved_surface.rs 43fc3670b80e931a0865f3790a9a39b5755e09a6c591e89b2cbf9b18213ba43a
```

Exact implementation pins:

```text
crates/yu-hir/src/module.rs c40ebde1755d300c83aafba0a81a85d19ed5200dfc2163ab72c8a3bb08baf29a
crates/yu-solver/src/candidate_scheme.rs d4ff8a9e98eb667a5eb85aff9c0feec1f0227e86257bb56892493ac1d04a9278
crates/yu-solver/src/candidate_context.rs 42f89dcf5fa6d7095db1e220c89308a2a35f4e74b05c3e8821d4fb2e3e32b0ca
tools/inference-playground/src/runtime/program.rs 7bc27580711d3ef09044e324541904ef3388aca8e3b4f3a72437b1e04dc0210a
```

`runtime/program.rs` is a proof input and is not an implementation-lane write
lease. Luna's removal of the redundant stored `callback_apply` is sequenced only
after the proof writer freezes and stops; the proof review will compare its
claim with the unchanged pinned bytes and the narrowly reviewed cleanup diff.

Warning inventory: HIR unused `AssociationProvenance::{Token,Synthetic}`
payload fields; `replace_admission_root`; `AssociatedFieldTailSource` and its
three accessors; `AssociatedRoleImplSource` and its two accessors;
`ShadowArtifact::with_associated_method_role_sources`; `walk_associated_pairs`.
Solver unused locals `requested`, `graph_row`, `completion`; test helper
`freshen_candidate_graph`; retained fields in `LicensedOperationFieldV1`,
`CallbackFieldRealizationV1`, and `FieldBoundV1`. Playground stored
`OperationV1Plan.callback_apply`. The audit classifies the helper/local/test
wrapper and redundant stored field as safe local cleanup; provenance and effect
evidence as intentional scaffolding/evidence that must remain.

## Two continuing lanes

Proof — Sol/high constructive bridge on the exact fixture and pins above.
Inspect LocalSource binder construction and lexical scope, candidate catch
endpoint registration/name resolution, runtime instruction preservation and
Catch binder environment installation/lookup. Compare IDs/owners at every join.
Apply the bounded result to the static-to-runtime parent and state what remains
open. No CLI/build/test/probe work.

Implementation — Luna/high source-local cleanup on the three pinned files only:
Make the five changes listed above, preserve behavior and test observations,
write the frozen diff/handoff, and stop. No tests, builds, CLI, formatters,
probes, warning suppression, or extra paths. If an edit needs a wider owner or
semantic decision, stop that edit and identify the exact boundary.

Fresh independent reviews: compiler/source review of binder correspondence and
of every cleanup diff; spec/authority review of the proof boundary; regression
review of test-only observation preservation and unchanged public behavior.
Authors do not review their own outputs. CLEAN cannot promote the result to a
general effect theorem or production approval.

## Exact leases and resources

Proof writes only:
`notes/theory/2026-10-19-r117-catch-payload-projection.md` and
`tasks/agent-loop/inbox/20261019-r117-proof.md`.

Implementation writes only `crates/yu-hir/src/module.rs`,
`crates/yu-solver/src/candidate_scheme.rs`,
`crates/yu-solver/src/candidate_context.rs`, and
`tasks/agent-loop/inbox/20261019-r117-warning-audit.md`. Luna alone writes this
contract, `tasks/agent-loop/current.json`, `tasks/current.md`, closeout, and
`tools/inference-playground/src/runtime/program.rs` after proof writer STOP.
Everything else is read-only. No scratch paths, descendants, or overlapping
writers.

Aggregate cap: 1,620 active seconds: proof 480; implementation 300; fresh
reviews 300; verification 240; Luna inventory/closeout 300. Astra 0. Two
producers may work concurrently; reviews begin only after writers stop. Existing
three UNKNOWN reservations remain charged; no lease or capacity is reclaimed.
No more than one heavy Cargo process; verification owned only by Luna after
frozen output and CLEAN reviews. Exact commands, one attempt each:

```sh
timeout 120s sh -c 'CARGO_BUILD_JOBS=2 cargo check -p yu-hir -p yu-solver -p yu-playground'
timeout 120s sh -c 'CARGO_BUILD_JOBS=2 cargo test -p yu-hir -p yu-solver -p yu-playground --lib'
```

The shared verification wall budget is 240 seconds, with each command capped at
120 seconds and run sequentially. If command one consumes the full shared
budget, command two is NOT_RUN; no overrun or retry. If a command fails or
times out, preserve the result; do not repair expectations or retry. Tests/
builds remain forbidden until the reviewed source diff freezes.

## Frozen handoff, integration, and stop boundary

Each handoff records exact hashes, original parent application, premises,
constructors-to-consumers, falsifiers, checks omitted, spent budget and stopped
writers. The proof is applied immediately to the six-front rotation without
closing any parent. The implementation's remaining intentional warnings are
recorded under their owning modules in `tasks/current.md`.

R116 CLI success is reused only as a finite surface observation. R100-P2,
R113/R114 boundaries, all six effect fronts, and original evaluator/Simple-sub
A/B obligations remain OPEN. No semantic adoption, general permission
equivalence, production cutover, commit, or push follows automatically. Luna
integrates only after clean fresh reviews, exact verification, warning-owner
notes, and full outbound range inspection.

Next dispatcher trigger: sprint closeout, projection counterexample/missing
owner that changes the proof path, cleanup authority expansion, or integration
seam. Following R117, continue the six-front rotation from a ready effect front
not already monopolizing the queue; keep method/role and surface-execution
progress in the active goal.
