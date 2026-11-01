# R159 Rust App owner trace

Disposition: **NO_SAFE_CODE_SLICE** for constructing the original App
descriptor/profile formation and independent logical admission law. This is
a bounded source-owner trace; it is not a compiler execution result or a
whole-source absence claim.

## Exact Rust owner chain

| Owner | Locator | Evidence and limit |
|---|---|---|
| Ordinary source preflight | `crates/yu-hir/src/module.rs:2871`, `lower_ordinary_admission` | Associates CST provenance and accepts a bounded source grammar. This is structural admission. |
| Ordinary Apply constructor | `crates/yu-hir/src/module.rs:2977`, `finalize_ordinary_admissions`; Apply case `:3049`, constructor `:3076` | Retains exact occurrence, callee and argument children, source form, range and descendant diagnostics. |
| Source carrier | `crates/yu-hir/src/module/local_source.rs:1025`, `form_ordinary_with_root_parameters`; Apply constructors `:1632–1710` and `:1881–2026` | Retains exact operand indexes and source form; an empty call tail supplies a Unit argument. It supplies syntax identity, not typing. |
| Candidate planner | `crates/yu-solver/src/candidate_source.rs:1043`, `ConstraintBatch::emit_candidate_source`; Apply case `:1808` | At `:1869` retains `CandidateRelation::Apply` from the actual operand positions; at `:1911–1922` ties `ApplySourceInput` to its recipe and slot-0 checking occurrence/cause. These IDs are provenance, not finite source Checking judgments. |
| Native consumer | `crates/yu-solver/src/shadow_apply.rs:4159`, `InferenceSession::admit_candidate_fact` | At `:4163–4185` checks source-input, recipe and operand identity. At `:4302–4378` constructs the negative Function demand, invocation row and `NativeInterface`; at `:4389` admits value provenance and at `:4424–4441` adds evaluation/invocation effects. |
| Source-call observer | `crates/yu-solver/src/candidate_call.rs:485`, `observe_inner` | Authenticates exact source operands, occurrence/cause, HIR ownership/scopes, native Function fields and port polarities; `:580–672` authenticates the conditional formal route. This remains candidate structural evidence. |
| Candidate entrypoint | `crates/yu-solver/src/shadow_apply.rs:2236`, `source_call` | Selects the owner HIR and delegates to the source-call observer. |
| Effect join observer | `crates/yu-solver/src/shadow_apply.rs:2089`, `source_operation_apply_effect_joins` | Joins an operation occurrence and FreshUse route to a captured direct Effect bound, exact `BoundKey`, copied operation identity and outer Apply rows. This is structural observation. |

The missing-input interface is explicit in `candidate_call.rs:252`
(`OriginalGenCall0Input`) and `:397` (`PendingCallConstruction`): the original
whole interface, checking exposure, Gen-Call-0, argument carrier and dispatch
suppliers remain outstanding. `CandidateSourceCall::unresolved` at `:391`
preserves the source typing/admission obligations.

## First missing owner law

The first missing owner is original source/Checking semantics intake, before
the native planner and consumer:

> For the same original App binder and exact operands, construct lawful
> descriptor/profile formation and independent logical admission from the
> actual Local premises and both finite Checking judgments, preserving the
> selected interfaces, occurrence, payload/extension and conditional
> singleton-formal origin.

Neither `ApplySourceInput` nor `NativeInterface` construction supplies those
judgments or that law. Native Function shape, provenance IDs and effect-row
joins cannot discharge it. Extending a structural observer would not prove
this implication, so no production or proof-dependent App edit is justified
by the inspected Rust owners.

## Inspection boundary

Read-only inspection covered the owners listed above and the clean structural
owners `crates/yu-core/src/shadow_call_formation.rs` and
`crates/yu-core/src/shadow_derivation.rs`. The latter retain pending call
bookkeeping and explicitly leave typing, endpoint and admission premises
unresolved. No source was changed. `candidate_scheme.rs`,
`candidate_receiver.rs`, `tools/inference-playground/src/runtime/**`,
untracked quarantined artifacts, Cargo, tests, builds, and Lean were not read
or invoked. The actual FreshUse-map construction is outside this bounded map.

Next owner: derive the original source/Checking law first, then connect its
outputs to these retained Rust identities. Rust App admission, source/native
closure and whole-program soundness remain OPEN.

## Frozen inputs

| Path | SHA-256 |
|---|---|
| `crates/yu-hir/src/module.rs` | `6bf92c93fa37f425a7380248c12c50c0d04ea6eb282e76edb6df54e628260646` |
| `crates/yu-hir/src/module/local_source.rs` | `7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1` |
| `crates/yu-solver/src/candidate_source.rs` | `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49` |
| `crates/yu-solver/src/candidate_call.rs` | `fdc39e01fa3665b4dc14e167973de63b275eb0280b831e340b6cdcee5ed0fc3f` |
| `crates/yu-solver/src/shadow_apply.rs` | `99d67895c250e5d79fb774728867fe2fc88c4dc22df9bfc38ac9fd1aeb0908e5` |
| `crates/yu-core/src/shadow_call_formation.rs` | `394c763e5b4e2de6ae692ffacf22c07db8958f00129a47f1332f238c9a8eb5eb` |
| `crates/yu-core/src/shadow_derivation.rs` | `714fa4f53ee14f7a4d4e1d38ff0820157838de9c4b70a266bee1998eb2851dc2` |
