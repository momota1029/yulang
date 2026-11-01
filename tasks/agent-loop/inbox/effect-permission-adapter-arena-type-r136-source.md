# R136 Rust source candidate: adapter arena argument

Status: `STOPPED_WRITING`; immutable-baseline reconstruction complete. No Rust
source was changed, and no compile, Cargo command, test, Lean command, or checker
was run.

## Frozen target

Baseline: `abbe733b952138b5d576c30936692dd262f3e92f`.

The unique call in `crates/yu-solver/src/candidate_scheme.rs:506` is:

```diff
-    let native = extract_native_lambda_argument_effect_incidence(route, incidence_index, &session.store)?;
+    let native = extract_native_lambda_argument_effect_incidence(route, incidence_index, &session.store.terms)?;
```

The extractor's complete signature at committed `candidate_scheme.rs:451–455`
is:

```rust
fn extract_native_lambda_argument_effect_incidence(
    route: &FreshRoute,
    incidence_index: usize,
    store: &BranchTermArena,
) -> Option<NativeLambdaArgumentEffectIncidence>
```

The body uses `store.term_view(function)` to compare the retained positive
Function's native argument-effect term with the retained route term. The sole
committed definition/call-site search result is that definition and the one
call at line 506; the extractor is not called elsewhere in committed Rust
sources.

`ConstraintStore` at committed `lib.rs:3425–3430` owns `terms: BranchTermArena`.
The field has no explicit visibility modifier and is private to the crate-root
module; `candidate_scheme` is its child module, so this child can access that
field under Rust's descendant privacy rule. `BranchTermArena` is `pub(crate)`
at committed `term.rs:488`. Thus `&session.store.terms` has the extractor's
required `&BranchTermArena` type; the current `&session.store` has type
`&ConstraintStore`.

The candidate module is gated by `#[cfg(feature = "shadow-apply-candidate")]`
at committed `lib.rs:210–211`. The extractor itself has no additional cfg
gate. With the feature disabled, the candidate module and this call are absent;
with it enabled, the field and extractor argument types above apply.

## Exact reconstruction evidence

All source bytes below came from immutable `git show HEAD:<path>` blobs.

| Path | Bytes | SHA-256 |
|---|---:|---|
| `crates/yu-solver/src/candidate_scheme.rs` baseline | 508255 | `9cb8349a6ad43ddde8f54ae04ea464a61781b626b25917e928d45d49de3b2012` |
| `crates/yu-solver/src/candidate_scheme.rs` reconstructed target | 508261 | `e2b6209e3bf486a302e52e5051be60bf7cd8187a7a1e8453087b94f77e06b814` |
| `crates/yu-solver/src/lib.rs` | 1662249 | `429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be` |
| `crates/yu-solver/src/term.rs` | 82419 | `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1` |
| `crates/yu-solver/src/candidate_effect.rs` | 301873 | `102d0c78bb57339ccf110b9da721f005c83ad88d5a32901d6c676b90376ddf01` |
| `crates/yu-solver/src/candidate_receiver.rs` | 296602 | `335f5f2cd4841dd8288306623ee863606e355b9ceda6948ab6877d944bed3165` |

The baseline call argument `&session.store)?` occurs exactly once in the
baseline `candidate_scheme.rs`. Replacing only that byte sequence with
`&session.store.terms)?` yields the stated target size and hash: 6 bytes added,
one source line changed. The four dependency hashes match the frozen R136
contract.

## Meaning and limits

This repairs only the internal argument type at the adapter boundary. It does
not add a permission consumer, alter solver choices or validation, establish
runtime reachability, or prove source/native correspondence or effect
hygiene. The extractor remains an approved interface with no permission
consumer. This static reconstruction is not a compiler result; the R111
compiler/resource gate remains unmet and unspent.

No other path was written. No scratch artifact was created. Requested Luna/high
role metadata and observed model/effort are not exposed to this worker runtime.
