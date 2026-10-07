# Successor priority attack round 9

Baseline: fetched `origin/research/simple-sub-intrusion` at `f1ec5d0e8ad5fb78806500a7ad55a9c16103bd64`; local HEAD matched and the worktree was clean. The canonical DAG started and ended at 90 nodes / 196 edges: CLOSED 7, CONDITIONAL-CLOSED 20, OPEN-PROOF 43, OPEN-SEMANTIC 19, IMPLEMENTATION-ONLY 1. No semantic status changed.

## O0 last-rule attacks

A constructive source-rule audit compared the exact nested Call with Gen-Call-0, typed-core Lambda/Application, typed-boundary §6, and source-contract introductions. Gen-Call-0 constructs the dependent schema (`U_c`, `beta`, `p0`, and `ElimOrigin`) but its port typing is conditional on a well-formed realization. Typed-core's Lambda rule constructs `Fun(P,Result(I_body))`; it does not form the complete Call signature. Typed-boundary projects ports only after supplied signature ownership and descriptors. No cited rule introduces the original dependent signature position:

```text
e_c : generated dependent Call-demand record at B,X,xi,Delta_c
-------------------------------------------------------------- [not supplied]
call.effect[U_c] : EffPosition_sig,orig(U_c;B,X,xi,Delta_c)
```

This formation case must designate immediate complete invocation including entry and designated consumers, preserve the original scope and whole `xi`, and avoid successful comparison, solved shape or execution. It is separate from `OC-CallEff`, which would type the occurrence against `p0`. A complementary complete-model mutation attack produced no pair of Authority-consistent interpretations with different observations/principal outcomes. It did not establish uniqueness or impossibility. O0 therefore remains open; no user decision is warranted by these attacks.

The exact approved `REC_INIT_SELF` proof is already closed. A production trace found no execution-admission consumer in this workspace: HIR resolves exact `my f = f`, and the inference solver preserves `Never`, but VM/native crates are stubs and no evaluator invokes the existing cold rejection classifier. Enforcing rejection in collection/solve would violate inference preservation. No local production code change can establish execution-boundary conformance until an execution-acceptance owner exists. Keep `REC_INIT_SELF` CLOSED and `HIR_WIRING` IMPLEMENTATION-ONLY; other initializers remain separate.

## Shadow vertical slice

The current generalizer directly selects live-row→Q and live-row→R maps, then boxed draft construction discards those origins. The default-off shadow path now retains only `(binder kind, current binder ordinal, historical live row)` per member. It uses the exact map output, not ordinal or scheme-shape reconstruction. Staging survives normalization/finalization privately and is observable only through a successfully published `SolvedModule`. The borrowed API distinguishes unrequested, unavailable and complete captures (including an empty binder inventory), and shares row identity branding with existing fresh-use capture.

The three-alias fixture now joins each source use's fresh rows back to the exact receiving scheme binders, checks stable identity and separation between alias origins with matching local ordinals, and rejects cross-solve identity reuse. The zero-binder route remains complete-empty; a focused injected second-member finalization failure exposes no partial origins. The independent compiler-referee review passed without findings. It inspected current selection, binder substitution, normalization, publication/failure paths, identity APIs, premise markers, and the three-alias/zero-binder tests. It noted that the integration test does not exercise a nonempty R origin; the R path was traced to the exact selected map and finalizer binder ordering but received no separate nonempty-R fixture.

Producer checks passed:

```text
RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo check -p yu-solver --features shadow-f5
RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo test -p yu-solver --features shadow-f5,shadow-scc-observer --test shadow_receiving_root_scheme_crosswalk -- --test-threads=1
RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo test -p yu-solver --features shadow-f5,shadow-scc-observer --lib shadow_generalization_origins_do_not_publish_partial_finalization -- --test-threads=1
RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo check -p yu-solver
rustfmt --edition 2024 --config skip_children=true crates/yu-solver/src/shadow_f5.rs crates/yu-solver/tests/shadow_receiving_root_scheme_crosswalk.rs
git diff --check -- crates/yu-solver/src/f5c_generalization.rs crates/yu-solver/src/lib.rs crates/yu-solver/src/shadow_f5.rs crates/yu-solver/tests/shadow_receiving_root_scheme_crosswalk.rs
```

The integration target passed 2 tests; the injected-failure target passed 1. No broad suite or performance measurements ran. The implementation remains opt-in under `shadow-f5`; ordinary solver inference and all successor markers are unchanged.

## Next attack

Use the retained exact current-row origin only to test the source-derived incoming-use/generalization bridge. The next proof obligation is the source producer's eligible-owned versus fixed-import partition, complete dependency map, and joint substitution correspondence. Do not equate F5's Q/R layout with successor binders or use visibility/allocator freshness as eligibility. In parallel, retain O0's missing original dependent signature-position constructor as the first CALL_TYPE→ORIGINAL_ASSOC prerequisite; no further rephrasing of the same missing rule is useful absent new source evidence.
