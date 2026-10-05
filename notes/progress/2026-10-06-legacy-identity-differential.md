# Frozen legacy versus current F5 identity shape

Date: 2026-10-06
Status: Implemented and spec-audited, restricted displayed-shape differential
Baseline: `d8e25902a946edfd907f1c385fa2b18b5cf12370`, `research/simple-sub-intrusion`
Source: exact Oracle input `my f x = x\n`
Implementation authority: existing Authoritative F5 identity scheme contract; no production change

## Result

Added the internal `yu-solver` test
`current_f5_versus_frozen_legacy_identity_displayed_shape_differential`.
It uses the exact 11-byte source from the frozen Yulang2 probe (SHA-256
`6fdaa7a0ce83d2309290787aa7de9f1d9080bacf3f33726ac19974fc954a1273`) and pins
the exact CLI output recorded from Oracle source commit
`a58eefc31e22141574b6f20c6a5748151c6d79f1`:

```text
my d0:f: 'a -> 'a = e1:(fn p0:d1:x -> e0:r0:x->d1:x)
```

The test strictly recognizes only a single displayed variable arrow with the
same variable on both sides. Unsupported constructors, additional arrows,
effects, quantifiers, changed endpoint relation, malformed prefix and extra
lines fail normalization. Current F5 runs the same exact bytes through parse,
HIR, constraint collection and solving, then resolves the binding through its
own definition-root map. It requires one `Q`, no `R`, a positive Function,
empty negative argument effect, bottom positive result effect, and one shared
quantified endpoint. Both sides normalize to the single `DiagonalIdentity`
shape.

This establishes only the correspondence between the old printer's restricted
arrow/variable display and the current F5 closed-scheme shape for this input.
It does not equate the full old constrained scheme with the current scheme,
interpret every legacy effect/row, compare against the successor shadow,
establish denotational equivalence, or close soundness, principality, Apply, or
call-view gates. Current successor-shadow output still has no solved scheme.

## Authority, review and checks

The displayed identity scheme agrees with the existing Authoritative F5
identity contract in §§1,6,23: `Q=[q0]`, `R=[]`, and a Pure Function whose
negative argument and positive result share `q0`. The pre-write
`spec_auditor` approved this narrow comparison with the explicit limitations
above. A post-write `spec_auditor` review found no blocking, major, or minor
issue in the expected legacy fixture, strict normalization, root-specific
current extraction, required structural assertions, or claim boundary.
No existing expected value or test name was changed.

Checks:

```text
RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-solver legacy_identity_differential -- --test-threads=1
rustfmt --edition 2024 --check crates/yu-solver/src/tests/legacy_identity_differential.rs
git diff --check -- crates/yu-solver/src/lib.rs crates/yu-solver/src/tests/legacy_identity_differential.rs
```

The focused command passed both the comparison and strict-normalizer tests;
442 unrelated unit tests were filtered and no integration cases were selected.
One rustfmt check on the large `lib.rs` owner reported pre-existing formatting
drift outside the one-line module registration; no formatter wrote files and
no unrelated formatting was applied. The new test file passes its own rustfmt
check. No broad suite or performance experiment ran.

## Next differential boundary

Identity is now a tested old/current overlap. Compose and captured-step have
recorded old-side baselines, but current production HIR rejects their ordinary
application or nested block before solver collection. The shadow retains syntax
and occurrence identities but does not solve a scheme. Extending this test to
those cases therefore requires successor inference work; this test provides
no permission to infer or fill in the missing call-view semantics.
