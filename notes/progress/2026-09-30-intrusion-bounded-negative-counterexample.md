# Intrusion bounded-negative erasure counterexample

Date: 2026-09-30
Branch: `research/simple-sub-intrusion`
Classification: conditional denotational counterexample; no Yulang semantics selected

## Claim

Under a subtype preorder with `Top ≰ Int` and Function subtyping

```text
Arr(A, R) ≤ Arr(A', R') iff A' ≤ A and R ≤ R'
```

a negative-only local argument `x` constrained by `x ≤ Int` cannot in general
be replaced by `Top` while preserving the candidate principal relation. The
constrained relation is `↑{Arr(A,R) | A≤Int}`. `Arr(Top,R)` belongs to
`↑{Arr(Top,R)}` by reflexivity. It cannot belong to the constrained relation:
membership would require some `A≤Int` with `Arr(A,R)≤Arr(Top,R)`, hence
`Top≤A≤Int`, contradicting `Top ≰ Int`.

This counterexample shows that the unconstrained negative-argument lemma cannot
be generalized by polarity alone. It is not an Oracle observation and does not
establish that the Oracle accepts or emits this exact selected graph.

## Frozen Oracle characterization

A temporary Rust source-path test against frozen Oracle `a58eefc3` used:

```text
my expect(x: int): int = 1
pub k x = expect x
```

The lowering completed without diagnostics. In `k`'s first compact view, the
Function argument includes `Int` and `TypeVar(16)`; that variable has an upper
bound record. At the saved `GeneralizedCompactRoot`, the argument contains
`Int` and no variable, and the public scheme is `int -> int`. This is
consistent with the frozen Oracle compactor expanding negative variables
through upper bounds before one-polarity elimination, but this source graph is
not proven identical to the abstract counterexample above.

Probe command:

```text
cargo test -p infer scratch_oracle_saved_bounded_negative_projection -- --nocapture
```

One focused test passed, including an assertion that lowering produced no
diagnostics. Its temporary instrumentation and test lived only in
`/tmp/yulang-intrusion-bounded-arg-probe` and were removed after capture. The
frozen Oracle worktree was not modified. The proof must still compare the
candidate's selected-obligation relation with this ordered Oracle projection;
deleting a bounded variable directly is not a valid shortcut.

Independent `compiler_referee` review verified the counterexample under the
stated preorder and Function rule. Independent `spec_auditor` review confirmed
that its scope is conditional and it makes no Oracle-semantic decision. Neither
review establishes the source graph or the general root-projection theorem.

## Next action

Use the exact saved-root observation to prove or refute the bounded-variable
projection rule for a clearly stated graph class. The general denotation,
ordered root simulation, use simulation, and implementation gates remain open.
