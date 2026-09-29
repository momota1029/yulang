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

## Restricted correspondence result

A conditional path theorem is now recorded in the abstract semantics draft.
It covers a pure acyclic complete root `Arr(x, R)` with one negative occurrence
of `x`, a successful projection query whose sole effective input is one direct
concrete upper atom `U`, eligible one-polarity elimination, and later passes
that leave `U` and `R` unchanged. If the candidate separately stipulates
`{A | A ≤ U}` as the nonempty admissible assignment set with greatest element
`U`, both paths produce the same root denotation, `↑{Arr(U,R)}`.

This statement was reviewed conditionally by a `compiler_referee` and
`spec_auditor`. Their required qualifications are explicit in the draft:
projection must have no weighted, alias, row, recursive, or secondary input;
the variable must meet the actual elimination eligibility checks; later
coalescing, ancestor simplification, and post-loop passes must preserve the
root; and `{A | A ≤ U}` remains an independent denotational premise. The
`expect`/`k` probe is only an observed `U = Int` instance consistent with the
path. This is one restricted correspondence, not Gate C closure or proof of
Oracle equivalence for the source graph family.

## Next action

Extend the correspondence to a graph class where upper constraints interact
with lower obligations, anchors, or shared occurrences, deriving the candidate
admissible assignment set from the selected graph rather than stipulating it.
The general denotation, ordered root simulation, use simulation, and
implementation gates remain open.
