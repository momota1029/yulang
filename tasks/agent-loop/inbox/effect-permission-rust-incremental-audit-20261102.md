# Rust incremental audit — FormalEntry permission binding

Status: read-only source audit plus one independently reviewed, behavior-neutral
ownership-check deletion. No Cargo, Rust build, or test was run.

## Frozen dirty source bytes

The reviewer inspected only these root-owned dirty files:

| File | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/candidate_scheme.rs` | `4494ba879a05f90767779e12c9ca8e1364f2203f2f60eb63239a544c0d0da470` |
| `crates/yu-solver/src/candidate_receiver.rs` | `3ec1a45f5cdcfa5f5f28c2ef433c37d03322150a3155228f898e6fc5b77725cf` |

Independent reviewer: `/root/r103_rust_referee` (`compiler_referee`), read-only;
the final receipt is recorded in this artifact. No quarantined runtime or
untracked paths were inspected.

## Findings

**BLOCK — do not stage the complete diff.** In
`candidate_scheme.rs:505–535`, the adapter now receives a `FreshRoute`, term
store, effect state, formal registrations, and occurrence independently. The
old API received one `InferenceSession` and joined the registration, unique
Lambda recipe, LocalSource Lambda/parameter, raw Function argument row, and
current representative to the captured route. The remaining `definition_use`
and `context_use` comparisons are tautological: the extracted incidence copies
those values from that same route. The clean permission binder checks row and
source labels, but not which session owns them. Two sessions with matching
numeric labels could therefore combine one session's route and another
session's retained permission. No caller for the adapter was found, so this is
an evidence-construction regression, not an observed production inference
failure. Restore the session-owned join or introduce a sealed same-session
projection before using this adapter.

**BLOCK — registration is not a dense permission position.** In
`candidate_receiver.rs:1860–1862`, `self.permissions.get(request.registration)`
replaces the previous lookup by the permission's registration label. The
constructor at `candidate_effect.rs:1991–2050` retains only nonempty concrete
permissions, so registration ordinals and permission-vector positions can
differ. A preceding formal without a retained concrete permission makes this
lookup reject a later valid record. The current private single-Lambda assembly
envelope does not establish a reachable failure inside that restricted case;
general inventory code must keep label-based lookup or prove its singleton
registration invariant.

**Safe reviewed slice.** Delete only the initial three-pointer guard in
`ProviderNativeContextProjection::capture` around the former line 5087. The
same owner pointer is checked immediately afterward; batch and live-state
ownership are supplied by the `OwnedResidualProjection` and
`SourceInternalProjection` constructors. This removes duplicate checks without
weakening the owner join. No other removal in `candidate_receiver.rs` was
approved as a separate slice.

## Independent review receipt

The reviewer confirmed both findings above and the narrow safe slice. It also
confirmed the limited envelope caveat on the sparse-index finding. The review
used the frozen hashes in this note and made no edits, builds, tests, Cargo
calls, staging, or Git mutations.

## Checkpoint boundary

Only the independently reviewed duplicate-guard deletion is eligible for this
checkpoint. The adapter rewrite and all other receiver changes remain unstaged
and unpushed. This audit does not connect Catch consumption or close R116,
R45, R54, or the original `InferenceSoundness` obligation.
