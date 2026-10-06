# Shadow Apply endpoint-address skeleton

Date: 2026-10-06
Status: independently reviewed default-off structural experiment; no blocking or major findings; one Debug-output observation closed by primary
Baseline: `2741d7a245adbfe2648e3749073b64e7321f074c`
Branch: `research/simple-sub-intrusion`
Authority: user's explicit authorization for shadow structure/identity/evidence plumbing with unresolved semantics left pending

## Result

The default-off `yu-core::shadow_derivation::RawStructuralArena` now exposes a
borrowed `PendingApplyEndpointSkeleton` for each retained ordinary `Form::Apply`.
It retains the exact existing Apply `ExprId`, ordered callee and argument
identities, the existing `RawCall`, and eight fixed structural address labels:

```text
callee value/effect
argument value/effect
candidate Function return-effect/result
whole Apply value/effect
```

Each address is the pair of an already HIR-branded Apply identity and a
bookkeeping-position enum. The core does not mint a port identity or create a
second identity domain. A nested Apply's argument labels remain distinct from
the child's whole-Apply labels; repeated calls through one binder remain
occurrence-specific. Lookup is an O(1) checked offset into the retained HIR
arena. It allocates no heap storage.

These are candidate bookkeeping positions only. They assert no typed port,
endpoint equality, Function applicability, path, role, `beta`/`Slots(beta)`,
profile, owner/receiver relation, original `xi`, admission, inference result or
premise discharge. In particular, `OriginalAssocType_X(beta,p0,j_call;s0,c0)`
remains open. The lane has not produced a solved application interface or
successor/current-infer scheme differential.

## Ownership and rejection

HIR remains the source identity owner. The core accessor exists only on an
arena returned by validated `RawStructuralArena::from_artifact`; it checks the
requested expression against the arena's retained HIR skeleton, confirms the
same retained form reference, and returns a view only for `Form::Apply` with
its already validated raw metadata. Foreign-artifact IDs and other expression
forms return `None`. Existing pending rows, direct-Use joins, annotation
incidences, captures and capture-input joins are borrowed unchanged.

The added arena reference to the retained `Skeleton` is excluded from Debug
formatting. This preserves the prior `RawStructuralArena` Debug fields and
avoids formatting the complete source skeleton as a side effect of formatting
the raw view.

## Review and verification

A compiler referee found no semantic/invariant issue in the derived-address,
artifact-validation, lifetime or premise boundaries. A regression auditor
found no production reach or sibling-path regression; the audit covered
ordinary, grouped/computed, annotated, repeated and nested calls, captures,
foreign identities and non-Apply forms. The auditor noted that retaining the
Skeleton reference would expand derived Debug output; the primary closed this
minor finding with a manual formatter that omits that reference.

Checks run after the final code change:

```text
RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-core --features shadow --test shadow_apply_endpoint_skeleton -- --test-threads=1
# 3 passed
RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo check -p yu-core --no-default-features
# passed
rustfmt --edition 2024 --check crates/yu-core/src/shadow_derivation.rs crates/yu-core/tests/shadow_apply_endpoint_skeleton.rs
git diff --check -- crates/yu-core/src/shadow_derivation.rs crates/yu-core/tests/shadow_apply_endpoint_skeleton.rs
# both passed
```

The reviewer assigned no broad check. The workspace suite and benchmark were not
run; zero performance samples were used. The accessor has fixed-size labels and
constant lookup work, with one borrowed Skeleton reference retained per arena.

## Remaining work

The slice gives the experimental call seam inspectable structural addresses,
not a source-formed typed call contract. It does not derive Function role,
source-to-typed path, original slots/profile, contribution typing, independent
admission, event/receipt/receiver semantics, soundness, principality, source
adequacy or production conformance. No production inference route or default
feature changed.
