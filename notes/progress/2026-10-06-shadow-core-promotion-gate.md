# Opt-in HIR shadow artifact promotion gate

Date: 2026-10-06
Status: M2 promotion gate completed; production inference remains authoritative
Authority: user's explicit 2026-10-06 authorization for shadow implementation of settled structure/identity/evidence plumbing
Branch: `research/simple-sub-intrusion`

## Purpose and limit

Promote the two reviewed `cfg(test)` source-structure experiments into one
explicitly opt-in, immutable HIR artifact with a `yu-core::shadow` facade. This
gate is limited to preserving already parsed source, source occurrence
identity, lexical binder/use identity where the existing narrow application
builder succeeds, ordinary Apply structure, raw annotation owner paths, and
honest pending semantic obligations. It adds no Function typing, role choice,
`beta`/`Slots(beta)`, typed path, owner/receiver, `nu,K,D`, `Q`, membership,
solver, scheme, or production inference behavior.

Production F5 remains the only production inference authority. The feature is
default-off; production entrypoints do not call it. The facade cannot return a
solved or accepted program. No new language or inference rule is selected.

## Ownership and snapshot contract

- **HIR is the sole builder/owner** of the immutable source artifact. It
  consumes a caller-selected `yu_syntax::ParsedFile`, retaining its exact
  source and parse environment, then associates/resolves only the existing
  narrow application subset.
- **Core is a read-only facade** gated by a default-off `shadow` feature. Its
  optional upstream dependencies may expose HIR and syntax artifacts, but may
  not invert the dependency graph. It performs no parsing, identity minting,
  mutation, solving, caching, or publication to production.
- A successful construction publishes one complete immutable artifact. IDs
  are artifact-branded and constructors remain private. A new parse/build makes
  a distinct artifact; no cross-revision identity or correspondence is
  implied. Raw syntax paths identify syntax only.
- Callable role, complete Function membership, call-view realization, and
  annotation-to-typed-port/profile correspondence remain explicit unresolved
  premises. There is no discharge API or success/default fallback.

## Input bound, readers, comparison and cost

The adapter starts from a successfully constructed `ParsedFile`; parser stack
behavior is upstream and is not covered by this artifact API. It then performs
an iterative preflight of the CST and rejects when syntax depth exceeds 128 or
raw CST node/token count exceeds 65,536. These are structural caps on this
optional research API, not a source-language support decision. Since a shallow
CST can contain an
arbitrarily long flat application chain, the adapter must not pass accepted
input through recursive association/lowering or construct a recursively owned
`HirExpr`. Instead, it builds the narrow supported ordinary-application
projection iteratively into an arena indexed by artifact-branded IDs. Dynamic
operator forms and unsupported shapes remain explicit unresolved entries;
they are not guessed or delegated to the recursive production associator.
Retained identity edges are parent/ordinal based; the adapter must not store a
full copied path per node. No cache or retained global view is created. Output
exists only for the explicit caller's artifact lifetime.

Readers are focused shadow tests and explicit experimental consumers compiled
with the feature. The existing compose check remains a structural differential
against the test-only scoped candidate. The raw-source check compares the
artifact projection with its exact retained CST. Neither is old-infer semantic
parity. No executable frozen-legacy/old-infer Apply runner exists in this
workspace. On the common leaf-only supported subset, tests may inspect existing
F5 output, but may not claim equivalence outside actual overlap.

Expected added storage is linear in retained CST elements and supported
expression nodes, bounded by the caps above; IDs store one artifact brand and
ordinal/parent edge. No hot production path is introduced, so this gate spends
zero performance samples. Focused feature-on/off builds, graph validation,
public facade access, identity/atomicity tests, flat-chain stack-safety
coverage, and proof that default production entrypoints remain unchanged form
the verification gate.

## Lifecycle, retirement and rollback

This opt-in facade remains research infrastructure while useful to the active
successor work. Reassess it when an approved source/core artifact contract
supersedes it or the inference cutover gate retires the experimental lane.
Default production reach remains zero throughout this gate. A deletion commit
removes the core feature/dependency and facade, HIR feature/export, adapter
implementation and tests. The two prior test-only structural artifacts are
retained in Git history as rollback/evidence material, not as a second
maintained builder. Rollback of this promotion removes the opt-in
feature/dependency/facade and restores the test-only consumers; it does not
change F5 behavior.

## Stop conditions and review

Stop if the facade needs semantic role resolution, typed incidence, annotation
port/profile selection, solver calls, default production routing, stable IDs
across rebuilds, or grammar/diagnostic changes. Keep those as separate proof
and authority gates. This is M2: independent `compiler_referee` review covers
branding, source ownership, pending obligations and atomic publication;
`regression_auditor` review covers feature isolation, dependency graph and
production default reach. Passing this gate closes only the opt-in structural
artifact promotion.

## Evidence sources

- User direction: 2026-10-06 request permitting settled structure/identity
  plumbing in a shadow lane while prohibiting production cutover before
  soundness, principality and source adequacy.
- Current HIR structural experiments: `yu-hir/src/tests/shadow_source_core.rs`
  and `yu-hir/src/tests/shadow_annotation_positions.rs`.
- Architect recommendation: HIR owns source association and identity; core
  provides a default-off read-only facade; no production consumer.
- Open source/profile obstruction:
  `notes/progress/2026-10-06-annotation-position-profile-certificate-attempt.md`.

## Completion evidence

The immutable artifact and opt-in core facade are implemented on the exact
scope above. Reviewers: `compiler_referee` found no blocking or major issue and
confirmed the iterative arena/premise boundary; `regression_auditor` found no
blocking or major issue and confirmed default feature isolation and no
production routing. Their two minor comments were closed: the differential
description now says parsing is shared but association/projection paths are
distinct, and a UTF-8 comment fixture checks byte-based ranges and exact CST
reconstruction.

Focused verification passed:

- `RUSTC_WRAPPER= cargo test -p yu-hir --features shadow shadow::tests` (9);
- `RUSTC_WRAPPER= cargo test -p yu-hir --features shadow shadow_` (8);
- `RUSTC_WRAPPER= cargo test -p yu-core --features shadow` (2 integration tests);
- `RUSTC_WRAPPER= cargo check -p yu-core` and
  `RUSTC_WRAPPER= cargo check -p yu-core --features shadow`;
- `RUSTC_WRAPPER= cargo xtask check-graph`, `rustfmt --check` on changed Rust
  files, and `git diff --check`.

`RUSTC_WRAPPER= cargo test -p yu-hir` also exposed one separate deterministic
failure in untouched test `tests::research_apply_lowering_preserves_mixed_unary_call_spines`
(`30` valid cases observed, `14` expected); it reproduces in isolation. The
failing assertion and its generator are unchanged in this diff, so its cause
is recorded for a separate audit without changing its expected value. It does
not affect the focused shadow checks above.

The initial 4,000-argument end-to-end fixture overflowed during `parse_file`,
before a `ParsedFile` existed. Parser behavior is outside this artifact's
input contract. The final 4,000-tail fixture constructs a matching synthetic
CST and exercises the shadow preflight, iterative projection, validation, and
flat-arena destruction; a separate 8-argument parsed-source test covers the
public builder. This does not claim that the existing parser accepts arbitrary
flat-chain lengths.

This record closes only opt-in structural artifact promotion. It does not
close any theorem or authorize production inference replacement.

## Current-F5 leaf differential follow-up

The default-off `yu-solver/shadow-f5` feature forwards only to
`yu-hir/shadow`. Its integration checks parse one shared snapshot per source
and compare two common F5 leaves:

- `my f x = x`: binder/use spelling, byte ranges and lexical relation match
  current F5's parameter and `ResolvedExpr::Name`;
- `my f x = 42`: binder and exact integer-literal spelling/range match current
  F5's parameter and `ResolvedExpr::Integer`.

Both cases check that the F5 body occurrence enters collected constraints and
solved provenance. The shadow now retains integer source spelling and range,
without assigning a numeric value, type, or effect. Its separate scoped
research consumer still rejects integer semantics explicitly. Feature-off
discovery runs zero tests; feature-on runs these two cases. Both pass.

This is a source-incidence differential with actual current-F5 execution, not
inferred-type equality: IDs remain artifact-local, and no `SolvedProjection`
is claimed for either body. It covers no Apply, callable role, Function
membership, call-view realization, annotations, soundness, principality, or
old-infer parity. No executable frozen-old-infer runner exists in the current
workspace. `compiler_referee` found no issue in the integer structural/API and
differential delta; the earlier `compiler_referee` and `regression_auditor`
reviews found no issue in the original one-case feature/test artifact.
Verification was:

- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-hir --features shadow shadow -- --test-threads=1`
  (18 unit tests and 1 integration test passed);
- `RUSTC_WRAPPER= cargo test -p yu-solver --features shadow-f5 --test shadow_f5_differential`
  (2 passed);
- `RUSTC_WRAPPER= cargo test -p yu-solver --test shadow_f5_differential`
  (0 feature-off tests);
- `rustfmt --check` on the three changed Rust files and `git diff --check`.

No production inference path changed. This closes only the actual leaf-overlap
comparison seam; ordinary application inference remains absent from F5 and is
still an open successor/source-adequacy gate.
