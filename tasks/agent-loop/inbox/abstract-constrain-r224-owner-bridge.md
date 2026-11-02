# R224 Rust-owner bridge investigation

Sprint: R224; contract revision 1, SHA-256
`5c1a2f68200e5d291096ff3634f1fe337dec71ecde2a101eacbfdf0911a1543a`.
Assignment: `/root/r224_owner_bridge`; handoff revision 1.
Baseline: `7a4e25417a2794d3d19e9cb128060ad240d2b255` (`yulang3`).
Method: bounded source/abstract-operation comparison; no execution or theorem
construction. Outcome: **source-native-evidence, partial correspondence;
NO_SAFE_CODE_SLICE**. Independent review: pending, not self-certified.

## Original obligation and authority

The parents remain `InferenceSoundness`, `SourceScopedCoverage`,
`PrincipalCoverage`, and `InferenceTermination` at
`notes/theory/lean/YulangClosure/Contracts.lean:128–154`. No original parent
closes: roots/packages remain **0/4 and 0/5**.

The local target is the source correspondence needed to apply R224's proposed
successful-constraining lemma: consistent input bounds, a successful cache-aware
run, consistent output bounds, and the negative-to-positive coalesced inequality.
The reference is the pinned paper §3.2.2 (cache before case analysis; insertion
before opposite-bound propagation), Fig. 9, and §5.3.1 Lemma 2 (including temporary
inconsistency of cached variables). No interpretation of the selected language
meaning is changed. Top-level inference principles §§1–3 and §1.1 govern ordinary
extrusion and value-occurrence-qualified intrusion; §§4–5 govern abnormal safety.
The leaf has no authority to implement or to discharge the full Call/effect gate.

## Pinned direct inputs

All hashes are SHA-256. Both Rust inputs and the additional scoped-publication
input also matched their Git blobs at the baseline. Rechecked immediately before
the sole artifact write; HEAD still equalled the baseline.

| Input | Hash |
| --- | --- |
| `crates/yu-solver/src/candidate_scheme.rs` | `6072c73bc1a1629f025dcaf61fcbed98c738d93f8993bd81182a391d1ad4d89e` |
| `crates/yu-solver/src/candidate_receiver.rs` | `5ca308e7b890e57a8458a151554ece55585d762565204d39c520c4b534e44ade` |
| `/home/momota1029/rust/simple-sub-reference-paper.pdf` | `5ab2bd4122caee17c20134e4cbe8dc8a4848c142de1e576b5fd178aed8787698` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| `notes/theory/lean/YulangClosure/SimpleSubConstraintSyntax.lean` | `a9ec574d31223e0484fd827838b45cd019fc858eece9f326c95ebc2e1e77a1f6` |
| `notes/theory/lean/YulangClosure/SimpleSubConstraintSoundness.lean` | `33709d3978e8071708c10bba23d85b1b025c11dfd988220501acb7c6e3220293` |
| `notes/theory/lean/YulangClosure/AbstractSimpleSubCore.lean` | `023635d283f9a00e906ec965a6eaa5595eab21f2b93f353a1d5ea0ede0bffb6c` |
| `notes/theory/lean/YulangClosure/SimpleSubLatticeCertificates.lean` | `55533eee35ed7058abd125ac0e01d8f29b8c0534800018d254c1bd9f9c0bb79b` |
| `notes/theory/lean/YulangClosure/SimpleSubScopedPublication.lean` | `d64e9bffca5d513985237a9ff78dcf3d9e43baae1594edbc93dff4b5410d428f` |

No proof-lane draft was read or used as an authority.

## Concrete correspondence and derivation

These are equations of the inspected Rust constructors under the hypotheses
below, not a whole-run simulation or a new proved Lean theorem.

1. **Function shape.** Suppose `Capture::expand_node` succeeds on an actual
   Function endpoint and each `intern_shape`/`term_endpoint` call succeeds.
   At `candidate_scheme.rs:2226`, both TermView Function constructors extract
   `[argument, argument_effect, result_effect, result]`. The kind array is
   `[Value, Effect, Effect, Value]`; the polarity array is
   `[opposite, opposite, p, p]`. At `:4765`, reconstruction uses those exact four
   child indices and invokes the same-polarity Function constructor with
   `[a, ae, re, r]`. Thus the constructor wiring agrees with
   `extrudeTerm`'s two contravariant and two covariant ports and with
   `SimpleSubConstraintSoundness.Step.function`'s four comparisons. This is a
   structural correspondence; the actual structural solver comparison rule is
   not implemented by these capture/reconstruction lines.

2. **Stored-bound orientation.** Let `b` be a captured bound successfully
   processed by `Capture::bound` (`:2351`) and
   `begin_candidate_fresh_bound` (`:4947`). Write its decoded positive/negative
   endpoints as `L` and `U`. Both functions select
   `(owner,item) = (U,L)` for Positive and `(L,U)` for Negative. In
   `ScopedPublication.Bound.clause` (`SimpleSubScopedPublication.lean:66`),
   Positive denotes `body <: owner`, and Negative denotes `owner <: body`.
   Substitution gives `L <: U` in both cases. Reconstruction selects Value or
   Effect endpoints by the bound's `ComponentKind`, so this derivation includes
   both kinds. Relation/evidence identity is retained separately; this equation
   alone does not prove physical admission, cache handling, or propagation.

3. **One use map and current representative.** For a successful
   `prepare_candidate_fresh_use` (`:4529`), every captured graph row is resolved
   through `intrusion.rep`. If `canonical_rows` already contains that resolved
   source, its first image is reused. Otherwise a fresh row of the same kind is
   allocated exactly when `row.local && level > graph.boundary &&
   !metadata.non_generic`; the source is reused otherwise. The image is inserted
   into that invocation's map and appended to its `rows`. Every reconstructed
   Row node subsequently reads that shared `rows` entry (`:4761`). The capture
   guard setting `row.local` is itself `level > boundary && !non_generic`
   (`:1988`); `expand_row` stops at nonlocal owners (`:2400`). This establishes
   the local map/guard wiring, conditional on successful helper calls. It does
   not establish global allocator freshness, cross-use disjointness, full
   captured dependency closure, or preservation through future intrusion.

## Exact missing owner equations

**Scheme owner: admission and cache boundary.**
`freshen_candidate_graph_core` (`:4508`) restores every captured bound through
`begin_candidate_fresh_bound` and `candidate_drive_bound_restoration`.
The incremental Local route (`:5430`) similarly stores an outstanding
restoration ID, advances `next_bound` only when restoration completes, and admits
the root link after all captured bounds. The owner calls therefore retain the
transport inputs and a completion boundary. They do not supply the cache-state
equation of the R224 algorithm. `Capture::bound`'s `bound_keys` prevents duplicate
captured graph entries; it is not the paper's recursive comparison cache.

The first needed source equation is a simulation for the actual delegated
admission/restoration operation, with a separately defined decoder `D`:

```text
nativeBoundRestoration(s, encoded L, encoded U) = success s'
  implies ConstrainRun(D s, L, U, D s')
```

`D` must project both lower/upper bounds, representatives, active comparison
cache, and outstanding work. The proof must identify which native event inserts
the cache entry, which inserts the bound, and which drains every required
opposite-bound comparison, with cache-sensitive consistency premises from the
R224 theorem. The existing partial `CoreState.insertPendingUpper`
(`AbstractSimpleSubCore.lean:174`) inserts before replay for a same-level
variable-upper case, but has no comparison-cache field, no full lower/structural
step relation, and no general extrusion transition. Its queue record cannot
certify the delegated Rust run. The body of the delegated admission operation is
outside this leaf's two-owner read lease and was not inspected. This is an exact
remaining source obligation, not a claim that native cache behavior is wrong.

For publication/use, the existing core explicitly records a further missing
equation at `AbstractSimpleSubCore.lean:429`:

```text
resolveOriginalUse (performUse state publication use) use template
  = actualFreshRowAllocatedForThatUse state publication use template
```

The local map evidence above identifies concrete data for that future bridge;
it does not construct the missing abstract `performUse` transition or discharge
its both-bound-sides and subsequent-equality preservation premises.

**Receiver owner: residual filtering precedes native constrain.**
`execute_receiving_assembly` (`candidate_receiver.rs:5542`) deliberately defers
the unique catch fact at `edge_scrutinee`, local slot 51. It routes the unique
original module use and executes the other actions, then traverses actual
lower bounds to collect terminals. It rejects a row with neither lower evidence
nor bottom evidence, an unresolved Support tail, and an empty terminal result.
Its comment explicitly says this assembly inventory is not an SCC and does not
populate intrusion `active_roots/uses`. It cannot certify the general
occurrence-qualified intrusion operation.

`complete_residual_plan` (`:3595`) classifies each collected terminal. Suppress
requires matching operation identity, a closed provider view, an authenticated
provider entry certificate, the exact catch fact, and matching endpoint.
`publish_authenticated_residual` (`:3182`) calls
`constrain_live_effect(endpoint, pending.upper, fact.id, fact.cause)` only for
Forward decisions. Suppress decisions perform no such call. This is actual
owner-local evidence that an unfiltered catch clause is not simply passed to
the constraining theorem as one unchanged native demand.

The first needed receiver equation, before applying any cache theorem, is:

```text
decodeSourceCatch(fact, authenticated receiving context)
  = approvedResidualObligation(terminals, exact suppression evidence, upper)
```

It must derive the source obligation represented by the retained/forwarded
terminals and explain each suppressed terminal under the approved handler
meaning. Its conclusion must not be assumed from `ReceivingResidualOutcome`.
For a Forward terminal, a second bridge is the same successful-native-constrain
simulation above, specialized to Effect. The observation helpers
`capture_native_publication_call` (`:3478`) and
`capture_native_whole_publication` (`:3251`) provide source-drain cuts, exact
physical-slot checks, and before/after prefix coverage when they return Some.
Observation failure can clear the observations while native publication still
succeeds (`:3203–3247`). These optional certificates therefore cannot be treated
as a universal successful-run premise. A certificate's existence also does not
prove its source interpretation or the semantic consistency of the whole store.

## Coverage, independence and limits

The method compares actual constructor expressions in the two pinned Rust
owners to the pinned abstract definitions and the paper, rather than running a
checker that postulates the missing transitions. It is independent of the
R224 proof producer's implementation, but shares the sprint's paper and selected
Yulang semantics; it is not independent review. The inspected method bodies and
their exact locators delimit the evidence. No claim is made from exhaustive
inspection of all source paths or from unrelated cfg(test) assertions.

No executable experiment, seed/range search, mutation, build, test, cache,
scratch output, or Git mutation was performed. Commands were bounded
`cat`/`sed`/`rg` source reads, `pdftotext -layout ... -` piped to a bounded
text search, `sha256sum`, read-only `git rev-parse`/`git show`, and the sole
artifact patch. Hash results matched the contract; baseline Git hashes matched
both inspected Rust owners and scoped publication. Several broad initial
captures were truncated; conclusions use the subsequent narrow method reads,
not omitted output. CPU time and peak RSS were not instrumented; wall time was
not measured. There were no heavyweight processes or compiler invocations.
The assigned ceiling was 1,200 seconds; no additional resource budget is claimed.

Omitted: actual solver admission/cache bodies, extrusion allocator and recursive
bound-copy implementation, value-SCC qualification and equality propagation,
complete source catch/Call semantics, failure/retry soundness, all publication
paths, source-to-CST closure, Lean/kernel verification, and runtime coverage.
No counterexample to the approved algorithm or impossibility result is asserted.
No safe production implementation follows from the local wiring equations:
**NO_SAFE_CODE_SLICE**, supported independently by both owners above.

Recommended next action: after adjudicating R224's abstract relation, grant a
single source bridge packet at the actual bound-admission/cache owner to derive
the displayed `nativeBoundRestoration -> ConstrainRun` equation. Keep receiver
filtering and publication/use obligations separate and OPEN.

## Frozen handoff and commit packet

- Exact leased/changed path:
  `tasks/agent-loop/inbox/abstract-constrain-r224-owner-bridge.md` only.
- Author: `/root/r224_owner_bridge`; descendants: none. Actual role: researcher;
  runtime model/effort metadata: UNKNOWN. Launch receipt: parent assignment.
- Baseline SHA: `7a4e25417a2794d3d19e9cb128060ad240d2b255`.
- Changed dependency hashes: none observed. Direct hashes are recorded above;
  additional scoped-publication dependency matched the baseline blob.
- Claim/review status: partial source correspondence, conditional derivations,
  NO_SAFE_CODE_SLICE; independent review pending; no parent promotion.
- Checks already run: direct-input SHA-256 rechecks, baseline blob equality for
  both Rust owners and scoped publication, exact-method source reads. No tests.
- Worker state: STOPPED after this revision; **WRITES STOPPED** on submission.
  No unresolved descendant lease or generated output. Artifact hash is returned
  to Luna externally so it does not require a self-referential file hash.
- Proposed research-checkpoint commit message:
  `research: record R224 owner-local constrain bridge obligations`.
- Shared-record deltas intentionally left for Luna/curator: retain 0/4 roots and
  0/5 packages; record the two owner boundaries and optional-observation limit;
  keep Rust correspondence, intrusion, publication/use, residual-source meaning,
  and production promotion OPEN. No shared file was edited.
