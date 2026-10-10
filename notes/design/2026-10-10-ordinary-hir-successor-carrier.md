# Ordinary HIR successor source carrier

Status: Reviewed proposal; user approval pending
Scope: retain successor source facts during the ordinary `ParsedFile -> HirModule` path without changing existing HIR admission, items, errors, diagnostics, or occurrence identities
Baseline: `5fc8acfc0`
Authority: active user objective to use successor inference through ordinary entrypoints; existing HIR association, recovery, identity, and Simple-sub withdrawal contracts
Reviewed-by: spec_auditor and compiler_referee; two minor review findings repaired and delta-closed
Supersedes: none

## 1. Problem and constraints

The ordinary route is `lower_module` -> `ConstraintBatch::collect` ->
`SolvedModule::solve`. `lower_module` currently does not retain `LocalSource`.
The source carrier and its identity sidecar are available only through
`lower_module_with_local_source` under the HIR `shadow` feature. This blocks
ordinary successor collection from receiving the source-owned binders,
occurrences, lexical resolutions, and local forms already consumed by the
candidate collector.

Calling the opt-in lowerer from ordinary lowering is not behavior-preserving.
Its `local_source` switch also changes header admission, adds effect-declaration
diagnostics, applies a parameter-count refusal, allocates source occurrences
before ordinary body occurrences, and returns `StructuralProjection` for
unsupported or recovered source. Existing HIR authority requires those source
cases to remain an `Ok(HirModule)` with their established ordered errors and
diagnostics.

This draft selects no new source syntax, admission, recovery, typing, or effect
semantics. It does not claim a complete source carrier for every accepted HIR
form, complete Call, public scheme construction, or F5 retirement.

## 2. Proposed internal carrier contract

Ordinary HIR lowering remains the owner of item admission, namespace
resolution, recovery interpretation, diagnostics, `DefinitionRootId`, and
ordinary `HirOccurrenceId` allocation. After ordinary lowering has completed,
form exactly one source-carrier outcome for every already admitted binding, in
direct-root source order. Direct expressions and rejected headers are outside
this outcome domain. Carrier formation must not modify the ordinary product or
reinterpret its errors.

Store one explicit result per admitted root:

```text
SourceCarrierOutcome = Supported(LocalSource)
                     | Unsupported(SourceCarrierFailure)
```

`Unsupported` records the root and source origin/reason needed by successor
preflight. It is not a `HirError`, does not add a diagnostic, does not make
`lower_module` fail, and does not authorize fallback to F5. Genuine identity,
allocation, and internal projection failures remain ordinary availability
errors; they must not be blanket-converted to `Unsupported`.

The sidecar reuses the exact already-created root, admitted parameters,
namespace, source snapshot, and artifact. Stage additional identity and
provenance writes until that root's carrier succeeds; unsupported or failed
construction publishes no partial occurrence, local-binder, or local-parameter
mapping. It must not admit a rejected header, create a second module namespace,
parse source again, or mint replacement ordinary identities. Additional
source-structural occurrences are allocated only after ordinary lowering
finishes, processing roots and source children in source order, from the same
artifact and above its final ordinary occurrence ordinal. Existing ordinary
item resolutions and occurrence ordinals remain byte-for-byte observable as
before.

The builder's candidate grammar may remain a subset. Recovery, unsupported
forms, or its local supported-depth limit produce `Unsupported` for that root
while later roots and ordinary HIR diagnostics remain intact. Source identity
construction must not expose a partially formed carrier.

## 3. Ownership and phase boundary

Source provenance and carrier formation move from the `shadow`-only HIR
surface to an ordinary HIR-owned internal module. Existing `shadow` APIs become
adapters over that owner; `ShadowArtifact` remains separate and is not required
to form `LocalSource`.

The ordinary solver may read a supported carrier from its `Arc<HirModule>`.
That read does not itself select candidate collection or change `SolvedModule`
publication. Those are later migration gates and may not silently retain F5 as
a fallback for a source that the successor declines.

Ordinary rejected headers remain rejected in this gate. In particular,
multi-parameter and annotated root-header expansion needs a separate authority
audit; this carrier cannot expand admission by setting the existing opt-in
switch.

## 4. Required implementation evidence

Focused regressions must show that ordinary and source-bearing lowering agree
on existing items, ordered errors, diagnostics, recovery attachment, namespace
resolution, structural definition/parameter ordinals, and all ordinary
occurrence ordinals. Distinct lowering invocations have distinct artifact
brands, so compare structural identities across runs and assert exact branded-ID
reuse between each carrier and its owning HIR within one run. Include a
supported source body, a recovery-bearing body,
an unsupported body followed by another valid root, and a foreign-artifact
lookup. Carrier construction failure must leave no partial carrier or changed
ordinary result. A default-feature solver collection probe must consume the
same carrier identity once this integration is enabled.

Account for the source-key traversal, carrier traversal, retained map/arena,
and source-occurrence allocation. Avoid a second recovery interpretation,
second parse, full duplicate expression tree, and solver-side identity
reconstruction. If these costs cannot be bounded by the existing traversal
and storage owners, obtain a focused performance review before merging.

## 5. Decision and limits

This proposal is an internal architecture choice beyond the opt-in source
carrier checkpoint. Its intended outcome is determined by the user's ordinary
successor-inference objective; the exact sidecar and unsupported-result
representation remain to be approved under `rules/design-authority.md` before
implementation. It does not reopen Simple-sub let/generalization, parent-copy
intrusion, annotation polarity, or the existing HIR error contract.

The pre-write specification review confirmed that enabling the existing
`local_source` switch directly violates the established HIR contract. The
independent compiler review found two minor wording gaps: carrier outcome
coverage/allocation order and cross-run branded-ID comparison. This draft now
requires exactly one outcome per admitted root in source order, atomic staging
of sidecar identities, and structural comparison across distinct artifacts.
The fresh delta review closed both findings. No implementation review or
compiler verification has run.

Remaining gates include ordinary source/solver selection, complete Call,
contextual effect attachment and hygiene, live generalization, complete public
export and use, soundness/principality evidence, and removal of actual F5
consumers. This carrier proposal closes none of them.
