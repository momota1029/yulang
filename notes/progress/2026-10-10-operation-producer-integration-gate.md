# Authentic operation producer integration gate

Date: 2026-10-10
Baseline: `4c3a74356991a7e94e7c49e1c39115bf23557473`
Status: producer implemented and verified; execution supplier pending
Authority: current complete-inference implementation objective,
[constructor packet](2026-10-10-authentic-operation-source-next-gate.md),
charter §§17–18 and frozen Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Mode: M2; semantic and conformance closure reviews; measurement budget zero

`operation_hir_owner_map` and `operation_signature_effect_owner_map` identify
actual constructor owners. Pre-write `operation_producer_prewrite` confirms
this producer slice needs no additional semantic selection. These are
implementation conditions, not a full Call or cutover certification.

## Confirmed construction

HIR retains nullary Act families and every admitted bodyless typed operation
member, declaration-owned identity `(SourceEffectId, member SourceNodeKey)`,
visibility, name/signature positions and original signature. Collect all family
headers before resolving signature rows. Preserve duplicate/private/missing and
recovery failures; do not suppress them as legacy placeholders. Direct-root
`family::operation` resolves the actual namespace, distinct from field access.
Ordinary name-resolution indexes are construction outputs, not a frozen Call
registry prerequisite; build once rather than scanning all declarations per use.

The existing Unit/Int/variable/Function type carrier is reused structurally.
Require an outer Function; retain the current bounded type depth, nullary family
and at-most-one-symbolic-tail envelope. Reject unsupported concrete rows at
composed negative positions, unresolved row operands and unsupported family
arguments explicitly. No annotation wrapper is fabricated for a signature.

Each operation lookup constructs its own positive signature instance with
ordinary fresh variable environments. Variables introduced by the signature
are younger than the enclosing source level, permitting normal alias
generalization and independent subsequent uses. Missing negative effect rows
are pure/empty; missing positive rows are bottom/pure, including nested
Functions. Prepend the owning family only to the outer Function's return-effect
row, preserving original members and symbolic tail. Lookup evaluation itself
has exact-pure ordinary name effects.

## Effect ownership and transport

Generalize immutable support-view provenance to distinguish actual annotations
from actual operation interfaces. Retain operation identity, signature/source
position and originating use occurrence. Borrowed conflicts must report an
operation-interface member truthfully, never an invented annotation or emitted
contribution. Existing annotation handles retain their actual annotation owner.

Use the existing support expansion and nominal family comparisons; ordinary
alias/capture/freshening/extrusion/intrusion transport preserves typed provenance
and independent instance identity. Journal and account for added owned payload
and scratch using the current fallible mechanisms. No global registry, early
satisfiability test or source-callee-shape Force is introduced.

Ordinary Apply constraints and truthful pending Call suppliers remain. Native
request-carrier construction and request-exposing execution are distinct. This
slice retains declared interface operands; it creates no execution contribution
or subtraction attachment at lookup and supplies no executable consumer recipe.
Complete Call, hygiene, soundness, principality, public schemes and F5 replacement
remain required subsequent gates.

## Verification and convergence

Freeze HIR and solver dependency combination before two independent reviews.
Run owning all-target checks and focused added source tests plus unchanged Unit,
annotation, intrusion, live-local and lifecycle controls. Verify retained bodies,
typed signatures, qualified/private/missing/duplicate resolution, pure lookup,
independent polymorphic instances, wrong arguments, actual interface diagnostics,
aliases/capture and rollback. Preserve existing tests and resource expectations.
Converge with no accepted major/blocking finding; primary owns Cargo, records,
Git and whole outbound inspection. No benchmark is selected.

Delivery, review repairs and exact verification are recorded in
[the integration delivery](2026-10-10-operation-producer-integration.md).
Empty nullary Act bodies are admitted by this declaration-owner expansion;
the previous unsupported-body fixture premise is retired, not preserved as a
language restriction. Original return-row members, including repeated owning
families, retain their sequence after the prepended family.
