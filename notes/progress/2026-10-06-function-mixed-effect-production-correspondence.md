# Mixed Function effect profile: production correspondence boundary

Date: 2026-10-06 (assignment label)
Status: Unreviewed research-only bounded source characterization
Baseline: `45b81a28d614f9f0a4d15c7a861347cb14506566`
Lease: this file only; previous invocation source-bridge artifact remains frozen
Method: static representation derivation and source/design correspondence audit

## 1. Objective and governing decisions

Find whether the existing production F5 objects can express the approved
mixed profile, and identify the exact source premise connecting the profile
to the supplied typed-boundary evidence. This lane does not repeat identity
carrier reductions, finite attachment searches or handler-transition probes.

Authority is the committed q1/d1 mixed-row answer
`questions/2026-10-05-function-effect-row-denotation/approved-answer.md`, blob
`77e28d7826634421a98e556a0023b29c762420ad`, validated by its receipt, blob
`7d77c531937422b37f93d36b50924a1042f3e605`. Its exact decisions 2–6 govern:

- Covariant `['e, write int]` permits the shared `'e` together with `write int`,
  with `'e` also occurring contravariantly.
- Contravariant `['e, write int]` requires compatibility for a matching
  `write 'a` inside `'e`; the supplied instance is `int <: 'a`.
- The selected removal is for the illustrated deep-handler case, preserving
  original request/continuation/path/attachment evidence at one `(nu,K,D)`.
  The shallow principal-type expression remains tentative.
- No general family variance, complete membership rule, parser spelling,
  new carrier or compiler implementation is approved.

The governing design records this in
`notes/design/2026-10-03-concrete-compatibility-boundary.md` §9, lines
1912–1957. Its §§6–8, especially lines 120–159, distinguish existing
subtraction/path evidence from its missing successor source interpretation.
The F5 foundation is Authoritative within its declared pure subset:
`notes/design/2026-09-21-f5-general-function-scheme-foundation-draft.md` §§1–3
explicitly excludes annotations, dynamic dependencies and effects beyond
closed pure Functions. This absence is an existing gate boundary, not a newly
discovered compiler defect.

The typed-boundary draft, §§6–8, contains reviewed conditional transport and
decorated-context results; its header still excludes complete source
realization and implementation authority. The coupled-interface draft's
`TypedRow` and relational handler-image rules remain candidate constructions.
Reviewed mathematics in those records is not a reviewed production profile
generator.

## 2. Smallest fragment and precise missing premise

Use exactly the approved fragment, rather than inventing a full handler body
or assigning a principal type:

```text
at a role-selected contravariant port p_in: ['e, write int]
at its linked covariant port p_out: the shared 'e after targeted removal
one matching contribution in 'e: write 'a
required concrete compatibility instance: int <: 'a
```

This has one abstract component, one concrete component and two incidences of
the same abstract view. It is the smallest useful source-interface obligation
for this audit; it is not a complete source signature, accepted production
program or global minimality theorem. No new deep-handler syntax or body is
introduced. The separate covariant allowance case has the same component
inventory, but does not by itself assert capture or removal.

The missing formation premise can be stated without a new carrier:

> Source elaboration of this row occurrence, after role and typed-port
> selection, supplies its original annotation occurrence, the same abstract
> complete-view root at the input/output incidences, the concrete `write int`
> contract at its exact profile position, and the corresponding source-owned
> `(nu,K,D)`/request/path witnesses. Its compatibility derivation produces the
> specified `int <: 'a` obligation, while its separate handler-image
> derivation licenses only the targeted removal.

The current production HIR/F5 path does not generate this premise. HIR's
`plain_binding_header` (`crates/yu-hir/src/module.rs:1471–1533`) admits only
plain identifier headers. `ResolvedExpr` at line 426 has Lambda, Integer,
Name and Error, with no annotation/profile/operation/handler constructor.
`HirModule` at line 705 retains source revision and items/errors, not a
decorated row-profile graph. An annotation can exist in lossless syntax
without becoming a resolved production Function recipe. No claim is made
that the language, every HIR representation or legacy compiler lacks mixed
rows; this is the scoped F5 entrypoint.

## 3. Representation derivation from production code

There is a stronger bounded fact than a missing test: the existing decoded
closed F5 effect grammar has no mixed-profile alternative.

1. `crates/yu-types/src/lib.rs:614–620` exhaustively defines
   `PositiveEffectView = Bottom` and `NegativeEffectView = Empty`.
2. Their finalizer constructors at lines 1917–1935 store `()` payloads.
   The effect lookup methods at lines 851–867 validate the handle and always
   return the respective sole variant.
3. Function views at lines 590–609 expose those effect handles alongside
   value ports. No decoded effect node carries an abstract binder, family,
   concrete argument, profile position or subtraction witness.
4. `crates/yu-solver/src/f5c_generalization.rs:470–476` uses the same singleton
   effect variants. Production Function finalization in solver `lib.rs:15256–15263`
   reconstructs the negative Empty and positive Bottom effects.

Therefore, through the existing reviewed F5 effect observation interface,
every successfully decoded closed effect field has the same variant for its
polarity. It cannot expose either the concrete `write int` item or the linked
abstract profile of this fragment. Distinct arena handles remain real
identities; no reviewed semantics assigns a family/profile meaning to their
raw index. Encoding the profile through such indices would require a new
interpretation contract, and is not established by this audit.

The retained live store is richer than the closed effect API in one respect:
solver `lib.rs:723–727` has `EffectRow(u32)`; `EffectBounds` at lines 3712–3719
retains lower/upper row links and extrema; `effect_endpoint` at lines
10631–10651 accepts only those rows and the two effect leaves. Those links
can preserve shared row identities. They provide no concrete-family term or
profile/attachment payload, and the Function comparator at lines 11164–11192
only dispatches the four child pairs. HIR occurrences and fact provenance
can name where facts came from; they do not turn a pure row term into
`Gamma_b(p)` or a complete request instance.

This is an established characterization of the listed production schemas,
subject to the pinned source envelope. It is not a language nonexpressivity
theorem, a proof of carrier insufficiency or authority to extend F5.

## 4. What typed-boundary objects can express conditionally

The reviewed typed-boundary package already has mathematical locations for
the necessary facts, if source construction supplies them:

| Required fact | Existing candidate/design object | Missing production correspondence |
| --- | --- | --- |
| Role, receiver, exact profile port | Boundary `b=(receiver r,slot a,Gamma,endpoints)`, typed-boundary §6, lines 683–700 | Source elaboration must assign this row occurrence to `Gamma_b(p_in)` after role selection. Family support does not reconstruct the profile. |
| Shared abstract component at two ports | Typed view packet `(v,t,chi,K,D,L)`, lines 730–753; path correspondence transports `chi,D`, retaining `K,L` under one `nu` | F5 row links are not a proved interpretation of these complete view packets. No emitted mapping for `'e` at `p_in,p_out` exists here. |
| Concrete operation/family instance | Supplied `OpInst`/compatibility described by concrete-compatibility lines 318–329; the complete relation retains payload/response and witnesses | The row item does not itself construct a request, and current F5 has no concrete family node from which `int <: 'a` can be generated. |
| Event eligibility at this profile | `Receive`, `Observe`, `Path`, `Inc_C`, `Grant`, typed-boundary lines 794–851 | Production fact-admission receipts/provenance are not invocation receipts or event-specific typed incidence. |
| Targeted subtraction | Existing source request/path/attachment witness plus complete derived deep-handler image, compatibility §9 | A row-support match or `Grant` alone does not prove removal or absence of remaining output contributions. |
| Residual publication with sharing | Joint `Rel_C`, original scopes and retained `K,D`; handler support is projected from its full image | Current F5 generalization emits no combined profile/handler-image contract. A complete transport proof is needed before calling its residual the shared `'e`. |

Thus the mathematical typed-boundary objects can express a *supplied*
mixed-profile incidence and its local eligibility obligation. They are not
production objects or an exhaustive mixed-row membership implementation.
The existing capture-profile derivation note explicitly assumes the
annotation-to-`Gamma_b` premise and leaves the combination/removal proof open;
this audit corroborates its production seam rather than claiming to close it.

## 5. Membership, eligibility and subtraction stay separate

The following conditional deductions are licensed by the cited sources, not
new row rules:

1. A concrete type/family support match can discharge its specified
   compatibility subcase; for the approved matching `write 'a` example that
   subcase requires `int <: 'a`. It does not identify the abstract occurrence
   with the concrete annotation or choose a different witness for each port.
2. Unfolding typed-boundary `Grant` additionally requires `Inc_C`, ownership
   and the explicit profile contract. Compatibility alone does not entail
   those premises. Handler/receiver expiry sets `Inc_C` false while a static
   family/type match can remain unchanged (lines 839–856). This is a direct
   equation-level discriminator, not a newly executed state model.
3. Even a granted and selected event does not alone establish subtraction of
   its support point. Compatibility §9 requires its original attachment and
   the full derived deep image, including selector/arm effects, re-emissions,
   latent results and future uses. Ordinary computation semantics §5 has one
   primitive shallow image; deep behavior comes from explicit recursive
   reapplication. The name “deep” supplies no new grant or wrapping rule.

The support projection of an established complete image omits a point only
if that image has no remaining contribution at the point. This projection
fact does not define the annotation's complete membership or prove that the
handler image has the required absence. The previous two-event attachment
probe assumes attachment/consumption/output flags; its counts are historical
bounded evidence, not results rerun here. No same-family cancellation or
general family variance follows.

The exact blocker is consequently source formation of the shared abstract
view and concrete profile, followed by a distinct complete-image removal
proof. Another support-only checker would assume both missing premises.

## 6. Checks, independence and unverified scope

Checks used committed `git show BASE:path` with bounded line ranges/searches,
scoped `git grep` over `yu-hir`, `yu-solver`, `yu-types`, and dependency blob
queries. The approved answer and receipt were read directly. A search for
`TypedRow`, `OpInst`, `Inc_C`, `Rel_C` and subtraction/profile-related names
in those packages found no production semantic counterpart; HIR diagnostic
`HirErrorAttachment` is unrelated to effect-contribution attachment.
Negative name search alone is not the representation argument; §3 uses
exhaustive variants and their lookup/finalizer code.

At handoff, all 15 listed dependency blobs matched fixed HEAD
`45b81a28d614f9f0a4d15c7a861347cb14506566`. The previous invocation note's
SHA-256 remained `dcdb32c6c7aa7e055baabd11f7af23523e22d2a1158620a6c1f04a46d8fee828`;
it was not modified.

Implementation source and semantic decisions are independently specified
inputs. They share the approved contract; the typed-boundary equations remain
conditional on supplied decorations. No checker assuming their transitions
was treated as proof that source generates them. Claim classes are: bounded
production schema characterization, conditional typed-boundary deductions,
and an open source formation/removal premise. No independent review of this
note is claimed.

No tests, builds, executable probes, seeds/ranges, mutation runs, benchmarks,
formatters, Git mutations or children. The proposed discriminator is to
preserve a family/type match while removing its exact active typed incidence;
it would reject a family-only grant shortcut. It was not executed. Source
reads completed below one second per command. CPU/RAM and total reasoning
wall time were not instrumented; computation consisted only of lightweight
reads and the leased note write.

Omitted: whole-workspace/legacy/core-IR audit, runtime source execution,
complete annotation elaboration, general family instances, recursive
handler typing, principal shallow types, arbitrary Option 2 extras and
generalization of an already generated mixed contract. The representation
claim must be revised if another reachable in-scope production generator
or reviewed interpretation supplies this profile. None was found in the
bounded F5 path; no global absence claim is made.

## 7. Dependencies and next obligation

All direct dependency IDs below are Git blob hashes at the baseline:

| Path | Blob |
| --- | --- |
| `crates/yu-hir/src/module.rs` | `668d1b6f82fb17a96178a2353543d288c32e2762` |
| `crates/yu-hir/src/lib.rs` | `0c5e1ac6c1acba5707b33911be82fe4a1d75caa0` |
| `crates/yu-solver/src/lib.rs` | `fa118b726ebbfdc7d32b617373b4e2cb04e84682` |
| `crates/yu-solver/src/term.rs` | `001ffd3022b2fad0d7d67e0a853aaeb83db00b12` |
| `crates/yu-solver/src/f5c_generalization.rs` | `4d0d598c7a702cdfc37eaf77af4e9dbbe8243ec9` |
| `crates/yu-types/src/lib.rs` | `c3a4e95d199fba0784b7e6448b6bb37a1f2c7798` |
| F5 foundation | `51d37bb77b069bfbcd8d7c320b7ced64f51c401b` |
| Concrete compatibility | `07e2c58a928540c730dd67e74f2e65161ea6a9b5` |
| Typed-boundary realization | `5e0499e43b3dbf04de0bcdb6c0fa5994224d8a87` |
| Coupled effect-interface core | `841325b72ab797729b9f26d4569007ec6694c99b` |
| Ordinary computation semantics | `640bbfa85630d1dd496a3fd1ccb757536385d720` |
| Concrete capture-profile derivation progress | `8b23a4f3349d4048748b16ecdc7beb11c84551db` |
| Attachment-subtraction progress | `15ccc59ef531e4c5e84fe4e41cdb36d7b321ecb4` |
| Mixed-row approved answer | `77e28d7826634421a98e556a0023b29c762420ad` |
| Mixed-row receipt | `7d77c531937422b37f93d36b50924a1042f3e605` |

Recommended next action: construct and independently review one source
formation derivation for this exact row fragment, explicitly mapping its
two `'e` incidences and concrete annotation to the existing complete view and
`Gamma_b` at one original `(nu,K,D)`, and emitting only the approved
compatibility instance. Keep its targeted complete deep-image removal lemma
as a separate obligation. Production representation/implementation remains
behind the existing approval gate.

Commit packet:

- Exact leased paths: `notes/progress/2026-10-06-function-mixed-effect-production-correspondence.md` only.
- Baseline SHA: `45b81a28d614f9f0a4d15c7a861347cb14506566`.
- Dependency hashes changed: none by this lane; all reads were pinned objects.
  Recheck these dependencies against integration HEAD before acceptance.
- Review status: frozen, unreviewed research characterization; conditional
  typed-boundary deductions; no mixed-row conformance or theorem closure.
- Checks already run: narrow committed source/design/receipt searches and
  dependency blob queries, output-lease absence and final note path/hash check.
  Zero tests/builds/probes/mutation runs.
- Proposed message: `research: isolate mixed Function profile production correspondence gap`.
- Shared-record deltas left for primary/curator: link the static F5 effect
  grammar boundary and exact annotation-to-profile premise from the mixed-row
  source bridge entry; preserve separate membership, eligibility and
  complete-image subtraction statuses. No shared records or frozen artifacts
  were edited.

Writing stops at frozen handoff.
