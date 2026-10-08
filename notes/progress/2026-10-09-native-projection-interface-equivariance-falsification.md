# Native projection equivariance: bounded falsification characterization

Date: 2026-10-09
Baseline: `c27870a13d2ff9205c94e973224ab1a1b4df9360`
Status: unreviewed research characterization; frozen at submission
Scope: selected native PE-ID and finite-public-import PE-PICK rule skeletons
Production implementation / IFACE_EQUIV closure: none

## Objective, method and result

Search the selected native constructors and observers for a sort/scope-preserving
renaming that changes truth, evidence or observations, or exposes a missing
rigid identity. Method: source-clause inspection and a local record-law
mutation, rather than a checker that supplies its own transition semantics.
No executable semantic experiment, test, build or enumeration ran.

No lawful counterexample was found in the inspected rule skeletons. This is
bounded source inspection, not exhaustive falsification over every authentic
local registry entry. The smallest useful discriminator is a binding lookup
after incorrectly treating an externally registered slot as an alpha-local
name. It defeats sort/scope preservation alone and is excluded by the pinned
CI rigid-anchor condition. It does not refute PE-ID, PE-PICK or CI_USE.

The selected phase construction already states rule-by-rule whole-action
equivariance in its §6. The new characterization identifies where this
argument must stop when a fixed opaque law has semantic identity observations
whose covariance is not independently supplied.

## Pinned authority and inputs

Read the following at the baseline revision:

- [Native projection selection](../design/2026-10-08-native-projection-public-export-definition.md)
  §§2–4: native formation before Build; transformed public allocation;
  retained fixed anchors and finite-public-import boundary.
- [Projection construction](../theory/2026-10-08-projection-public-export-construction.md)
  §§3,3.1,4.1–4.3,6–8: typed slot map, simultaneous alias substitution,
  actual-root checking, independent W and fixed import closure.
- [Native certificates](../theory/2026-10-08-native-projection-certificate-constructors.md)
  §§3–4: fixed local registry and Bind/Project/Restrict/Return/frame records.
- [Recursive synthesis](2026-10-07-successor-recursive-synthesis.md) §5.1:
  names for bound coordinates/internal nodes; fixed semantic identities;
  independently supplied operation laws and complete identity accounting.
- [Obligation DAG](../theory/successor-proof-obligations.md), IFACE-EQUIV and
  CI_USE: actual operation laws remain open; CI_USE retains those premises.
- Supporting selected [phase constructor](../theory/2026-10-08-id-public-phase-constructor.md)
  §§3–4,6–7 and [uniform inlet](../theory/2026-10-08-uniform-value-entry-constructor.md)
  §§4.2–4.3,7.1: complete histories, explicit whole-action claim, fixed pick
  capture, and q/source-slot intrinsic registrations.

Retained decisions: instantiate eligible descriptions before challenges; act
once on the whole incidence/telescope; keep actual provider, capture and
external inputs fixed; retain all proof choices; keep independent Option 2
members; do not identify foreign kernels with native constructors. No source
or language meaning is selected by this note.

Pinned SHA-256 dependencies, in the order above:

```text
aed6ef63b01f555a5f2804f87a599167c1a30fa999afc0b9d9f11b8ae974a919  notes/design/2026-10-08-native-projection-public-export-definition.md
4cf84e7a38153b893f1d339780598e2b79084c747ecb883acf0e4fdaa49cf631  notes/theory/2026-10-08-projection-public-export-construction.md
04c5699dfaaf5f98ee9db54df5bd124f25e7131abb6bc3104e1675a5490f74a8  notes/theory/2026-10-08-native-projection-certificate-constructors.md
e34a568946f5c1946c01828aae34e890747477ee8c272775408438acd95aa43f  notes/progress/2026-10-07-successor-recursive-synthesis.md
41e25bc633f69df302361f41c60c0c324e9713a7194373f23f9f7a182724e4a1  notes/theory/successor-proof-obligations.md
140c9c907f3ae27120acd84d96c75b2d9a64b437e3e0e71c540c0030864ebb6b  notes/theory/2026-10-08-id-public-phase-constructor.md
273e8dae447e9997d586fc07abf48883c76b90988c8906094dd428a48339c2e5  notes/theory/2026-10-08-uniform-value-entry-constructor.md
```

## Exact action and conditional structural result

Separate a *reference name* from the semantic identity stored at that reference.
Let h be a bijection of alpha-local reference names preserving typed sort,
scope/order, every ordered operand, sharing edge and designated export. A
corresponding assignment is defined by

```text
rho_h(h(x)) = rho(x).
```

This moves the spelling of a local reference, while retaining its assigned
semantic value. It does not replace a source binder, raw provider, installed
slot, receipt, registered root or live authority by a distinct one. Fix all
rigid inputs in the same original fiber. Fixed L tags, entries and equation
declarations are not renamed into different rules. Original proof values,
including Identity versus Compose and their intermediates, stay distinct.

**Conditional structural result.** If every leaf operation receives the same
semantic operands under this assignment correspondence, or has its independently
supplied whole-action preservation/reflection law when semantic operands
themselves transport, then the inspected native record skeleton preserves and
reflects all its finite derivations and their full retained outputs.

For dependent records this follows field by field: each renamed reference
evaluates to its original operand; equality and record projection therefore
have the same truth/output. Fixed constructor tags preserve alternatives;
whole telescopes preserve dependencies and field absence. For a rule image,
use the actual leaf law, and then assemble the same full result record.
Induction on finite proof/development trees transports each child and parent;
h inverse proves reflection. Registered recursive references use their
original declaration and finite-development law, not an arbitrary accepted
cycle. No histories are shortened and no independent member is source-filtered.

The same argument commutes with the PE raw-alias graph: h(z)=h(t) is the
transport of z=t, and total substitution acts on every incident operand,
including W. When the client W stays literally unchanged, all semantic client
coordinates it reads must stay fixed. A W that contains a fixed identity
constant for an internal node makes that identity rigid; leaving that constant
unchanged while moving its denotation is outside the hypotheses. PE's
arbitrary-W fiber equality alone is not a theorem of arbitrary renaming.

This result is conditional at the authentic leaf laws. It does not prove
equivariance of an opaque primitive merely because its interpretation or
registry name is unchanged. The reference-name subcase supplies identical
semantic arguments; a nontrivial action on an operation's semantic identity
arguments needs the separate law required by CI §5.1.

## One minimized omitted-rigidity discriminator

Use the actual native `ProjectIntro` law (§4.2), not a newly invented observer.
Assume an independently valid immutable world certificate omega whose retained
environment has two authentic registered slots b0,b1 of the same sort and scope:

```text
omega.env[b0] = beta0,  Lookup(C,b0) = (v0,p0)
omega.env[b1] = beta1,  Lookup(C,b1) = (v1,p1)
(v0,p0) != (v1,p1).
```

Each beta includes its independently typed hereditary evidence and original
incidences. Distinct Bool values true/false provide the raw distinction already
present in the selected native semantics, if an authentic world with these
two registered bindings is supplied. Existence of that complete world and
its original registration/compatibility evidence is an explicit premise;
this is not a constructed complete source-program counterexample.

The native constructor accepts `ProjectIntro(b0;omega,beta0)`: beta0 is exactly
omega's retained field at b0. Mutate only slot-reference eligibility: allow
h to swap the *semantic* registered slots b0,b1, keep external omega/C and the
selected beta0/value/provider fixed, and treat matching sorts/scopes as enough.
The purported transported record is `ProjectIntro(b1;omega,beta0)`. Its
required record equality now reads beta0=omega.env[b1]=beta1, which fails
because their raw projections differ. The old output `(v0,p0)` also differs
from the actual Lookup output `(v1,p1)`. Preservation therefore fails; applying
the inverse swap gives the corresponding reflection failure.

This is the smallest nondegenerate discriminator within *two registered
lookup targets with distinct outputs*: one lookup, one retained projection,
two slots. A single registered slot swapped with an unregistered spelling
fails even earlier at registration, but adds no discriminator beyond that
typing failure. No global minimality over all Yulang observations is claimed.

The mutation is inadmissible under CI §5.1: b0/b1 are original binding/slot
identities read by a fixed external environment, not interchangeable names
for the same identity. Uniform inlet §7.1 explicitly calls q and source-slot
identity intrinsic registrations. Projection §3.1 and PE-PICK §8 retain the
actual original slot and fixed capture closure. Thus this exposes no omitted
rigidity in those sections; it is a concrete rejection test for an overly
permissive proposed renaming classifier.

## Inspected identity readers and stopping boundary

| Site | Actual identity-sensitive read | Required handling |
| --- | --- | --- |
| BindIntro / ProjectIntro | Authentic installed slot; retained environment field; input value/provider | Fix original registrations and external environment; rename only references to them. |
| RestrictIntro | Same binding/root/provider; current history, authority/scope/lifetime | Keep semantic lineage; independently justify any nontrivial history/context action. |
| PureReturn / InvocationReturn | Original result/provider/root port; current own occurrence and receipt/order | Transport whole incidence once; never exchange current and historical occurrences. |
| VP initial/Response/Raw/Future | Registered holes, request, raw handle, returned provider and original port | Retain complete dependent records; external compatibility laws remain authentic inputs. |
| ValueInletSchema / PackGeneric | q/IF0 registration; actual J witness and whole observation-image proof | Fixed intrinsic q/IF0; same proof choice and original telescope. |
| Decode / alias allocation | Same original frame versus distinct real new; Shared and event dependencies | Whole frame action; aliases retain sharing; new events stay distinct. |
| Direct §6.1 | Actual submitted root lookup; proof named root must match that record; fixed L entry/equation | Distinguish a local graph reference from a registry-visible semantic root handle. Fix the latter when external lookup/client coordinates are fixed. |
| Fixed(J_z) / captured Read | Actual captured value/provider/slot and complete free import closure | Keep J_z and its monomorphic closure fixed; printed type equality permits no replacement. |
| CE / client W | Proof choices, intermediate evidence, raw-alias graph and shared coordinates | Total substitution; no canonicalization or per-port witness replacement. |

The Direct row is particularly relevant to a classifier: an internal graph
node label can change while continuing to denote the same actual root. A
registry-visible root handle read as an identity cannot be exchanged merely
because the corresponding records have the same head or printed scheme.
CI §5.1 already includes client/query-resolution identity tests, and CI_USE
fixes original/client coordinates. No new mandatory semantic field follows.

Unverified cases include additional authentic `Local_f`, registry guarantee,
method/adapter/conversion or equation laws; opaque V/W/T/Car/history/Strict
operations under nontrivial semantic nominal actions; arbitrary foreign W/Z;
actual compiler producers and query lookup representation; general State or
recursive constructors. Merely importing an unchanged certificate does not
establish its covariance. No arbitrary extension was invented to force failure.

The exact blocker to a stronger no-counterexample theorem is the absence in
this bounded inspection of an exhaustive instantiated declaration/law inventory
for those authentic opaque operations. Another toy transition checker sharing
the same assumed laws would leave that premise untouched.

## Coverage, checks, resources and next action

Coverage is the documentary inventory above: four certificate families, four
independent history constructors, seven outer VP phases plus Restrict/Develop/
Future, public decode/aliases, three Direct wrappers, and finite-public-import
pick. This is not enumeration over all terms or histories. There are no seeds,
numeric ranges, sample counts, executable mutations or timed searches.

Commands: pinned `git show c27870a13:<path>` with bounded section reads;
`rg` for governing locators; `sha256sum` for pinned inputs; narrow lease status
inspection. No Git mutations, tests/builds, compiler edits, child processes for
research calculations or heavyweight jobs. Only this leased note was written.
CPU/RSS/total research wall time were not instrumented; tool commands were
lightweight sequential reads. Markdown integrity and live dependency equality
are checked at submission; they are not independent review.

Recommended next action: have the primary require the constructive sublemma
to distinguish reference renaming from semantic identity action, and enumerate
the exact active opaque declarations whose separate laws it retains. Use the
two-slot mutation to reject an action that moves an external registration.

## Commit packet

- Exact lease: `notes/progress/2026-10-09-native-projection-interface-equivariance-falsification.md`.
- Baseline: `c27870a13d2ff9205c94e973224ab1a1b4df9360`.
- Changed dependency hashes: none in pinned inputs; live equality reported at submission.
- Claim/review: bounded source characterization and conditional structural result;
  one inadmissible local mutation discriminator; unreviewed research-only.
- Checks already run: pinned section inspection and dependency SHA-256 collection;
  final note integrity/dependency checks reported at submission. No tests/builds.
- Proposed commit: `research: characterize native projection renaming and rigid lookup mutation`.
- Shared-record deltas intentionally left to primary/curator: record bounded
  identity-reader coverage if accepted; retain IFACE_EQUIV OPEN-PROOF and CI_USE
  CONDITIONAL-CLOSED; promote no compiler correspondence or theorem closure.
- Writing stops before frozen review; the producer supplies no independent review.
