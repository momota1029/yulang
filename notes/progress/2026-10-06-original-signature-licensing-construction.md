# Original signature licensing: constructive factorization and the remaining leaf

Date: 2026-10-06
Baseline: `f551bac00adaa4fe7e8676f0bbeaee616674078c`
Branch supplied by primary: `research/simple-sub-intrusion`
Status: frozen, independently compiler-referee-reviewed research-only derivation attempt
Method: constructive proof, followed by last-rule inversion
Exclusive lease: this note only
Semantic and implementation authority: none
Review: compiler_referee PASS on content SHA-256 `9de3783b1663471e4191b2aa0e74aae12dce72b6805ca53540aa41c08c4f58e8`; minor notation repair by primary after review, recorded below

## Objective, result and authority

Construct original inferred-signature applicability/contribution licensing for
the selected source `my apply f = { my step x = f x; step }`, on one original
row. The construction reaches a **conditional incidence-image theorem** whose
unproved premises are a source-owned contribution attachment rule and its
exhaustive rooted inversion. This removes complete profile assembly from the
licensing proof interface; it does not discharge either premise, produce a
complete profile or establish an admitted row. There is no new source
counterexample, competing language meaning or proved need for a user decision.

Governing sections read directly:

- [FVIEW](../design/2026-10-05-inferred-function-call-views.md) §§1.1–5:
  original shared contract, static slots, distinct source/public/internal
  layers, Q-independent formation and open complete source judgments.
- [Directional addendum](../design/2026-10-06-directional-inferred-effect-protection-addendum.md)
  §§2–4: original protected-variable/upper-output introduction, no provider
  lower backflow and distinct witnesses versus slots. The direct user choice
  governs; the formalization grants no new semantics.
- [Source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
  §2, §3 opening, §6.1 and §§8–9: independently interpreted whole-tuple
  primitives; decorated source inputs; conditional allowance coverage;
  retained non-coverage kernel and Option A/2 extras.
- [Nested-block decision](../design/2026-10-06-nested-block-function-source-realization-addendum.md)
  §§1–3: exactly this sequential binding, returned closure and outer capture.

The independently reviewed [original applicability derivation](2026-10-06-original-profile-applicability-derivation.md)
and [policy quantifier audit](2026-10-06-profile-completeness-inference-falsification.md)
are inputs. Their exposure completeness and conditional policy assembly are
retained, not rerun as new independent results. The reviewed
[Oracle signature archaeology](2026-10-06-frozen-oracle-signature-applicability-archaeology.md)
is read only to preserve its negative boundary: frame grouping and a folded
Function shape are not current exhaustive licensing. No Oracle premise is
used below. The supporting [Call construction](2026-10-06-source-call-generation-construction.md)
§§4–5 and typed-boundary §6 were read to avoid incorrectly treating the
already constructed mandatory address attachment as a missing rule.

## Explicit hypotheses and sorts

Fix the approved resolved core graph C, original binder tree and one shared
`xi=(nu,K,D)`. Let X contain xi together with the original complete Function
demand U, providers, environment, continuation, world and all retained
constraints. X is a candidate whole row; membership in a complete/admitted
solution relation is not assumed. Every logical witness stays below its
original rigid dependencies.

Use these distinct sorts:

```text
e = (k,beta,u,sigma,outEff(U))    original upper introduction witness
t = (beta,s,p,c)                original licensed incidence
s                               static signature slot identity
p                               original signature observation position
c                               original contribution witness/contract
```

The contribution coordinate c is retained even when two effects have equal
endpoint values. It is not an outward event-support set or an actual receiver.
Inherited provider and result packets use their own source tags and remain
outside the newly beta-owned component. An inherited occurrence with the same
static beta is not thereby a fresh introduction by this source boundary.

Reused bounded hypotheses H are: the selected core correspondence and lexical
resolution; ordinary symbolic parameter/Name/Result/Lambda/Bind/Call rules;
the selected unannotated protected seed at the formal; and its original
scope-preserving exposure witness. These hypotheses emit complete checking
obligations without assuming their success.

Two additional candidate premises are stated separately:

```text
Attach_C(X,e,t)
    Independently source-licensed attachment of e to t, retaining the
    complete invocation contribution, original position and slot identity.

Lic_C(X,t)
    Independently interpreted ORIGINAL signature applicability/contribution
    judgment, before policy assembly or receiving-side transport.
```

Neither predicate is defined by the generator's output, solved type shape,
successful Q, admitted executions or this theorem. The mandatory static
`call.effect` attachment is already constructed by Gen-Call-0/ElimOrigin.
It does not supply a complete interpretation of Attach_C for every licensed
contribution or prove that Lic_C has no other last rules.

## Exact proof tree available before the open leaf

The following tree identifies all source premises of the one known witness.
R is the original inferred-contract root, not the syntax Result occurrence.

```text
outer formal d_f, annotation absent
-------------------------------- selected registration
Seed(k,d_f,A_f,R,sigma_f), beta=(d_f,R)

same resolved capture/name of d_f at sigma_x
Seed(k,d_f,A_f,R,sigma_f)
-------------------------------- typed same-root scope transport
ProtectedVarAt(k,A_f,sigma_x,u)

Call C_fx with callee Result(Name d_f), actual Result(Name d_x)
original Value bindings A_f,A_x and scope sigma_x
-------------------------------- Gen-Call-0 / ordinary Call
SourceUpperUse(u,A_f,U,sigma_x)
p0=outEff(U), ElimOrigin(C_fx,u,d_f,R,p0,p_out(C_fx))
emit WF_Dec(U;xi), VIncl(A_f,U;xi), WholeArgCompatible(J_x,CarrierContract(U);xi),
     CompleteCallImage(...) fits Comp(E_c,A_c)

ProtectedVarAt(k,A_f,sigma_x,u)  SourceUpperUse(u,A_f,U,sigma_x)
-------------------------------- selected Dir-Protect
e0=(k,beta,u,sigma_x,p0), NewProtection(e0)
```

This tree produces a source obligation, address correspondence and protection
record. It checks no world or complete carrier domain. The source-specific
ordinary-value formal refinement retains this introduction and changes no
actual provider role/entry. It supplies no annotation grant.

The reviewed exact 11-node inventory has one Call and no operation,
annotation, explicit elimination or recursive reference. Hence, under H,
the direct introduction domain `E_C(beta)` is `{e0}`. Returning step and
capturing f are transport/constructor cases; they cannot be substituted for
a second direct source introduction. This is a reused bounded result, not
the conclusion `Slots(beta)={p0}`.

## Conditional constructor and both coverage directions

Once Attach_C is independently interpreted, construct the incidence relation
by one indexed relational image, without choosing a witness for each port:

```text
G_C(X,t) iff exists e in E_C(beta). Attach_C(X,e,t).
```

This defines the **candidate generator**, not Lic_C. Attach_C may be a
relation: one exposure is not assumed to own exactly one static slot or one
contribution. Conversely, different exposure witnesses need not have distinct
slots. No equality quotient of slots is selected here.

The exact sufficient source premises are:

```text
A_sound:
  e in E_C(beta) and Attach_C(X,e,t) => Lic_C(X,t).

A_invert:
  Lic_C(X,t) => exists e in E_C(beta). Attach_C(X,e,t).
```

**Conditional theorem.** For every X satisfying H and both premises at its
original scopes, `G_C(X,t) iff Lic_C(X,t)` for every tagged t. The same X is
used in both implications; no completion or xi is chosen for a separate t.

Forward proof tree:

```text
G_C(X,t)
---------------- definition inversion
e in E_C(beta), Attach_C(X,e,t)
---------------- A_sound
Lic_C(X,t)
```

Reverse proof tree:

```text
Lic_C(X,t)
---------------- A_invert
e in E_C(beta), Attach_C(X,e,t)
---------------- generator image introduction
G_C(X,t)
```

For the exact candidate both directions reduce to the local law

```text
Lic_C(X,t) iff Attach_C(X,e0,t).
```

This reduction is narrower than assuming a completed OriginalSignatureFormation
object with policy/profile/receipt/admission already assembled. It needs only
source contribution attachment and exhaustive origin recovery. It preserves
their full semantic difficulty: the right side cannot be defined to equal
the left side to obtain a source construction.

The candidate final licensing rule would be

```text
e in E_C(beta)    Attach_C(X,e,t)
-------------------------------- Sig-Upper [candidate, unresolved]
Lic_C(X,t)
```

Its forward validity is A_sound. Its exhaustiveness requires proving that
every actual original last rule for beta-owned licensing factors through this
rule, namely A_invert. This note selects neither this rule as language
semantics nor a closed list of licensing alternatives.

## First unclosed leaf and decidability boundary

The exact missing constructive work is to give Attach_C its source clause and
prove A_sound/A_invert against an independently interpreted original signature
judgment. For e0 the immediate static address correspondence is known. The
remaining contribution clause must retain the complete invocation dependency
and explain which original contribution/position pairs it licenses; inversion
must exclude or account for every other beta-owned formation case.

The selected direction proves NewProtection(e0). It contains no premise or
conclusion enumerating Lic_C. Typed-boundary §6 supplies a profile to boundary
introduction and transports it by typed images; that cannot establish the
upstream inversion. Source-contracts §6.1 bounds complete Call allowances but
retains the non-coverage kernel and is a proposed allocation interpretation;
it is not original signature licensing. Whole-call bounds check descriptor
inclusion and cannot themselves create source ownership of a contribution.

The direct exposure side is independently decidable for this finite resolved
graph: binder absence, root identity, source Call and designated output address
are constructor data. There is no comparable demonstrated decision procedure
for Attach_C/Lic_C. Reading arbitrary xi as an oracle for those predicates
would simply hide this missing leaf. An independently interpreted semantic
predicate may be retained as an unsolved constraint; its being retained does
not prove decidability or a finite exhaustive constructor.

This is a precise constructive blocker, not an impossibility theorem or proof
that the language is underspecified. No new equivalent toy probe is useful:
a checker assuming Sig-Upper and its closedness would only verify the supplied
rules. The attempt stops before making that assumption authoritative.

Review closure: the compiler referee identified one minor notation issue in
the emitted Call obligations. The argument endpoint is checked against
`CarrierContract(U)`, not the complete Function demand `U`; the displayed
obligation now matches the reviewed Call construction. The factorization proof
does not depend on this notation repair. Primary diff inspection closed the
minor finding; no semantic or quantitative claim changed.

## Falsifier, nonemptiness and failure conditions

The theorem has a specific falsifier once an independent original licensing
clause is available: an X,t with Lic_C(X,t) but no Attach_C(X,e0,t) refutes
A_invert; an attached t unlicensed on that same X refutes A_sound. A different
slot number, normalized shape or endpoint value alone is not such a falsifier.
No admitted X,t satisfying either discriminator was constructed. There is no
claim of a minimized Yulang source counterexample.

Proof mutations have named failures:

- Replace Attach_C with equal effect endpoints: loses source/contribution
  identity and can reverse the provider-lower direction.
- Assert Sig-Upper is the only rule because C has one Call: confuses direct
  exposure inventory with original signature-rule inversion.
- Derive attachment from an admitted observation or Q: violates independent
  source formation and can erase a required position when an invocation never
  emits an outward event.
- Append an arbitrary latent path: lacks the original exposure/contribution
  rule; returning step supplies none by itself.
- Select different X for two t: the image proof no longer establishes either
  inclusion on one whole row.

These are logical mutations, with no executable mutation counts or seeds.
They discriminate proof obligations, not actual language acceptance.

Even a future proof of both incidence inclusions need not establish
`exists X. CompleteOriginalRow(X)`. All independently interpreted descriptor,
provider, imported/world and whole-carrier predicates remain active. For fixed
licensed support the no-annotation policy is protection with absent concrete
grant; the reviewed policy lemma gives only conditional assembly. Q-independent
initial admission and all finite histories require their separate source
constructors. Empty admission, a single successful identity run and a correct
receiving-side replay cannot prove this nonemptiness or closure.

## Checks, independence, resources and proposed record delta

Only this leased note was written. Read-only commands used bounded `cat`,
`sed -n`, `rg -n`, `rg --files`, `sha256sum`, a path-absence check, and Git
revision/branch reads. A Python byte comparison against `git show <baseline>:<path>`
confirmed all ten direct document dependencies equal their pinned blobs.
Initial aggregate captures truncated; decisive sections were reread in bounded
windows. No absence claim rests on a truncated capture.

No compiler code, test, build, checker, Oracle execution, random/exhaustive
search, formatting, scratch artifact, Git mutation or child delegation was
performed. This derivation shares the named governing/reviewed source premises
with prior constructions; its image theorem does not independently validate
those premises or certify itself. Oracle contributes no semantic premise.
Seeds/ranges, runtime mutation counts and performance samples are inapplicable.
Heavyweight processes: zero. CPU time, peak RAM and wall time were not measured;
the packet gave no numeric limits. Output-path budget: one note, consumed.

Unverified scope includes Attach_C/Lic_C construction and decidability,
complete original profile and row existence, initial/history admission,
recursive/general source coverage, all-view principality and production
Option A/2 inclusions. The note is frozen for review; writing stops here.

Recommended next action: derive the source clause for Attach_C and enumerate
the independently interpreted original licensing last rules, proving the two
displayed local implications on the same X before returning to profile assembly.

Proposed shared-record delta, intentionally left to primary/curator: record
the reduced licensing interface `Lic_C(X,t) iff Attach_C(X,e0,t)` as conditional
research with its source clause/inversion open. Do not mark complete profile,
admission or the first producer closed, and do not request a new user choice
without two fully specified observable alternatives. No shared record changed.

## Frozen dependency inventory

All paths below matched the baseline byte-for-byte; identifiers are SHA-256.

| Path under `notes/` | Hash |
| --- | --- |
| `design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `design/2026-10-06-directional-inferred-effect-protection-addendum.md` | `6b1779933499b360627fa5852c292ce97bda9830d146863b1b7ef440706054a7` |
| `design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `design/2026-10-06-nested-block-function-source-realization-addendum.md` | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |
| `design/2026-10-02-typed-boundary-realization-draft.md` | `1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb` |
| `design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `progress/2026-10-06-original-profile-applicability-derivation.md` | `d66a7ec9a57c676668d0ad4531a1607594e681a59c17d0cf239e29cd7cd02905` |
| `progress/2026-10-06-profile-completeness-inference-falsification.md` | `bd2292e8348b36d8af0a4324a923f6302ee5774d52f24d010097fc34494aebb9` |
| `progress/2026-10-06-frozen-oracle-signature-applicability-archaeology.md` | `1621abe333739b475222953ec52adfd5a67d54727c2b612bdee160186ede8b30` |
| `progress/2026-10-06-source-call-generation-construction.md` | `6bd7773326ccdd3101eaeb60a7e0f5d98a6c7a80b68467f6bf06a6466ffc4073` |

## Commit packet

- Exact leased/change path:
  `notes/progress/2026-10-06-original-signature-licensing-construction.md`.
- Baseline SHA: `f551bac00adaa4fe7e8676f0bbeaee616674078c`.
- Changed dependency hashes: none; ten direct documents match the baseline.
- Review status: frozen unreviewed conditional derivation and precise blocker;
  no independent review, theorem closure, semantics or implementation authority.
- Checks already run: governing-section and supporting-clause reads, exact
  proof/quantifier audit, dependency hashes and pinned byte comparisons, path
  absence and note-local integrity checks. No runtime verification.
- Proposed one-line research-checkpoint commit message:
  `research: factor original signature licensing through source incidences`.
- Shared-record deltas left for primary/curator: record the conditional
  incidence-image interface and its open attachment/inversion leaf; keep full
  profile, complete-row nonemptiness, independent admission and production
  conformance open. Task/theory/index/authority/question files remain untouched.
