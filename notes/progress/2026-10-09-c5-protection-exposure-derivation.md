# C5: source seed to protected-variable exposure

Date: 2026-10-09
Baseline: primary-pinned `4e5e7fc7cf60cd1731f7d528754e86dcc70f9b2c` on `research/simple-sub-intrusion`
Status: frozen unreviewed research derivation; non-authoritative
Method: constructor composition and coverage-premise separation
Exclusive write lease: this file only
Production, semantic-choice and implementation authority: none

## Objective and result

Reduce C5's source-to-exposure obligation without choosing a temporal ordering,
recursive aggregation, multi-use conflict policy or role-refinement semantics.
For the selected original unannotated formal and certified direct/captured
Name Call, registration and a source derivation preserving its seed-bearing
endpoint suffice. For *every required* exposure, one additional coverage lemma
is necessary: every such exposure has that source derivation, or another
independently justified seed-at-exposure derivation. A seed inventory joined
to an upper inventory does not supply this lemma.

This is a conditional constructor theorem and a smallest missing-premise
statement. The selected annotation-absence/directional boundary is retained;
no unconditional C5, source-adequacy, principality or production closure follows.

## Governing sources and dependencies

- `notes/design/2026-10-05-inferred-function-call-views.md` §§2–3,5:
  original annotation presence, shared formal/use relation and scope survive;
  the exact selected formal is provisionally protected; detailed inference
  rules and their coverage remain open. §4 is used only for the accepted
  annotation permission boundary.
- `notes/design/2026-10-06-directional-inferred-effect-protection-addendum.md`
  §§2–4: `ProtectedVarAt` and original `SourceUpperUse` justify only the
  designated upper output occurrence; lower/provider protection is independent;
  arbitrary exposure-stage production is not specified.
- `notes/theory/2026-10-08-production-call-elaboration-proposal.md` §§3–5,
  §7 C5: candidate SeedFormal/RefineFormal require the retained exposure facts;
  conflict, recursion and principal interpretation remain open.
- `notes/progress/2026-10-09-annotated-formal-seed-inversion.md`: an actual
  annotated binder cannot instantiate the absence constructor; conserved
  extensions cannot create that missing origin. This does not establish a
  general no-seed judgment.
- `notes/progress/2026-10-06-directional-joint-source-judgment.md` §§3.1–3.2
  and S1 supply the selected registration/Name/Call composition; §§4–7 explain
  its conditional multi-use, refinement and transport boundaries.

The last source is a progress note, not a selected complete source calculus.
Its S1 composition is reused as a published bounded derivation, not certified
independently here. This note adds the explicit coverage factorization below.

## Exact hypotheses and conditional judgment

Let `b` be the original formal, `v` its registered inferred endpoint, `R` its
shared contract root, `k` its original seed and `sigma` its source scope. Let
`u` be an original Function upper exposure with complete view `U`.

H1. The source is the selected unannotated `apply f x = f x` pattern or its
already selected captured nested counterpart; original binder `b` actually has
no annotation. Ordinary formal registration supplies `Gamma(b)=Value(v)`.
The selected treatment supplies `Seed(k,b,v,R,sigma)` on this registered
inferred endpoint. This is the selected instance, not arbitrary Name seeding.

H2. A source derivation from that registration to the actual callee use
retains `k,b,v,R,sigma` and its inherited packet. Each Name/capture step is
resolved to that binder/root by authentic typed correspondence. Each Result
step retains the returning value packet. Any refinement or transport used
already has an independent preservation certificate; merely having a proposed
refinement rule is insufficient.

H3. The owning Call constructor emits `SourceUpperUse(u,v,U,sigma)` at that
same still-inferred, seed-bearing source occurrence. Its complete obligations,
joint original assignment `xi=(nu,K,D)`, and designated `outEff(U)` occurrence
are retained. This source-stage fact is not a predicate on a solved type or a
claim that a particular wall-clock action ran first.

H4. No step in H2/H3 releases, substitutes away or reconstructs the seed's
original applicability. A transported coordinate has its certified original
correspondence; equality of solved values is not correspondence.

Write `d` for this constructor derivation, not a new solver/runtime carrier:

```text
Seed(k,b,v,R,sigma)
d: registration -> resolved seed-preserving Name/capture/Result
                   -> original Call upper on that inferred endpoint
----------------------------------------------------------- [conditional composition]
ProtectedVarAt(k,v,sigma,u)

ProtectedVarAt(k,v,sigma,u)  SourceUpperUse(u,v,U,sigma)
----------------------------------------------------------- [selected Dir-Protect]
NewProtection(k,u,outEff(U))
```

**Proof.** At registration H1 places the selected protection on the inferred
formal, with its original seed identity. Follow the finite constructor
derivation H2. A Name/capture step preserves its source root and packet; Result
does not replace the value endpoint. Any other admitted step has the stated
retention certificate. Thus the Call leaf H3 exposes that protected inferred
endpoint, establishing exactly protection *at this source exposure*, with
the original `k` and scope. This is S1's constructor composition with retention
made explicit. Applying Dir-Protect gives only `outEff(U)`. No argument
requires solving `Q`, type membership success, a provider lower mark or actual
Handler/Pure role equality. H4 prevents changing this argument into a join on
final component membership. QED, conditional on H1–H4.

H3 is a substantial source premise: it identifies the upper's source stage
with the retained protected inference occurrence. Without its owning source
derivation, the displayed proof cannot independently establish that fact.
Replacing H3 with a supplied `ProtectedVarAt` flag would remove the bridge
being investigated.

## Coverage factorization: the smallest remaining lemma

Fix an independently specified inventory `Req(C)` of required original upper
exposures in a component. This note does not define it by successful checking,
nor by the exposures for which the proof happens to succeed. Then require:

```text
ExposureCover(C):
for every u in Req(C), an owning source derivation provides
  (a) H1–H4 with their same original seed/root/scope, or
  (b) an independently justified ProtectedVarAt derivation for that u.
```

Under ExposureCover, finite induction over the inventoried derivations and
Dir-Protect establishes the required exposure facts and their designated
upper output marks. This proves universal coverage *conditional on the
inventory and coverage lemma*, not a new aggregation rule. Distinct seeds and
uppers remain distinct; shared profile slots or solved coordinates do not
merge their witnesses. Existing lower/provider marks are copied without a
new backflow producer.

For the selected direct/captured single Call, S1 supplies case (a) under its
published constructor premises. For arbitrary recursive, late-introduced,
generalized or mixed-use exposures, the current documents do not supply
ExposureCover. Their conservation results consume origin-bearing certificates;
they do not construct all of them. The precise blocker is the owning source
producer of applicability at each inventory entry, including which
introductions correspond there. Expanding finite saturation of supplied facts
cannot resolve it.

## Minimal failure witness and shortcut mutations

Consider a finite fact fragment with one seed and one upper:

```text
Seed(k,b,v,R,sigma)
SourceUpperUse(u,v,U,sigma)
[no source derivation connecting this seed introduction to exposure u]
```

All endpoint/root/scope labels may match. The shortcut "same component/root
has a seed and an upper, therefore ProtectedVarAt" derives a fact that the
selected Dir-Protect rule cannot derive: it has no `ProtectedVarAt` producer
in this fragment. One seed and one upper are minimal for this attempted join;
deleting either eliminates the shortcut's trigger. This is a rule-relative
non-derivability witness, not a claim that a particular recursive source
program must be unprotected or rejected. A complete source producer could
later certify this pair. That would supply the missing premise, not validate
the shortcut from the present fragment alone.

Named mutations expose the same boundary:

- Replacing original binder absence with Name-local absence falsely seeds a
  known external Name or an actually annotated formal.
- Quotienting an upper and provider lower by their equal solved effect value
  loses the selected no-backflow distinction, even with one seed.
- Recursively marking all result effect positions exceeds Dir-Protect's
  single designated conclusion; a latent exposure needs its own derivation.
- Turning `[io]` permission or NonHandlerFormal refinement into either a
  fresh seed or protection release adds an unsupported constructor.

The annotated-formal witness was established in the input inversion note;
it is not repeated as a new attack here. Permission removes neither H1's
annotation-presence test nor the need for an independent annotated seed origin.

## Independence, omissions, resources and freeze

No executable oracle, experiment, seeds/ranges or mutation runs were used.
The proof shares the source constructors' retention and exposure premises;
it cannot independently validate those premises or their exhaustiveness.
Coverage is not finite characterization of all source programs. Unverified:
Req(C)'s exhaustive formation, ExposureCover outside the selected S1 envelope,
recursive/late seed rules, multi-use conflicts, refinement existence and
principal solutions, annotation contribution/removal, actual event/profile
protection, production conformance and solver implementation.

Failure conditions are changed dependency bytes, unauthentic source/capture
correspondence, loss of seed-stage applicability, an uncertified refinement,
mixed original assignments or a claimed inventory exceeding the certified
constructor envelope. No new rejection behavior follows from these failures.

Checks: required policy reads, governing-section reads, read-only HEAD/ref,
dependency SHA-256 snapshot, creation guard, and artifact readback. Initial
aggregate source capture was truncated; decisive proposal §§3–5 and C5 and
joint-judgment §§3–7 were read separately. No exhaustive repository search,
tests/builds/probes, Git mutation, children or shared-record edits. Local
commands were sequential, light, one process at a time. Numeric CPU/RSS/wall
usage was not measured; the approximate 60-second target was exceeded to
finish the governing reads and conditional artifact. All writes stop at
submission; independent review remains pending.

Freeze recheck found the proposal changed from `a6cfbb30...` to
`e6e333cdffc532310f58ad1fd56091b3e58185fb89802e9ac1814985182487dd`.
The exact read-only diff against the pinned baseline changes only §8's review
and omission declarations; governing §§3–5 and C5 are unchanged. Thus the
conditional premises above still use the pinned sections. The other four
dependency hashes remained unchanged. The read current branch ref was
`8bee83a975a5a993aa57cd6db3752df222a23d8e`; it is not this artifact's baseline.

| Dependency | SHA-256 at producer snapshot |
| --- | --- |
| inferred-function-call-views | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| directional-inferred-effect-protection-addendum | `6b1779933499b360627fa5852c292ce97bda9830d146863b1b7ef440706054a7` |
| production-call-elaboration-proposal | `a6cfbb30ce7ceaaafc0aac70eb326b3b6efaf410e89f5cd3cfe398cd6d0b2d44` |
| annotated-formal-seed-inversion | `110cf37e2c95caad4959429cf83e4da4e7ee1828abb1a2a071a39eb2e213605f` |
| directional-joint-source-judgment | `fc459dfac03693f426dea575585a0d20d7a075f8c7ac27be9fd2e67a150466c1` |

Recommended next action: have the owning source-formation lane supply a
syntax-directed exposure inventory and origin-bearing derivations for its
entries; return genuine applicability-policy gaps to the primary. An
equivalent saturation probe would leave ExposureCover untouched.

## Commit packet

- Exact leased path: `notes/progress/2026-10-09-c5-protection-exposure-derivation.md`.
- Baseline SHA: `4e5e7fc7cf60cd1731f7d528754e86dcc70f9b2c`.
  Dependency hashes changed by this worker: none. Observed proposal change:
  `a6cfbb30...` to `e6e333cd...`, review declarations only, checked above.
- Review status: frozen unreviewed conditional research derivation; no
  independent review, C5 closure or production authority claimed.
- Checks already run: policy/source reads, read-only ref, dependency hashes,
  creation guard and focused readback; zero tests/builds/probes.
- Proposed commit message: `research: factor C5 exposure coverage from seed retention`.
- Shared-record deltas left to primary/curator: distinguish selected S1
  exposure composition from the remaining ExposureCover producer; retain C5
  open, annotation seed inversion boundaries, role/principality and recursive
  applicability gaps. No task/index/authority/question-board changes made.
