# Exact captured-step component: conditional original-profile construction

Date: 2026-10-06
Baseline: `b0dd026bb9438b7dfb13c68a474a49145eb97555`
Status: unreviewed research derivation; frozen on submission
Claim class: conditional profile normal form and receiving-view preservation;
bounded source-constructor audit
Scope: P after the reviewed initial source-call construction, for
`my apply f = { my step x = f x; step }` only
Authority / implementation permission: none
Exclusive output: this note

## 1. Objective, dependencies and retained facts

The objective is to construct the complete original applicable-position and
contribution inventory at the generated Call root, and interpret its
protected Handler seed and `NonHandlerFormal` refinement on that same root.
This lane uses source-constructor factorization and relational-image algebra.
It performs neither an admission construction nor a counterexample search.

The independently reviewed input is
[source-call construction](2026-10-06-source-call-generation-construction.md)
§§3–5/7. It already generates `R_f`, the dependent complete Function variable
`F_c`, `beta=(d_f,R_f)`, `p_0=(beta,call.effect)` and
`ElimOrigin(c,u_f,d_f,R_f,p_0,p_out(c))`. Its initial seed is protected with no
annotation-removal grant. Its singleton role factor is conservative at the
static-record projection; it does not establish the complete profile.

The exact governing sources are:

- [Inferred call views](../design/2026-10-05-inferred-function-call-views.md)
  §§2–5 and approved `function-call-view-formation/q1 a2`. Annotation absence
  selects full protection at applicable positions; ordinary-value evidence
  refines this inferred relationship, preserving actual callable role/entry.
- [Nested source interpretation](../design/2026-10-06-nested-block-function-source-realization-addendum.md)
  §§1–3. The block returns the captured `step` closure without invoking it.
- [Callback delivery](../design/2026-10-03-callback-context-delivery.md)
  §§2–4. B remains normative and expects an already supplied profile; existing
  values keep their actual role and entry.
- [Typed boundary](../design/2026-10-02-typed-boundary-realization-draft.md)
  §6. Source introductions supply profiles; indexed typed packet images
  transport them; receipt and pre-dispatch observation realize applicability.
- [Source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
  §§2–3.5/10. Constructor images use independently interpreted whole-tuple
  primitives; C-realization assumes its source conformance certificate.
- [Minimal-clause localization](2026-10-06-main-source-generation-minimal-clause.md)
  §§6–7, with its earlier stop corrected by the reviewed input above.
- [Typed core](../design/2026-10-02-typed-computation-core-elaboration.md)
  §6 structural table and §8 routing-preservation theorem, used as conditional
  constructor and preservation lemmas, not additional source authority.

Everything is at one original `xi=(nu,K,D)` and binder tree `sigma`.
Dependent paths remain symbolic in `F_c`; a satisfying Function descriptor is
not needed to emit them. For their semantic interpretation, a well-formed
joint realization is required. The claims below quantify over such
realizations without selecting one during generation or selecting witnesses
independently at different ports. Neither `Q` nor its success is a premise.

## 2. What the source constructors determine after the initial slice

Let `P_F(xi)` be the tagged typed-path domain of a well-formed realization of
`F_c`, and `Eff(P_F(xi))` its effect-observation positions. This is the
dependent signature-path domain used by typed-boundary §6, not the set of
effects in an outward row. Distinct occurrences ending in an equal type
variable remain distinct paths. Recursive signatures keep occurrence tags;
no infinite unfolding or exhaustive path enumeration is asserted here.

The selected skeleton gives the following complete *constructor inventory*
for this component:

| Source constructor | What can be constructed or transported | What it does not establish |
| --- | --- | --- |
| `Name(f)` | Shared outer formal root; identity path schema for a supplied packet | Original packet, receipt or profile introduction |
| `Name(x)` / `Result` | Actual returning Name argument root `J_x`; `Comp(empty,A_x)` interface | That every carrier with this printed interface is that Name image |
| `Call(f,x)` | `F_c`, `beta`, `p_0`, complete-invocation elimination origin and initial policy | Complete source applicability of other signature positions |
| Local `Lambda(x,...)` | Inert closure and lexical capture of the same `d_f` | Public exposure of private capture fields or typed capture attachment |
| Sequential `Bind(step,...)` | Rebind the returned closure under the same joint witness | A call or force of the closure |
| `Name(step)` / final `Result` | Return the closure view by its typed value correspondence | Execution of its latent body or creation of latent protection by execution |
| Outer `Lambda(f,...)` | Inert outer closure and original scope structure | Identification of independent actual providers across separate invocations |

In particular, there is no second source Call in this exact component and no
explicit annotation occurrence. This excludes a second *explicit Call seed*
or explicit annotation grant from this syntax inventory. It does not exclude
a source-applicable latent position in the completed inferred contract.
The constructor inventory and the profile inventory have different domains.

Result transport is structurally decisive but narrower than P: a signature
path `result.latent.effect` can project to the returned view's `latent.effect`;
`call.effect` cannot do so without an independently justified correspondence.
Hence `p_0` contributes no such latent incidence by the ordinary result map.
This conclusion holds even if the two paths end at an equal effect family.
It also does not remove a profile already present on the actual returned
value or independently introduced at a matching callee-result position.

## 3. A source-tagged normal form, with its unknown operand exposed

For any well-formed realization, write an original source-owned introduction
relation as

```text
H_C(p,a;xi),   p in Eff(P_F(xi)).
```

Here `a` is an original contribution witness, retaining its source occurrence,
provider/operation or latent origin, and dependencies at their original
scope. It is not just an effect-family head. Its complete witness domain and
association with positions are part of the missing source constructor.
`H_C` is notation for that missing output, not its definition or an opaque
certificate asserted to exist. Giving it all well-formed decorated witnesses
would yield a decorated envelope; equality with original source contributions
would still need proof.

Define `App_C(p;xi)` to mean that the source contract exposes/protects `p`.
Keep this static applicability predicate separate from `H_C`: a protected
position can currently have no event or no realized contribution witness.
For example, an empty realized effect support does not delete `p_0`.
Consequently `Slots(beta)` cannot be defined merely as the projection of
currently realized events from `H_C`.

The reviewed initial construction fixes:

```text
App_C(p_0;xi) = true
Policy_C(p_0) = Protected
AnnotationGrant_C(p_0) = None.
```

It does not provide an extensional listing of every original contribution
of every possible provider. At `p_0`, full protection has a uniform
interpretation: every event with the appropriate same-view typed path,
receipt and live incidence is protected. That interpretation ranges over the
complete invocation, including its entry and consumer; it is not restricted
to the callee-body row or to events escaping an internal handler.

Suppose the following independent source premises have been produced:

**H1 (complete applicability).** `App_C(p;xi)` is decided or symbolically
presented by an independently interpreted source-to-signature rule, including
every exposed applicable position and excluding every inapplicable one.
It includes `p_0` and preserves original occurrence/scope identities.

**H2 (complete contribution incidence).** `H_C(p,a;xi)` relates exactly the
original contributions governed at each applicable position, preserving the
whole `xi`. Its primitive/provider witness interpretation is independent of
the pending comparison. It distinguishes this contract's introduction from
inherited provider/result packets. H2 is not implied by H1.

Then, for this unannotated source, the static profile is constructed by

```text
Slots_original(beta;xi) = {p | App_C(p;xi)}
Gamma_C(p;xi) = Protected,                 if App_C(p;xi)
Gamma_C(p;xi) has no incidence,            otherwise
AnnotationGrant_C(p;xi) = None,            for every p
Governed_C = H_C.
```

This is a **conditional construction**, with H1/H2 exposed. The approved
no-annotation decision fixes the policy once applicability is known; no
effect family, actual provider role, outward support or successful query is
inspected to choose it. In particular, the absence of annotation never grants
permission for removal at another position.

Separate introduced and inherited sources before transport. Using indexed
source tags, any subsequent supplied typed step has normal form

```text
Packet_out = Image_C(M_C,Packet_C)
             union_tagged Image_provider(M_provider,Packet_provider)
             union_tagged Image_result(M_result,Packet_result) ...
```

The ellipsis denotes additional actual typed inputs of that supplied step,
not invented inputs of this source. Each image acts on its own domain.
`chi` and `D` move together; `K` retains original predicate identities under
the same `nu`; inherited `L` and receiver references are retained. No alias
union by underlying pointer equality is permitted. A source-owned profile
at `p_0` therefore cannot erase an independently inherited latent profile,
and a transported inherited profile cannot establish `App_C` at its target.

**Derivation.** Apply typed-boundary §6's indexed relational image to each
tagged input. Induct on the finite constructor route. At a Name/rebind use
the supplied identity correspondence. At a result use its matching result
projection. At a capture retain its separately supplied typed capture map.
Composition and distribution over tagged union give the displayed normal
form. A Call introduction is the distinct source `C`, with policy above.
Every output witness has its original tagged input witness. Conversely every
input witness in the map domain has its image. This proves exact transport
given H1/H2 and the typed maps; it does not introduce H1/H2 or prove capture
attachment.

## 4. Same-root receiving interpretation: the exact preservation premise

The internal seed and refined records refer to the same `R_f`. Define an
administrative record normalization `N` which replaces only the internal
`ProtectedHandlerSeed` label by its already selected `NonHandlerFormal`
record, retains the source policy records, and fixes actual provider
role/entry. This is a candidate representation operation, not an assertion
that an operational refinement rule has already been generated.

For a supplied completed original profile and execution certificate, assume:

**H3 (receiving correspondence).** Seed and refined realizations are related
on the same admitted complete invocation histories. The relation preserves
source position/contribution tags, all matching `Flow`, `Receive` and
pre-dispatch `Observe` witnesses, original receiver/handler identities and
their activity at each actual search configuration. It preserves whole
argument, actual entry, body, consumer, current state and original raw
resumptions. It acts once on all `xi` coordinates. It does not identify an
internal seed label with an actual Handler introduction or allocate a new
receiver merely because a role label changed.

Under H1–H3, the normalized receiving view has the same original profile
interpretation and candidate-specific protection/grant behavior.

**Proof.** A `Path(q,u,b,p)` witness is exactly a source profile position,
matching flow chain, executing-view observation and matching receipt.
H1/H2 preserve its original position and contribution witness. H3 maps each
remaining witness bijectively; reverse the map for the converse. Thus `Path`
agrees. H3 retains the exact activity tests, hence `Inc_C` agrees. The
introduced unannotated profile has no explicit grant in either realization;
inherited profiles and their local annotations remain identical, so their
grants also agree. Existentially quantify over the same witnessed positions
to obtain equal `Protected` and `Grant`. With the same active handlers and
coverage tests, `Visible` agrees. Source execution and ordered selection
therefore agree along the related complete finite histories. The proof does
not depend on outward effect support or actual callable role being Handler.
It is the relational-image and routing-preservation argument on the same
original receiving graph.

For the isolated no-grant source contribution, the exact local preservation
test is equality of its live witness predicate:

```text
W_stage(q,h,C) = exists p.
  App_C(p) & Path_stage(q,owner(h),b,p)
  & Active(h,C) & Active(owner(h),C) & Active(b.receiver,C).

forall original q,h,C. W_seed(q,h,C) iff W_refined(q,h,C).
```

This equality is necessary and sufficient for preservation of *this
contribution's candidate protection*. It is not claimed necessary for every
whole-program observation: an unrelated inherited grant or lack of a
covering handler can mask a difference. H3 is a constructive sufficient
witness correspondence for the displayed equality, not a theorem derived
solely from equality of `R_f`.

Erasing only an internal label commutes with an already supplied profile
image, because neither the image nor `Path`/activity consults that label.
Deleting `p_0`, clearing its policy, or changing its receiver schema is a
different operation. Same-root identity alone does not justify any of them.
Likewise retaining the seed record is not a proof that the generated
operational refinement satisfies H3. The eventual source rule must establish
that implication at every original fiber.

## 5. Exact stop and discrimination between unsupported shortcuts

The source/typed constructor references suffice for the initial port, tagged
transport normal form, and the receiving preservation theorem *under* H3.
They do not supply these residual source outputs:

1. For each `p != p_0`, whether `App_C(p;xi)` holds because of this source
   contract, rather than because a compatible descriptor has that path.
2. At every applicable position, the complete original contribution-witness
   domain and relation `H_C(p,a;xi)`, including symbolic higher-order provider
   contributions. The initial origin identifies a route, not this catalog.
3. A source-derived seed/refinement realization correspondence establishing
   H3, rather than an administrative normalization on a graph supplied by
   assumption. Actual receipt/capture attachment remains a later independent
   premise; this lane supplies no such instance.

These are minimal residual subpredicates of the displayed factorization,
not a claim that no other construction can prove P. H1 alone leaves H2
unknown; H1/H2 alone leave actual refinement preservation unknown. Packaging
all three as `OriginalProfileCertificate` would not prove any of them.

The following formal mutations discriminate the proof premises, without
claiming Authority-consistent source counterexamples:

- Set `App_C={p_0}` without deriving source exclusivity. The initial-port
  construction remains true, but H1 completeness is unproved.
- Add every latent effect path solely from descriptor reachability. Typed
  paths exist, but no source applicability witness is supplied; H1 soundness
  is unproved. Result transport still does not map `p_0` to those paths.
- Project slots from current outward requests. A protected position with
  no outward event disappears; this changes static policy and fails the
  all-pre-dispatch witness requirement.
- Retain `R_f` but delete the protected incidence during role refinement.
  Record identity remains true; the displayed `W` equality need not hold.
- Preserve profile paths but change receiver identities or use separate
  port valuations. H3's activity/receipt or whole-`xi` premise fails.

No execution of these mutations was performed. A second latent slot, a
changed receiver or a convenient event graph is not an independently typed
source witness. This note establishes neither incompatible complete language
meanings nor a new user decision.

## 6. Evidence, omissions and recommended next action

Commands: bounded `cat`, `sed`, `rg`, `wc`; read-only `git rev-parse`,
`git branch`, `git status`, `git ls-tree`, `git hash-object`; dependency
hashing and a Python standard-library relative-link inventory. No test,
build, Oracle execution, executable checker, parallel process wave or Git
mutation. Mathematical evidence is the constructor audit, source-tagged
relational-image induction and conditional witness bijection above.

Coverage: one exact approved source component; every constructor in its
selected skeleton; symbolic typed paths at each well-formed joint fiber.
There are no seeds, numeric ranges or sampled cases. Complete source
applicability, original contribution primitives and H3 are unverified.
Neither all-view source inversion, independently typed admission A, source
principality, finite effective presentation nor production Option A/2
containment is proved. No interpretation of an unknown signature is inferred
from the finite constructor count.

Oracle independence: no Oracle is used. The algebra is independent of Oracle
algorithms, but shares the supplied typed-boundary introduction/transport and
source-constructor assumptions. It proves consequences of those assumptions,
not that source syntax establishes them. The producer's own derivation and
reread are not independent review.

Resource usage: zero build/test/probe processes; only short bounded reading,
hashing and note-write commands. CPU time, peak RSS and exact wall time were
not measured. No numerical process/RAM/wall-time allowance was supplied;
the explicit no-build/no-test/no-Oracle restrictions were respected.

Recommended next action: supply one source constructor for the original
applicability/contribution relation at `F_c`, and its refinement witness map,
then check H1–H3 by source-rule inversion. If the proposed rule decides
positions or receiver behavior beyond existing Authority, return that exact
decision to the primary before adoption. Enlarging a toy event graph would
leave these same source premises untouched.

## Commit packet

- Exact leased path:
  `notes/progress/2026-10-06-profile-P-exact-candidate-construction.md`.
- Baseline SHA: `b0dd026bb9438b7dfb13c68a474a49145eb97555`.
- Dependency blobs at baseline:
  `source-call-generation-construction.md` = `2e9879c162d93f6560889f4738bcaab4ac72be6e`;
  inferred-call-view = `9493abd55e61dbc59de31f319c2ff9670204069a`;
  approved q1/a2 = `0f74be2cb4d9a95707081e5cd9401e2ab53b14b7`;
  callback delivery = `eeed5c2b5dd38404a4c774cda486864a63992fad`;
  typed boundary = `5e0499e43b3dbf04de0bcdb6c0fa5994224d8a87`;
  source contracts = `1c2b1a579a9cc7a51d98a4fda755838decb96d07`;
  minimal clause = `457c924b807540685b24b656425c99e9dbe4fdee`;
  nested source addendum = `704048bc866d1638ef8811e2364a25e31c0ebb96`;
  typed core = `d0948191bbc2d1eb10a7e6e360dc8852a185db1d`.
- Changed dependency hashes: none observed; primary recheck required before
  integration. Unrelated concurrent shadow edits are outside these inputs.
- Review status: unreviewed research-only conditional derivation; frozen
  before submission. No independent review or gate closure claimed.
- Checks already run: governing-section inspection; all nine dependency blobs
  match the pinned baseline; eight relative links resolve;
  `git diff --no-index --check -- /dev/null <leased-note>` emits no whitespace
  diagnostic (exit 1 denotes the new-file difference). No compiler
  verification was run or required by this lease.
- Proposed commit message: `research: factor exact-candidate profile construction and refinement premises`.
- Shared-record deltas intentionally left for primary/curator: link this
  conditional normal form; retain P open at H1/H2 and source-derived H3;
  leave admission A, actual capture/receipt and production gates unchanged.
  No task, theory map, authority, index or question-board file was edited.
