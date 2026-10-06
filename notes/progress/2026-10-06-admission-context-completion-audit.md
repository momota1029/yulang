# Initial admission: context quantifiers and semantic import cut

Date: 2026-10-06
Status: independently compiler/spec-reviewed conditional construction and source/authority audit; see [P/A review](2026-10-06-source-generation-pa-review.md); no semantic selection
Baseline: `763ad96d4576ee6e2672c0cc35125e79c89fe955`
Method: two attacks — quantifier inversion and open-hole substitution discriminator
Write lease: this file only; no compiler, authority, question-board or Git mutation

## 1. Result

The selected initial domain is **all independently typed compatible source
contexts, under all jointly admissible semantic environments at one original
fiber**. It is neither all arbitrary machine worlds nor contexts reachable
from the current closed program. This quantifier direction is already
selected; no choice between these universes remains.

The audited sources do not give its exhaustive environment/import validity
rules. However, that absence does **not** establish semantic
underdetermination. This audit found no pair of fully defined, different local
primitives that both satisfy the selected clauses and give different source
acceptance or observations. Source-only imports and arbitrary graph worlds
are not such a certified pair: the former has no proof that its source
witnesses recover the selected semantic free-variable universe, while the
latter has no proof that all its states are source-admissible.

Nor has equality with a denotation of *all universally safe contexts* been
proved. Independent source typing is a judgment over open source constructors
and hypothetical holes. Universal semantic safety of hypothetical fillings
is a possible soundness characterization, but identifying that characterization
with the selected source-typing judgment additionally requires completeness.
Universal safety of the actual filling being compared is the wrong criterion:
it removes the violating challenge and can make comparison vacuous.

There is a positive source-generation conclusion: **given an independently
interpreted original world/import basis and original P, A is the canonical
collecting union of open source constraints and same-world receipt images**.
The source need not manufacture or decide runtime imports, nor prove its
emitted constraints satisfiable before generating this relation. In the
supplied immutable derivation core this is a constructor induction. That
conclusion must be separated from an unconditional construction of the full
selected semantic world universe, which the audited documents explicitly
leave open.

The smallest isolated **semantic leaf** in the all-context route is validity
of an ordinary semantic import at its original declared interface and current
joint source world, together with the source transitions that preserve that
validity. This is more specific than an unexplained `TypedContext` premise or
the entire `DescMem` relation. Hole-dependent closures in the immutable core
can instead be justified by open source constructors and the hypothetical
hole rule. General imported reference/alias worlds need their own source
bridge; a static capture tag is insufficient. P, full raw-source open typing,
and production-only membership remain distinct obligations.

## 2. Source clause crosswalk

| Source | Selected or supplied clause | Audit consequence |
| --- | --- | --- |
| `questions/2026-10-05-production-function-inlet-context-domain/approved-answer.md`, decisions 1–5 | Every independently typed compatible punctured caller context at fixed original `(nu,K,D)`; callable and whole-carrier holes; independently valid other environment values; future reuse; exhaustive noncircular rules remain a proof/design task | Settles breadth and independence, not the primitive validity judgment |
| `questions/2026-10-05-production-function-denotation/approved-answer.md`, decisions 1–5 | Original `Rel_C` fiber, independently interpreted endpoint/role/path/origin/continuation/scope/authority/dependency constraints; admission separate from membership; no completed rules approved | Supplies the semantic basis; does not identify independent typing with arbitrary runtime safety |
| `questions/2026-10-05-production-function-bound-membership/approved-answer.md`, decisions 1–4 | Option 2 permits licensed conservative observations without mandatory source-constructor witnesses; four port types alone do not license them | A source-witness restriction on all production observations is invalid; Option 2 does not license arbitrary imports/worlds |
| `notes/design/2026-10-05-inferred-function-call-views.md`, §§2, 5 | Original source component constructs slot/path/owner/profile and joint witnesses; Q does not create them; exact judgments remain open | An existential successful decoration cannot supply original context evidence |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md`, §§2.1–2.2 | Primitive and descriptor relations are independently supplied; active membership/admission incidence is an additional hypothesis | Renaming a root predicate is not its interpretation |
| Same, §§3.1, 3.3 | Decorated immutable source base excludes opaque uncertified imports; initial, response, same raw handle, returned-provider future use | Exact bounded reference envelope and positive history extension do not cover all selected semantic imports |
| Same, §3.7 | Whole-tuple abstraction under a complete guard; `W,Z` and concrete membership grammar unselected | Paired abstraction cannot fill the environment leaf by itself |
| `notes/design/2026-10-01-coupled-effect-interface-core-draft.md`, “Candidate Function contract” and “call-configuration domain” | Every typed evaluation context under every semantic environment for its other free variables; two holes; context/Env judgment explicitly open | Underlying source of the broad quantifier, with a disclosed formalization gap |
| `notes/design/2026-10-03-concrete-compatibility-boundary.md`, §8 contextual-domain, rigid-hole, open-graph, indexed and source-state follow-ups | Whole-carrier holes; hypothetical assumptions do not assert actual filling membership; semantic imports distinguished from hole-dependent open values; closed-source reachability and arbitrary graph worlds insufficient | Provides the discriminator and exact source-state boundary below |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md`, §§2–4, 6, 9 | Finite typed-core constructors; Name relative to given Gamma; inert whole-argument introduction; receipt before actual entry Force; realization from supplied derivation | Constructs execution/open immutable values relative to supplied declarations; does not validate every free-variable import |
| `notes/design/2026-10-04-source-generated-callback-structural-theorems.md`, §3; `notes/design/2026-10-04-source-indexed-callback-realization.md`, §4 | Hypothetical callable hole; surrounding source nodes checked locally; finite reference admission independent of Q | Reference admission is constructive within its premises, not an exact all-world production interpretation |
| `notes/design/2026-10-02-source-interface-adequacy-theorem.md`, §§2–4 | Every admissible finite future interaction and same-fiber execution/interface coverage; admissible worlds taken as premises | Universal future behavior does not construct the initial admissible world |

## 3. Exact quantifier shape, conditional on primitive completion

Fix original imports `rho`, binder map `sigma`, profile P and
`xi=(nu,K,D)`. Write `Hf:F` and `Ha:I` for proof-only callable and
whole-carrier assumptions. They are not environment bindings asserting
membership of the actual filling at F. Let:

```text
OpenDer(P,Gamma; Hf:F,Ha:I |- C:J ; sigma,xi)
World(P,rho,Gamma,eta,W; Hf,Ha,sigma,xi)
Joint(P,C,eta,W,f,a; sigma,xi)
ReceiptExec(C[f,a],eta,W; sigma,xi,h)
```

name respectively an independent open derivation, an admissible semantic
environment/source world, the retained cross-root consistency, and source
projection to the designated receipt. These displayed predicates are an
**interface equation**, not claimed newly completed primitives. Then the
selected initial collecting domain has the shape

```text
Initial_F(f,a;rho,sigma,xi)
 = { h | exists P-compatible Gamma,C,J,d,eta,W.
       d : OpenDer(P,Gamma;Hf:F,Ha:I |- C:J;sigma,xi)
       and World(P,rho,Gamma,eta,W;Hf,Ha,sigma,xi)
       and Joint(P,C,eta,W,f,a;sigma,xi)
       and ReceiptExec(C[f,a],eta,W;sigma,xi,h) }.
```

The union ranges over **every** such derivation and **every** admissible
environment/world. The existential in the set comprehension witnesses one
specific history; it does not mean that a context with one convenient quiet
environment gets to ignore other admitted environments. A comparison then
quantifies universally over all histories collected by this union.

There are four different quantifier positions:

1. A complete open typing derivation may be existentially witnessed. This is
   ordinary proof existence; it is not inherently a shortcut.
2. Validity of a supplied ordinary provider must cover its declared complete
   behavior, including every admitted finite future interaction. It cannot
   be proved by finding one quiet execution.
3. Every valid environment/world contributes all its receipt histories to
   the collecting domain, including counterfactual clients and imports.
4. The final inclusion checks every such challenge at the same original
   assignment. Neither world nor port witnesses may be reselected per segment.

If a total independently interpreted OpenDer/World/Joint basis is supplied,
the equation equals the selected collecting domain by two elementary
inclusions: an equation witness is exactly an independently typed compatible
context/world and its designated source receipt; conversely every selected
context/world/receipt supplies those witnesses. This is a **conditional
definition correspondence**, not a constructive equality proof without those
primitives. Positive history induction then supplies finite extension, as
already established in source-call construction §6.

### 3.1 Emission before satisfiability: the positive A theorem

Ordinary independent imports may be leaves. The approval already quantifies
over their independent validity; it does not require the current source
component to construct every runtime provider. Likewise an existential
semantic variable is legitimate when its predicate already has an independent
interpretation. The issue is not the existence of such a variable.

For the supplied finite immutable source constructors, use an open generation
judgment with two hypothetical hole assumptions:

```text
Gamma; Hf:F,Ha:I |- C => J ; exists z. Phi_C
```

Here Phi_C is the joint same-scope conjunction/composition of the independently
interpreted local source constructor constraints; a syntactic derivation
skeleton need not already have a successful filling. Name reads the same
Gamma root or hypothetical hole. Closure/delay records those open captures.
Call uses its independent callee/whole-carrier/root/path constraints and
complete invocation image. Bind retains the shared result/state witness.
No rule reads the pending Function comparison's success.

Replace the `d:OpenDer` conjunct in the collecting equation by Phi_C and
existentially bind z once around the whole context/history. Constructively,
form the union over every finite context constructor tree and project its
same-world source receipt image. This emits A before solving Phi_C. It does
not select a separate world per port or per continuation segment.

**Conditional source-generation theorem.** If the supplied local constructor
relations are the exact interpretation of the original source typing and
transition rules at original P, and the independent semantic World/import
basis is supplied, this emitted A equals initial admission for that basis.
Proof: structural induction identifies satisfying Phi_C witnesses with open
local source derivations, retaining the same captures, roots, state and scope.
The forward receipt image then gives an admitted initial challenge. In the
reverse direction an original open derivation determines the same constructor
tree and one joint Phi_C witness; its original execution supplies the receipt
image witness. Union and projection preserve both inclusions. Hole-dependent
source closure construction never invokes closed target membership of the
actual filling. QED, within the supplied constructor envelope.

This is source A construction on an independently interpreted semantic basis,
not proof that the finite immutable envelope covers every raw Yulang State,
reference, pattern, adaptation or import context. Source-contracts §3.1
explicitly restricts its source base. The production observation grammar is
also separate: this theorem does not require all Option 2 observations to be
source-generated.

## 4. One source-core discriminator: hypothetical captures and whole carriers

This is a derivation-indexed ordinary-core example with independently supplied
role/entry/profile/path premises, not a raw Yulang inference or P proof. No
mutable-cell operation, new syntax, solver extreme or value-identity
observation is used.

Use `Unit`, an independently declared operation `ask : Unit -> Comp(Eask,Unit)`,
Value-entry actual callables, and pure carrier
`a0=Delay(Return Unit)`. Let `f0` return Unit; let `f1` execute the declaration's
designated `ask` computation and then return Unit. The imported declaration
`u : Unit -> Comp(Eask,Unit)` permits a quiet provider and an ask-emitting
provider. Both have explicit source-core realizations; they retain distinct
request behavior after the approved data-value erasure.

For checked hypothetical holes

```text
Hf : Unit -> Comp(Eempty,Unit)
Ha : Comp(Eempty,Unit)    [whole argument-code/carrier proof hole]
v  = lambda(Unit, source_call_with_holes(Hf,Ha))
```

`source_call_with_holes` abbreviates the ordinary Call derivation punctured
at its callee and its complete argument introduction, with Ha inserted
directly as the one whole inert carrier at invocation. It is not a new source
construct and does not reify or force an already supplied carrier again.
The open closure constructor records the retained hypothetical roots and
justifies v under those assumptions. A context can invoke v, reaching the
Hf receipt with the same inert Ha. Plug actual f1/a0 for execution only.
An ask request is exposed by f1's body after receipt and the one designated
argument Force. The open context was admissible independently; the request
can falsify the checked pure output obligation.

Requiring the *closed*, actual-filled v to satisfy the checked pure Function
contract **before admission** would discard this challenge because f1 emits
ask. That is a circular environment filter: it demands the proposition being
tested through a captured alias. Requiring all hypothetical valid fillings to
preserve v's declared interface is a different statement and is consistent
with the open derivation. The hypothetical hole assumption never proves
actual f1 checked membership.

Replace a0 by `aAsk=Delay(Execute_ask Unit)` at an independently licensed
argument profile. Construction emits no request; receiver receipt happens
first; Value entry exposes ask while forcing the whole carrier, even if the
body ignores its parameter. A diverging pure carrier likewise reaches receipt
but never reaches the body. This is why an evaluated-value hole, a return-only
test, or support alone is insufficient. These are the selected core equations,
not an interpretation of `never`.

| Proposed check/universe | What this discriminator establishes |
| --- | --- |
| One successful/quiet execution types the declared u contract | Invalid shortcut: the same declared envelope also permits the independently supplied ask provider; both environments must be considered |
| Universal behavior check on each ordinary import at its declaration | Appropriate necessary semantic obligation; the quiet and ask providers both satisfy the ask-allowing declaration |
| Universal checked-membership test on the actual closed v before admission | Circular: rejects the violating actual filling instead of testing its observation |
| Open derivation for v under hypothetical holes, then actual source execution | Correct separation in the supplied immutable core; exposes the violating request |
| Source-only import witnesses | Covers these two explicit providers, so this example proves **no** difference from the full semantic import universe |
| All original admissible semantic worlds | Selected universe; whether a further non-source-denotable world changes acceptance requires a real admissible provider/world witness |
| Arbitrary structurally shaped worlds | Not selected; source admissibility and original joint evidence remain required |

No fabricated third provider was added to force a source-only/all-world
difference. Establishing such a difference needs a semantic imported value or
state permitted by the original interface, absent from the source-only domain,
and a context that observes it. Neither the approved scope decision nor the
bounded examples supply that witness. Hence no incompatible interpretation
or concrete source acceptance pair is certified here.

## 5. Minimal semantic leaf and constructive boundary

The Name row is already source-constructive **relative to Gamma**. Its first
unexplained external leaf in the all-context route is this particular clause:

```text
INPUT:
  original free-variable declaration j:J at original scope;
  one supplied complete provider root r and its reachable shared roots;
  fixed rigid import identities rho and original xi;
  current source configuration W and original profile/typed incidence;
  no pending Q, inclusion hypothesis, or actual-checked hole membership.

OUTPUT:
  ImportValid(j:J,r,W;rho,xi) or invalid;
  if valid, the original typed root/path/authority/dependency certificate
  and admitted source successors at this retained import incidence.
```

The output must cover every finite declared provider development; certifying
one observed trace is insufficient. It must preserve the same world/identity
and assignment through source calls, requests, typed responses and raw
resumption. This is a single declaration-to-provider incidence, not a request
to choose all descriptor semantics again. For scalar literal/operation leaves
the inspected local rules already supply corresponding source relations.
For an ordinary imported Function/reference leaf the independent declared
validity and successor rules are not supplied by those constructors.
This is an **ambient semantic premise allowed by the selected domain**, not
an additional source-owned output demanded of the captured-step generator.
It blocks unconditional interpretation of all semantic worlds if that is the
claim; it does not block emitting canonical A over supplied imports with their
independently interpreted predicates.

Hole-dependent immutable closure/delay roots are a second **construction
mode**, rather than ordinary closed import validity: construct their open
derivation from Hf/Ha and preserve those original captures. They must not be
tested by closing them with actual f and asserting checked membership. A
general reference import that aliases such an open root requires its real
source read/update/re-entry bridge. Concrete-compatibility §8 explicitly
requires that bridge and rejects inventing primitive heap writes. No claim
is made that one static import boolean suffices for every State/reference
world.

For the finite decorated immutable source base with independently certified
leaf relations, original P and the local open source rules supplied, these
rules construct initial challenges and positive extensions by source
induction; §3.1 makes explicit that generation can precede satisfiability.
Their source-reference correspondence is already covered by
Theorem C/source-indexed realization. Extending that proof to the selected
semantic import universe requires the displayed leaf clause plus open source
substitution/transition closure; equality with all universally safe contexts
requires additional source-typing completeness. Option A/2 endpoint membership
and actual-to-checked containment remain separate after initial admission.

## 6. Freeze, checks and commit packet

- Exact leased output: this file only.
- Baseline: `763ad96d4576ee6e2672c0cc35125e79c89fe955`.
- Claim/review: unreviewed source/authority audit, conditional collecting A
  construction before satisfiability and a supplied-core open-hole discriminator. No closed
  all-world theorem, production conformance, new decision, or implementation
  authority.
- Checks: direct relevant-source inspection; dependency equality to the
  pinned baseline; SHA-256 manifest below; whitespace check. No executable
  model, compiler/Oracle build, broad test, or measurement was run.
- No Git mutation, redelegation, external file save, questions or shared-file
  edits. Unrelated worker outputs were observed and left untouched.
- Proposed commit message: `research: audit initial context quantifiers and semantic import leaf`.
- Shared-record deltas deferred to primary: distinguish an incomplete
  independently typed world formalization from demonstrated incompatible
  semantics; preserve selected all-context breadth; identify ordinary import
  validity as an allowed ambient premise and open-hole source construction
  separately. Do not report this ambient premise as a new source-owned
  output demanded from the captured-step component. Keep P, full
  source-world closure, production-only membership and principality open.

All thirteen direct semantic dependencies matched their pinned-baseline
contents on freeze. SHA-256:

| Dependency | SHA-256 |
| --- | --- |
| inlet-context-domain approved answer | `9b63603890cd522ec80ef81e6208c52acdb1f09ab0a847a9b51368a8f563acf3` |
| production-function-denotation approved answer | `7e7f3c717b16a70fc754c930a1654666c8b61a89a4861fca27b0ae3fa5f1890a` |
| production-function-bound-membership approved answer | `d9ddea04a44d2307cf587bc4ae9b2a1c50d062c4077306a5bf9ea9da00eca179` |
| inferred-function-call-views | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| source-contracts-and-common-allowance | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| coupled-effect-interface-core-draft | `9eca7e45d1f0927397763481b0280bf54182408bd3c562aa2f6e80454f57ba3d` |
| concrete-compatibility-boundary | `5b0b4321d8644f88a7a946aff31b6b3190d37a9076ac698fa91fdfeef1470f16` |
| typed-computation-core-elaboration | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| source-generated-callback-structural-theorems | `568bb4649ba278519f3ad01af2091dd1baaca42850cd19e3b5734b3c47c2eefe` |
| source-indexed-callback-realization | `76874a219ac86068027b1f08a5bc27a12d93a0169a52cebd896a6ff6f2c6b671` |
| source-interface-adequacy-theorem | `6b8f95cfc2380508d500c447c82b64fd2c26fb32248e6fb3244314cc02023660` |
| ordinary-computation-semantics-package | `ee3f5cf8185d516775b8915b0fda6dbb07390c3ecad7ac028eb5995581dff917` |
| source-call-generation-construction | `6bd7773326ccdd3101eaeb60a7e0f5d98a6c7a80b68467f6bf06a6466ffc4073` |
