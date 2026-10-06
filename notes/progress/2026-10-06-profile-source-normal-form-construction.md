# Exact captured-step source: profile introduction and transport normal form

Date: 2026-10-06
Baseline: `763ad96d4576ee6e2672c0cc35125e79c89fe955`
Status: frozen research construction; compiler-referee review completed, one minor coordinate-domain finding repaired and delta-closed
Claim classes: constructive least-generated source footprint; conditional
typed-profile provenance theorem; exact remaining converse obligation
Scope: `my apply f = { my step x = f x; step }` only
Semantic and implementation authority: none

## 1. Result

There is a constructive, syntax-directed **least-generated footprint** for
this source whose original `beta` positions are exactly `{p_0}`. This note
defines its introduction and contribution rules, computes the footprint for
every node of the exact source, and proves the transport normal form by
induction. It does not take a completed original profile as its input.
Inherited actual-provider and actual-result packets remain separate leaves
of the construction, with all of their own latent profiles retained.

The construction is a candidate completion, not a proof that its least
footprint equals the complete original source profile selected by Authority.
The converse needed for that equality reduces to one precise source
introduction judgment: every original applicable position at this inferred
formal's root must be an elimination-introduced position. Neither the typed
transport equations nor the finite source constructor inventory supplies
that converse. In particular, a single original boundary introduction can
have a multi-position signature profile; uniqueness of `beta` does not prove
uniqueness of its positions.

No existing constructor was found that forces a second **source-applicable**
position for this exact source. No Authority-consistent source counterexample
to the singleton profile is claimed. Thus the result neither closes P nor
establishes a new semantic decision for the user. It removes transport,
capture, returned-closure structure and endpoint substitution as possible
causes of a second *generated* original position, and isolates the one
remaining completeness implication at the original introduction.

## 2. Governing clauses and input

The [inferred-call-view contract](../design/2026-10-05-inferred-function-call-views.md)
§§1.1–5 fixes one shared source contract; annotation absence as the cause of
full protection; the protected Handler seed and ordinary-value
`NonHandlerFormal` refinement; stable source identity and scope; and
comparison-independent formation. Its §5(1) explicitly requires a judgment
constructing the complete original profile.

The [nested-block addendum](../design/2026-10-06-nested-block-function-source-realization-addendum.md)
§§1–4 selects exactly this core tree:

```text
L_apply = lambda(f,
  B = bind(step,
    R_step = result(L_step = lambda(x,
      c = call(R_f = result(N_f = name f),
               R_x = result(N_x = name x)))),
    R_return = result(N_step = name step)))
```

The final `step` name returns the local closure without calling it. The local
closure captures the same original outer `f`.

The [callback-context contract](../design/2026-10-03-callback-context-delivery.md)
§§2–4 distinguishes source introduction from an existing callable's typed
invocation view, retains the original slot/profile at use, and preserves the
actual callable's introduction and entry roles. Neither local lambda here is
an inline argument literal in a known callback slot. Charter
[§§13, 21, 24](../design/2026-09-29-scc-intrusion-redesign-charter.md) supplies
typed-path transport, ordinary Value entry, no recursive force from latent
shape, and Pure introduction for the two ordinary unannotated lambdas.

The conditional mathematical basis is the [typed core](../design/2026-10-02-typed-computation-core-elaboration.md)
§§6, 7, 9; [typed boundary](../design/2026-10-02-typed-boundary-realization-draft.md)
§§4, 6; and [source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
§§2–3. These supply source-tagged symbolic skeletons, representation-preserving
checks, complete invocation and the packet-image equations. They do not
themselves become new source authority.

The reviewed [initial Call construction](2026-10-06-source-call-generation-construction.md)
§§3–7 is used unchanged:

```text
u_f -> d_f                    u_x -> d_x
Gamma(d_f) = Value(A_f)        Gamma(d_x) = Value(A_x)
R_f = shared inferred-contract root at (C,d_f,A_f,sigma)
F_c = one dependent complete Function variable at R_f
beta = (d_f,R_f)              p_0 = (beta,call.effect)
ElimOrigin(c,u_f,d_f,R_f,p_0,p_out(c))
InitialSeedSlots(beta) = {p_0}
Role_0(R_f) = (ProtectedHandlerSeed,NonHandlerFormal)
```

`F_c` is introduced before solving. Its arbitrary dependent result may later
have latent Function, Thunk, recursive or structural paths. All definitions
below use one original `xi=(nu,K,D)` and one coherent scope/renaming action.
No successful Q, actual receipt, executing boundary or packet attachment is
fabricated by this input.

## 3. An explicit source-footprint and contribution constructor

### 3.1 Domain and provenance

An **original address** is `(beta,s)` in the original dependent signature of
`F_c`. A **view address** is `(view,t)` in a particular typed occurrence.
They are different domains. Transport can relocate one original address to
many view addresses; that does not add an original signature position.

Use two kinds of provenance leaves:

```text
Generated(c,beta,p_0,FullProtection,NoGrant)
Inherited(i,packet_i,original_source_witness_i)
```

`i` identifies an actual formal/provider/result input. `Inherited` retains the
entire supplied packet `(v,t,chi,K,D,L)`, including arbitrary latent profile
positions. It asserts no fresh source introduction and no actual receipt.
Inherited source witnesses need not have different `beta` names: a packet
may retain a view from another use or activation of the same static template.
The distinction is provenance of introduction, not an invented disjoint
namespace or deletion of coincident labels.

Let `G_C(beta)` be the original positions of **Generated** leaves emitted by
the source construction, independent of all inherited leaves. It is not the
support of `chi` at a runtime view and is not initially identified with
`Slots_original(beta)`.

### 3.2 Introduction and profile rule

The candidate rule is directly over the generated source Call records:

```text
resolved c = Apply(u_f,u_x); u_f -> d_f; u_x -> d_x
Gamma(d_f)=Value(A_f); Gamma(d_x)=Value(A_x)
R_f,F_c,beta,p_0,ElimOrigin generated by Gen-Call-0 at sigma
NoAnnotation(d_f); Role_0 refers to that same R_f
---------------------------------------------------------------- Foot-Call
G_c(beta) = {p_0}
Gamma_gen(beta,p_0) = (Protected=true, ConcreteRemovalGrant=false)
OrigContribution_gen(c,d_f,R_f,p_0,p_out(c))
```

The last record has an interpreted meaning, not only a new certificate name:
this is the source Function elimination whose *complete invocation*
observation position corresponds to `p_0`. For any later typed realization,
an event contributes through this record exactly when its pre-dispatch
`Observe` witness is at `p_out(c)` in this executing complete invocation and
the original source/address correspondence realizes `ElimOrigin`. Entry,
body and designated result consumer observations are included; outward
residual support is not the test. Static generation itself creates no event,
`Observe`, `Receive`, dynamic boundary or `Inc_C`.

Protection is the constant source policy at this applicable generated
position. No effect family is selected for removal. The rule can be emitted
even when the subsequent constraints have no solution. It imposes neither a
particular latent result shape nor emptiness of `E_c`.

For every other node, the generated original inventory is the union of its
children's generated inventories. At a bound reference, use its registered
root rather than reintroducing the root's leaves. For the actual formal and
result interfaces, retain their inherited packets separately. Define
`Gamma_gen` by the same union, keyed by the original introduction witness;
duplicate routes keep one original entry and several transport witnesses.

This is a total source-to-footprint rule for the displayed source tree. It
computes its own profile rather than asking for `P` as a premise. Calling it
the **least-generated** profile states its proof status: its closure is
defined by the positively displayed introduction recipe, and equality with
the full original profile requires the converse in §6.

### 3.3 Typed transport recipes

For each independently typed source correspondence `M_i`, transport a packet
by the existing indexed image:

```text
chi_out = union_i M_i*chi_i
D_out   = union_i M_i*D_i
K_out   = same joint predicate ledger
L_out   = inherited origins/runtime identities
```

Keep each input index and original introduction witness through the union.
These recipes are generated structurally; their actual packet attachment,
ownership and liveness remain realization premises. Unknown latent paths use
the symbolic dependent domain `Paths(A)`. They are not speculatively
enumerated from a chosen solved shape.

Identity applies to typed Name/binding/capture edges. Returning an actual
result removes its matching result prefix. A result view retains both the
actual returned packet and the callee-signature result projection, as separate
indexed sources. The latter requires actual original information at the
matching result position; it is not filled by the `p_0` Call seed. Private
captured `f` is an environment view, not an exposed field of `step`'s public
signature.

## 4. Exhaustive induction for the exact source footprint

The induction domain is the finite selected source tree above, with binder
references resolved to original roots. The theorem is:

```text
G_C(beta) = {p_0},
and every Generated beta leaf in any recipe is Generated(c,beta,p_0,...).
```

This theorem concerns the recipe introduced in §3. It is unconditional on
constraint satisfiability and conditional on no additional source-introduction
recipe being silently appended to that construction.

| Constructor in this source | Local introduction/transport | Generated original beta footprint |
| --- | --- | --- |
| `N_f` | Resolve the same `d_f`; reference its provider and inherited packet; identity-address schema on `Paths(A_f)` | Empty |
| `R_f` | Return the same callee view inertly; preserve its evidence | Empty |
| `N_x` | Resolve `d_x`; reference its already rebound Value interface and inherited packet | Empty |
| `R_x` | Return the same Value view; no shape-derived elimination | Empty |
| `c` | Apply `Foot-Call` once, in addition to both child recipes; complete invocation is distinct from latent result | `{p_0}` |
| `L_step` | Inert local closure; retain the original body root and captured `d_f` view with its identity schema | `{p_0}` |
| `R_step` | Return the closure value without executing its body | `{p_0}` |
| `N_step` | Reference the already registered local closure/provider; do not copy its source introduction as a fresh leaf | Empty local increment |
| `R_return` | Return that same local closure; retain its inherited actual view and matching result information | Empty local increment |
| `B` | Sequence the RHS/result binding and final return at shared roots; union child inventories | `{p_0}` |
| `L_apply` | Inert outer closure; retain its body and ordinary Value formal skeleton | `{p_0}` |

**Base cases.** A Name rule supplies a resolved provider reference and
dependent identity correspondence, not a fresh boundary introduction. Thus
the three Name occurrences add no Generated leaves. For `N_step`, the
existing root can already contain `c`; referring to that root does not
create a second source Call occurrence. Inherited packets remain present and
unconstrained by this count.

**Result case.** `Result(Value(A))=Comp(empty,A)` and normalization is Return
of the same descriptor. It adds no source elimination of latent `A`, even
after substitution. Its original footprint is its child's footprint. A
matching result projection is a transport edge; it cannot introduce an
original profile leaf.

**Call case.** Both children have empty local generated footprints. The
unique resolved Call emits exactly the one displayed `Foot-Call` leaf at
the same outer `d_f,R_f` root. The argument is the actual inner returning
Name computation, not every computation having the same printed empty row.
Complete entry/body/consumer behavior is a later interpreted constraint and
realization; it does not add another source elimination node or manufacture
another profile leaf from that behavior.

**Lambda cases.** Ordinary unannotated `apply` and `step` are Pure
introductions, with Value parameters chosen from syntax. Neither is a
callback-position literal receiving expected `Slots`. Capturing `f` retains
its original root; public transport of the closure does not expose its
private environment. The body's leaf set is retained as latent source code,
without running it or replacing its root. Thus both lambda inventories equal
their bodies' inventories.

**Bind case.** Ordinary Bind uses the RHS result and registers one `step`
binding, then the final result references that provider. Sharing and union
retain the RHS body's original Call leaf once. No invocation is added by the
returned Name, as the addendum requires. This completes the source induction.

The source-contract inventory also has Literal, Operation, Reify, Eliminate
and, in typed-core, Handler constructors. None occurs in this exact selected
source tree. The theorem does not silently supply their original profile
rules or assert closure for a larger source language. Provider/ambient graphs
may contain all of them; those are inherited inputs here, not additional
nodes of this source's original introduction footprint.

## 5. Transport normal form and role-policy preservation

### 5.1 Normal form

For every output packet-profile fact in a finite composed recipe, there is
an input profile leaf `ell`, a position `r_ell` in that leaf's own coordinate
domain, and a typed composite correspondence `M` from that domain such that

```text
chi_out(t,b) iff
  exists ell,r_ell,M.
    LeafProfile(ell,r_ell,b) and M(r_ell,t),
```

where the existential is over the recipe's actual indexed inputs/routes,
and `ell` is either Generated or Inherited as in §3.1. Source tags, original
receiver references, `K,D,L` and witness identity are retained. This is the
expanded typed-boundary equation, with no profile supplied for the generated
leaf beyond `Foot-Call`.

A Generated leaf uses its introduced original position `p_0`. An Inherited
leaf uses the supplied packet's input-view position; its retained original
source witness does not identify that position with an original address.
When the witness supplies an original-to-input correspondence `J`, the route
from its original position `s` to output position `t` is `M compose J`, with
an intermediate input-view position `r_ell`. For example, an inherited
returned-thunk fact at `latent.effect` can originate at
`result.latent.effect` through `J`'s result projection.

**Induction.** At a Generated leaf the identity route starts at its introduced
position. At an Inherited leaf the supplied packet is the base, and identity
starts at its input-view coordinate; this does not assert an identity route
from its original source coordinate. At identity Name/binding/capture
transport the same witness survives. At a
projection or result transport, append its typed correspondence; paths not
in its domain have no output incidence. At an indexed union retain the
chosen input and use its induction witness. At a composed route use
`N_*(M_*chi)=(N compose M)_*chi`; conversely split the composite witness at
the actual intermediate correspondence. A finite registered-graph use has
a finite route derivation; induction is on that derivation, not on recursive
type unfolding. These cases exhaust the constructed packet algebra.

Consequently every *generated* `beta` output entry originates at `p_0`,
although it can appear at many corresponding view addresses. There is no
theorem here that the complete output packet has only one `beta` entry:
Inherited leaves remain separate even if their static labels coincide.

### 5.2 Latent results do not create another generated original position

Typed-boundary §6 expressly distinguishes `call.effect` and
`result.latent.effect`: result projection maps the latter to a returned
`latent.effect`, and does not map the former there. The generated leaf is at
the former. Therefore a matching result projection cannot turn that leaf
into a new original latent position. A future call of returned `step`
executes the original body `c` with its captured view; it does not expose the
private `f` profile as a public latent-result profile of `step`.

An inherited actual returned thunk/closure retains whatever boundary packet
it has at its own matching result paths. A supplied callee-result profile
can also project to its matching paths. Both facts are compatible with the
singleton **generated** inventory. Removing either inherited source would
violate the selected transport rule. Filling either from equal endpoint shape
or the root `p_0` seed would also violate it.

Uniform endpoint substitution commutes with Result/Normalize and with
dependent typed address renaming. A substituted latent result reveals paths
in an inherited packet's existing symbolic domain, but does not add a source
elimination occurrence or a Generated original position. A transformation
that supplies a new original source contract is an introduction, not this
substitution/transport case.

### 5.3 Exact status of NonHandler refinement

The candidate `Gamma_gen` is independent of the administrative role label:

```text
NormalizeRole(ProtectedHandlerSeed,R_f) = NonHandlerFormal at the same R_f
NormalizeRole(Gamma_gen) = Gamma_gen
```

The generated source remains unannotated, the applicable generated position
remains `p_0`, and its removal predicate remains false for every operation.
Hence normalization of this candidate static profile retains full protection
and introduces no concrete removal permission. Actual providers keep their
actual roles and §21 entry.

This proves policy preservation for the constructed footprint. It does not
prove a solution-preserving normalization of a larger original profile whose
applicable positions have not yet been generated. Operational protection
still requires the actual source profile, correspondence, receipt and live
receiver, with pre-dispatch `Observe` and current `Inc_C`. Annotation absence
does not manufacture those dynamic premises, and expiry still filters their
activation-scoped protection.

## 6. A second attempt: inversion down to the original introduction

The genuinely different route is to start with an arbitrary profile fact in
a putative original source realization and invert all typed transport,
receipt and observation rules. Typed-boundary §6 states that the graph has
boundary introduction, typed-flow, receipt and source observation edges only.
Receipt creates ownership, not a boundary or profile; Observe creates no
grant or value profile. Inverting profile-image rules therefore reaches an
original introduction at a corresponding source signature position.

This proves the conditional provenance implication

```text
OriginalProfileFact(beta,p)
  => exists original source introduction I at beta.
       I supplies an applicable profile position p_I
       and a matching typed route from p_I to p.
```

It does **not** prove `p_I=p_0`. The exact introduction clause in that same
section takes

```text
b = (receiver r, callback slot a, signature profile Gamma, type endpoints)
```

and says that `Gamma` marks exactly which computation positions of the
received typed value are protected and have concrete contracts. It
explicitly distinguishes this introduction from transport and says that
profiles are supplied by source elaboration. A single such introduction
can therefore be the provenance witness for several original positions.
The no-authority-creation induction is exact while leaving that original
inventory parameter untouched. Counting boundary IDs or source binders
cannot remove the parameter.

For the least construction of §3 to close P, the following **converse to
Foot-Call** must be proved from a source introduction rule at this exact root:

```text
Applicable_original(C,d_f,R_f,p;xi)
  iff p = p_0 and ElimOrigin(c,u_f,d_f,R_f,p_0,p_out(c)).
```

The right-to-left direction is the reviewed initial constructor. The
left-to-right direction is the remaining obligation. It concerns original
applicability, before any transport or runtime event. It cannot be justified
by defining `Applicable_original` to mean the generated right side and then
calling that definition source completeness.

This identifies the failed proof step positively: all normal forms end at
the existing **parameterized original boundary introduction**, not at an
exhaustive singleton rule. Inferred-call-view §2 requires source-derived
profiles and forbids creating them from type shape/Q; §5(1) asks for the
missing constructive rule. Source-contracts §3.2 exhaustively accounts for
emitted execution-relation clauses relative to the finite decorated source
base; its §3.1 supplies original profiles/paths/receipts. It is not an
exhaustiveness theorem for raw-source profile introductions. Core §§6, 7, 9
preserve source positions and decorated certificates without deriving that
introduction inventory. Thus this is not an inference from the absence of
rules: it is exact inversion to a named input of the present positive rules.

No additional latent position has been licensed by this inversion. A
schematic extra entry at `result.latent.effect` would need its own source
applicability derivation. Merely instantiating `F_c` to a Function returning a
thunk, or retaining a supplied decorated result profile, is not that
derivation. Conversely, prohibiting every such entry by leastness of a
newly defined recipe has not yet proved the original source converse.

## 7. Verification, omissions and commit packet

The bounded work used two methods: constructive least-footprint emission and
transport normal form; then inversion of arbitrary transport to its original
introduction. No lightweight semantic checker was run, since a finite model
sharing the same introduction recipe would only check that recipe's closure
and could not certify the missing source converse. No compiler build, test,
Oracle run, runtime measurement or source-acceptance experiment was run.

The mathematical checks are the all-node exact-tree induction, indexed image
composition/inversion, original-address/view-address distinction, and
inspection of every governing introduction/transport clause named above.
Independent compiler-referee review found one minor coordinate-domain defect
in §5.1: an inherited packet's input-view address was incorrectly named as an
original address. The repair now starts inherited routes at the packet input
coordinate and composes a supplied original-to-input map when available. A
spec-auditor delta review closed that finding with no new issues. This does not
add a premise or establish profile completeness.
The focused document check passed: all eight relative links exist; no
trailing whitespace; final newline present; and all eight direct dependency
hashes agree both with their working copies and with pinned baseline blobs.
HEAD remained the pinned baseline at that check. This was a metadata check,
not an executable source-semantics checker.
The primary owns independent review, Git integration and push. A source
adequacy/completeness proof, actual receipt/typed capture attachment,
admission A, full-profile solution normalization and Option A/2 production
containment remain omitted and open.

Exclusive changed path:
`notes/progress/2026-10-06-profile-source-normal-form-construction.md`.
No compiler, authority, approved answer, shared coordination or checker path
is changed. Proposed commit message:
`Document captured-step profile footprint and introduction converse`.
Shared task/theory/index synchronization is intentionally deferred to the
primary after adjudication. This artifact is a research-only checkpoint and
makes no independent-review, theorem-closure or implementation claim.

Frozen direct dependency SHA-256 values at the baseline:

| Dependency | SHA-256 |
| --- | --- |
| `2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `2026-10-06-nested-block-function-source-realization-addendum.md` | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |
| `2026-10-03-callback-context-delivery.md` | `df4941d4c66e4f3147257024a35e7041a2c51dd528657cc80efaf3d0db62fed5` |
| `2026-09-29-scc-intrusion-redesign-charter.md` | `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed` |
| `2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `2026-10-02-typed-boundary-realization-draft.md` | `1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb` |
| `2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `2026-10-06-source-call-generation-construction.md` | `6bd7773326ccdd3101eaeb60a7e0f5d98a6c7a80b68467f6bf06a6466ffc4073` |
