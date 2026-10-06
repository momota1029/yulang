# Profile substitution naturality: no fresh origins, but no first-introduction converse

Date: 2026-10-06
Baseline: `f93fb06cd40c12fed6caf5051e045f206c4b2da6`
Status: compiler-referee reviewed research-only producer artifact; one minor precision repair applied by primary
Claim classes: source-preservation consequence; algebraic method countermodel;
exact local output discriminator. Not an original-source countermodel.
Scope: the original profile of captured `f` in
`my apply f = { my step x = f x; step }`
Semantic and implementation authority: none
Lease: this file only

## 1. Result and what this new method decides

Substitution naturality does exclude allocating a genuinely new original
source-position identity solely because the result endpoint is instantiated
with a Function or Thunk. It does **not** exclude a source-generated dependent
profile clause already referring to that result endpoint before substitution.
Its concrete typed-path instances can become visible when the endpoint is
interpreted, while its original clause identity, annotation absence, source
anchor and scope remain unchanged.

The precise graft law is interpretation under a composed assignment. It is
not an equality obtained by mapping a syntactically empty concrete effect-path
set through an opaque type variable. A two-descriptor, one-extra-clause model
below satisfies the actual graft law and preserves every original identity.
Thus this method cannot derive the exact singleton original inventory from
preservation alone. Increasing the substitution cases or assuming more
ordinary value polymorphism does not repair this route.

This is a countermodel to the **claimed implication from those algebraic laws**,
not a certified second Yulang semantics. In particular it does not certify
that its additional clause is an independently justified source profile
introduction. The decisive local output is identified in §6; none is adopted.
No conditional completeness theorem takes the desired converse as a premise.

## 2. Exact source and three different meanings of an unknown endpoint

The [nested-block addendum](../design/2026-10-06-nested-block-function-source-realization-addendum.md)
§2 fixes the source tree and the capture of the same outer formal:

```text
lambda(f,
  bind(step,
    result(lambda(x,
      call(result(name f), result(name x)))),
    result(name step)))
```

The final Name returns `step`; it does not invoke it. There is one Call
`c=f x`. The reviewed [Call construction](2026-10-06-source-call-generation-construction.md)
§§3–5 introduces one complete Function variable `F_c` on the same inferred
root `R_f`, with an unknown value result endpoint `A_c`, and the immediate
original seed `p0=(beta,call.effect)`. Its effect coordinate is the complete
invocation, including entry/body/designated consumer, rather than the effect
of the inert argument carrier or the callee body alone. The ordinary Name
argument `x` supplies ordinary-value evidence on that shared relation.

| Object | Meaning and permitted reasoning |
| --- | --- |
| Flexible source/inference endpoint `A_c` | A coordinate introduced by Call generation before solving. It may acquire constraints and a latent constructor later. Its being unconstrained so far is not a proof of Reynolds relational parametricity. |
| Descriptor semantic assignment `nu` | Interprets all endpoints, profiles and the retained `K,D` jointly. At a fixed fiber, `nu(A_c)` can already be latent even when its syntax is still a variable. Evaluating an existing predicate is not allocating its origin. |
| Generalization/use substitution `theta` | A permitted, scope-preserving whole action on the retained relation and its coordinates. Captured outer roots are not independently generalized by local `step`; quantified local coordinates are freshened/grafted together. |

These objects cannot be exchanged in a free-theorem argument. No selected
clause declares that profile generation is a relationally parametric program
which cannot inspect descriptor structure. The selected direction instead
requires source-origin relations and their consistent symbolic incidences.
All comparisons below use one `xi=(nu,K,D)` at a time; varying a substitution
in the metatheorem is not independently choosing a witness at each port.

## 3. The actual preservation laws and their scope

[Inferred call views](../design/2026-10-05-inferred-function-call-views.md)
§2 and exact [approved a2](../../questions/2026-10-05-function-call-view-formation/approved-answer.md)
decisions 4–6 select stable source position/contract identity, annotation
presence and lexical scope through inference, generalization, instantiation
and transport. Their exact generating/preserving judgments remain open.
They prohibit obtaining a new relation merely from type shape or pending `Q`.
They do not state invariant cardinality of concrete effect-path instances over
all semantic assignments, nor a generic parametricity theorem for metadata.

The reviewed, non-authoritative
[parametric linking](../design/2026-10-02-parametric-component-linking.md)
§2 supplies the concrete graph law used by the proposed method. For a supplied
finite graph `G`, graft `theta` copies its existing nodes/adjacency and acts on
all references and primitive operands consistently. Distinct source boundary,
annotation, owner and event identities are not merged by type equality. Its
substitution lemma is, up to the one legal owned-name renaming:

```text
Interpret_nu(G[theta]) = Interpret_(nu composed with theta)(G).
```

The equality includes profile/dependency references. Primitive relations are
evaluated with their entire substituted operand tuple. It is not a statement
that a primitive's truth or extension is constant as its operands change.
Further grafting composes; graph substitution introduces no source execution,
Force, adapter or dynamic event.

[Source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
§§2.1,3.4 retain original binding and primitive identity, whole freshening,
legal uniform graft and joint hiding. They do not replace the primitive's
meaning by an opaque identity-only relation. Charter
[§§21,22,24](../design/2026-09-29-scc-intrusion-redesign-charter.md)
fix entry roles independently of solved latent value shape, preserve every
scope guard and actual receiver role, and forbid speculative recursive entry
Force. These laws concern roles, scopes and execution; they do not state that
the result's static profile is necessarily absent.

[Typed-boundary §6](../design/2026-10-02-typed-boundary-realization-draft.md)
proves an indexed relational-image law for **supplied** profiles and matching
paths of a fixed monomorphic realization. Every transported output has an
input boundary witness; `p0` cannot be copied to an unrelated latent result
path. The same section expressly leaves solver substitution and scheme
lifecycle separate. Likewise
[source-realization §§2–3](../design/2026-10-02-source-realization-and-symbolic-basis.md)
supplies fixed finite monomorphic `Slots(b)` and excludes polymorphic
instantiation. Its original-slot query inventory is not a proof about arbitrary
unknown-result source generation. It permits symbolic shape/position guards
in the supplied original constraint/query inventory, without constructing
those guards from arbitrary syntax.

A sound consequence of the selected preservation direction is:

```text
a use-time realization of an original beta-profile witness
must retain a pre-substitution original source-position witness;
substitution by itself cannot supply a first source origin.
```

For the particular supplied-graph copying protocol this has a direct proof:
map each output profile node back to its copied template node, then follow its
original source tag and uniformly substituted operands. No other output node
can be allocated by that protocol. This proves origin preservation for that
protocol, not completeness of its input graph. A node-count statement about
one graph copy is neither a bound on all allowed profiles nor invariant
cardinality of concrete dependent path instances.

## 4. Smallest useful countermodel to the naturality implication

Use two independently interpreted descriptors:

```text
U = Unit
T = Thunk(e,U)                (e is one retained symbolic effect endpoint)
```

Let `alpha` be one flexible value endpoint. Retain the mandatory original seed
node `s0` at `p0`. Add exactly one hypothetical dependent node `s1`, with a
fixed source label `(C,d_f,c,result-root)` and the same `beta`, annotation
absence and original scope. This is a mathematical test of preservation,
not an authorized original introduction. Its static predicate is:

```text
L(alpha,p) iff alpha is Thunk(E,B)
                and p is that descriptor's current thunk-effect path

Chi_extra(beta,alpha,p) iff L(alpha,p)
```

The defining relation `L` and its identity are fixed **before** any substitution.
Its operand `alpha` is the original `A_c`; it is not a independently selected
provider. In the received Function signature, its exposed instance has prefix
`result.thunk.effect`. `s1` does not copy, rename or project the seed `s0`.
It presents a separate dependent original-profile candidate attached to the
result root. No annotation, owner, receipt, activated receiver, lexical
capture or concrete grant is added. If it were a lawful original introduction,
annotation absence would give its applicable instance full protection and no
annotation removal grant, just as required elsewhere.

The only evaluations needed are:

| Input descriptor | `L`'s concrete extension | Original node identity |
| --- | --- | --- |
| `U` | Empty | The same dormant source-tagged schema `s1` |
| `T` | One current thunk-effect path | The same source-tagged schema `s1` |

For any lawful substitution `theta` on its operands, substitution gives the
literal clause `L(theta(alpha),theta(p))`. Evaluating that clause at `nu` is
identical to evaluating the original clause at `nu composed with theta`.
This is the graft law of §3, with no extra premise about its extension. Two
substitutions satisfy composition for the same reason. All `K,D` coordinates,
source tags and operand incidences undergo that one action.

At a fixed assignment where `nu(alpha)=T`, `s1` already has its one concrete
instance **before** replacing the written variable by `T`. The substitution
reveals no newly allocated original node. At an assignment where
`nu(alpha)=U`, its extension is empty. These are different evaluations, not
mixed witnesses in the same fiber. Thus stable source origin is compatible
with nonconstant dependent realization, and the alleged no-extra-original-
schema conclusion does not follow from substitution naturality.

This witness is minimal for distinguishing this method: one unknown endpoint,
one latent constructor, one extra tagged predicate/node and two descriptors
separate empty from nonempty realization. No multi-use, recursive, nested
annotation, handler-stack or Oracle complication is needed. A Function-only
version uses its immediate call-effect path instead of the thunk-effect path;
it adds no logical mechanism.

**Exact limit of the countermodel.** The generic graph and interpretation laws
permit transporting this already supplied primitive. They do not certify its
first introduction at this raw source Call or formal. We have not proved that
a dormant schema is an admissible original `Slots(beta)` entry in every
successor presentation, nor that `L` is an independently typed source profile
constructor. Consequently this is not an Authority-consistent full Yulang
countermodel, an accepted-source witness, an observable separation, a proof
that a new decision is necessary, or a reason to select `s1`. It falsifies
using graft naturality **alone** as the missing first-introduction theorem.

## 5. Why the stronger proposed free theorem does not follow

Suppose one defines `EffPos(alpha)` from the visible syntax of an opaque value
variable as empty, but `EffPos(Thunk(e,U))` as containing its current effect
position. There is no ordinary total set map from that empty set whose image
is the latter singleton. Therefore one cannot assume a concrete-path functor
with an image naturality equation

```text
Chi(alpha theta) = theta_* Chi(alpha)
```

and derive absence by evaluating the opaque syntactic variable. The needed
path action across a graft that exposes unknown structure is not that set
map. Source symbolic relations are instead interpreted under assignments,
or dependent path schemas are transported as schemas. Under the actual
interpretation equation, the right side at `nu composed with theta` already
sees the latent descriptor and any supplied `L` instance.

Demanding that every profile generator factor through the rigid, already
visible effect addresses of the open syntax would exclude `s1`. But that is
a stronger **first-generation locality law**, not a consequence of origin
preservation. It is exactly the law needing independent source justification.
The fact that ordinary execution returns arbitrary `A_c` without another
Force proves no additional runtime demand. It does not establish that all
static result-profile introductions are absent. The role-preservation theorem
in [source-computation-role §3](../design/2026-10-02-source-computation-role-elaboration.md)
explicitly separates that operational uniformity from unproved scheme
substitution, while its §§4/8 warn that syntax-template counts do not count
all inferred signature positions.

Unconstrained flexible variables also do not grant a new scheme quantifier
whose relational parametricity can be used while discarding dependent
constraints. Any generalized constrained scheme retains those constraints
and their incidences. A family `L(alpha,p)` can be part of such a retained
presentation even though a bare erased type variable has no printed effect
position. Public printing does not decide internal profile generation.

## 6. The exact local rule output that decides this witness

For this test the smallest unresolved output is **one optional source-owned
result-profile schema node**, generated or rejected at the original formal/
Call component, before solving `A_c`. All other supplied roots are unchanged.
The candidate rule interface is:

```text
Resolve(d_f,c,u_f,u_x; original scope)
NoAnnotation(d_f); shared R_f,F_c,beta; F_c.result = A_c
known mandatory ElimOrigin at p0
---------------------------------------------------------------- Gen-Implicit-Result-Profile [not supplied]
original profile schema nodes at (beta,c,result-root A_c),
with their independent source-origin clauses and policy incidences
```

Rejecting this particular witness requires that the local rule return **no
`s1` node** with the stated source identity, `L(A_c,p)` interpretation and
result-path incidence. That rejection alone does not prove singleton: an
exhaustive source rule could admit a different result-root schema. Proving
singleton also requires showing that the original implicit contract contributes
no other first introductions on this exact source beyond the immediate Call
seed.
To include this witness it must return `s1` with the fixed source identity,
`L(A_c,p)` interpretation and matching result-path incidence, independently
of whether the current solver happens to have exposed a latent head. Returning
that node only after detecting a latent shape would violate the selected
no-type-shape-created-original-relation direction.

Neither output is supplied by the graft law. The clause selecting the node's
presence is not `L`'s substitution proof: it is its source introduction.
Likewise the absence output needs a source locality/exhaustion justification,
not a convention that the initial seed is the entire inventory.

| Selected clause | Effect on the optional `s1` output |
| --- | --- |
| No annotation means full protection at applicable positions | Fixes policy if `s1` is independently applicable; does not make it applicable or remove it. |
| Stable position, annotation presence and original scope | Forbids generating its original identity for the first time during substitution; does not determine which original schemas were generated. |
| Type shape and pending `Q` create no relation | Forbids solve-time invention of `s1`. A proposed preattached source clause still requires separate source justification; shape cannot be that justification. |
| Outer annotation is not copied to all descendants | Forbids producing `s1` by duplicating `s0`'s annotation/profile via an unrelated path. The witness instead hypothesizes a separate original introduction; this transport prohibition does not decide that hypothesis. |
| Value entry does not recursively Force a latent result | Excludes speculative execution; the optional node does not Force anything. |
| Same captured `f`, no lexical typed-evidence fabrication | Retains one `R_f` and source identity. The model creates no capture/receipt fact and obtains no permission from lexical capture. |

Thus no inspected selected clause **requires** preattaching `s1`; none supplies
its independent introduction. The selected preservation clauses forbid using
newly solved latent shape as its producer, but do not themselves prove that
an independently source-generated guarded result clause is impossible.
Whether the particular schema is admissible as an original profile is exactly
the local semantic/source-form question for the complementary audit. This
note does not classify it as allowed merely because the graft algebra can
carry it.

## 7. Verification, claim boundary and frozen commit packet

The method was manual symbolic substitution and a two-descriptor
interpretation calculation. No transition enumeration, Oracle invocation,
production build, test, source acceptance experiment, new implementation or
semantic mutation was run. The earlier rule-inventory/transport-inversion
attempts were read only to avoid repeating their method. The actual additional
evidence here is the separation of interpretation naturality from concrete
path-image naturality and its one-node countermodel.

The original-source singleton, full P, original contribution interpretation,
seed/refined solution preservation, source admission A, full soundness and
principality remain unproved. No `FVIEW -> SRC` or production-conformance edge
is promoted. Oracle mechanisms are not premises.
All direct dependencies matched the pinned baseline bytes. SHA-256:

| Dependency | SHA-256 |
| --- | --- |
| `rules/research-lab.md` | `ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd` |
| `rules/design-authority.md` | `9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29` |
| `rules/git-concurrency.md` | `e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e` |
| `questions/2026-10-05-function-call-view-formation/approved-answer.md` | `1071cf1c2d9abce2ffbc829cec7757d2b2f52849174c04751bd63aeefa520536` |
| `questions/2026-10-05-function-call-view-formation/receipt.md` | `6dcf408143c7eb48260d8c4df9ef73834da8d28a7f4ec9744ab381e67414cee0` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-02-typed-boundary-realization-draft.md` | `1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb` |
| `notes/design/2026-09-29-scc-intrusion-redesign-charter.md` | `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-02-parametric-component-linking.md` | `108fb9ab91c79aedc716ae476a07d567447644892ae1e32671c8fa4bce96efca` |
| `notes/design/2026-10-02-source-realization-and-symbolic-basis.md` | `0fe7dba1af48f7bf60d5cbc7933c1d3562dade5d1f6fac023cd19d25bdd67794` |
| `notes/design/2026-10-02-source-computation-role-elaboration.md` | `9a230eb023698666f4c3e518a527009d6915e65f658b230e6da6a29914ca3abb` |
| `notes/design/2026-10-06-nested-block-function-source-realization-addendum.md` | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |
| `notes/progress/2026-10-06-source-call-generation-construction.md` | `6bd7773326ccdd3101eaeb60a7e0f5d98a6c7a80b68467f6bf06a6466ffc4073` |
| `notes/progress/2026-10-06-formal-profile-formation-rule-attempt.md` | `8b8b1d49e587835d65c4c6a13a0fc476b07bc58282ac5c58e782b4e5fd5b6a4b` |
| `notes/progress/2026-10-06-profile-original-applicability-converse-construction.md` | `3a7749b9e3678bc05f6f5754ad5304a707169d84162e95c741e650686736b203` |

Checks: read-only HEAD check, targeted reads, SHA-256/baseline equality, and
final leased-note whitespace/relative-link/dependency checks. Single small
shell/Python process at a time; no generated side outputs. CPU/RAM/reasoning
wall-time were not instrumented. No Git mutation or shared-file edit occurred.

Frozen packet:

- Exact path: `notes/progress/2026-10-06-profile-substitution-naturality-closure.md`.
- Baseline: `f93fb06cd40c12fed6caf5051e045f206c4b2da6`.
- Changed dependency hashes: none; direct snapshot above.
- Claim/review: compiler-referee-reviewed research-only algebraic countermodel
  and preservation analysis; one minor quantifier precision repaired by the
  primary; no gate closure.
- Proposed checkpoint message: `research: separate profile origin preservation from substitution naturality`.
- Shared-record deltas intentionally deferred: primary/curator may record this
  proof route as exhausted by a law-level countermodel, retaining no-fresh-
  origin preservation and the exact optional dependent result-node output;
  do not promote original profile completeness, semantic ambiguity, A,
  principality or production conformance.
- Next useful action: independently audit the **source meaning** of the local
  `Gen-Implicit-Result-Profile` output. More substitution/transport cases cannot
  select it. The primary owns review, integration and all shared records.
