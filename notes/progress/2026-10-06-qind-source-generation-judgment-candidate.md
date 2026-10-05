# Candidate judgments for Q-independent source generation

Date: 2026-10-06
Baseline: `9b123f481cfb6e394787bee5855127e73b358f07`
Status: independently reviewed research proposal; no semantic or implementation authority
Scope: source generation for inferred Function call views, first tested on
`my apply f = { my step x = f x; step }`

## Purpose and authority

The Authoritative inferred-call-view direction selects source generation from
relevant declarations, definitions, uses and recursive components. It requires
stable `beta`/`Slots(beta)`, source-derived typed paths and ownership/receiver
relations, one original joint `(nu,K,D)`, and admission independent of `Q`.
It explicitly leaves the construction judgments open. The nested-block
addendum additionally fixes sequential binding, the returned `step` value,
and the identity of the captured outer `f` for this exact candidate.

Recent source registration attempts reach shared symbolic endpoints and call
constraints but not the original typed relation. This note changes method:
instead of another consequence check, it states a candidate **judgment
interface** and separates its missing constructors into static generation,
event-specific receipt instantiation, and later capture attachment/lookup.
The split names proof obligations; it does not solve them. None of the
judgments below may be used as an admitted rule until each clause is defined,
reviewed and proved.

## Candidate static-generation interface

Use `S` for the resolved finite source artifact, `C` for the relevant source
component, and `Gamma_ext` for independently declared external interfaces.
The exact-candidate structural facts available from `S` are:

```text
outer formal d_f
inner formal d_x
local binding d_step, sequentially visible after its initializer
u_f -> d_f, u_x -> d_x, u_step -> d_step
inner call c = Apply(u_f,u_x)
capture incidence (l_step,d_f,u_f,position(u_f))
final expression u_step returns the local function value
```

They come from the verified CST/shadow lexical differential and the approved
source interpretation. They carry no type, call role, receipt, or activation.

The proposed interface is:

```text
Gamma_ext ; S ; C  |-gen  (I, B, P, Phi_C, E_C)
```

where the intended outputs are:

- `I`: symbolic declaration/use interfaces, with formal and resolved uses
  related through one shared inferred endpoint;
- `B`: stable static source-position/contract identities `beta` and their
  complete `Slots(beta)` inventory;
- `P`: typed path, Flow, owner/receiver, and receipt-schema correspondences
  generated from the source component;
  - `Phi_C`: the original constraint relation in one jointly scoped
    `(nu,K,D)` fiber, including shared dependencies and incidence;
- `E_C`: source/typed correspondence references that connect the preceding
  outputs to the exact resolved binders, uses, calls, annotations and scopes.

`Q` is absent from the judgment's inputs and construction. This signature is
only a contract for a future generator. Omitting `Q` from a signature would
not prove independence if any input had already been formed from `Q` success.
Generation retains unresolved symbolic endpoints and constraints; it does not
choose independent satisfying witnesses for separate ports. More strongly,
generation must present the scoped relation over its admissible fibers; it
must not select one satisfying assignment and encode only that assignment.
The relation's scope and admissible fibers are themselves source-derived and
remain proof obligations.

### Constructor clauses still required

The following are proof obligations for defining `|-gen`, not rules already
selected by this note:

1. **Resolved component:** derive `C` and its relevant declarations,
   definitions, uses, recursive roots and source scopes from `S`. Exact
   recursive relevance and closure remain open.
2. **Shared endpoint registration:** allocate symbolic declaration/formal
   endpoints once and reuse them at every resolved source use. Prove scope
   and reference preservation through any permitted generalization and
   use-time freshening.
3. **Ordinary structure:** apply the reviewed conditional parameter, name,
   result, lambda, bind and call constructions only within their stated
   fragment. For the exact candidate, this generates `Value(A_f)`,
   `Value(A_x)`, a call constraint at the endpoint referenced by `u_f`, and
   the sequential local-function result. These obligations do not solve
   callable membership.
4. **Inferred callable relation:** introduce a symbolic role-indexed
   `F_cb` relationship at the shared formal/use endpoint from the relevant
   source constraints. This is the first missing constructor. It must preserve
   the approved provisional protected Handler view and its ordinary-value
   refinement without assigning the actual role/entry of a supplied
   callable.
5. **Static slots/profile:** connect each exact source position to its
   completed contract, form `beta` and a complete `Slots(beta)` inventory,
   and preserve annotation occurrence and lexical scope. A binder, source
   range, call node, empty profile, or freshly allocated label alone is not
   this connection.
6. **Typed correspondence:** derive typed paths, `Flow`, ownership and
   receiver incidences from resolution and typed elaboration of the relevant
   names, captures, argument receipt and calls. Type-shape equality and
   successful `Q` cannot construct these edges.
7. **Joint source constraints:** form original `Phi_C` under one shared
   `(nu,K,D)` scope, including all dependent paths/incidences and the exact
   source constraints. No per-port solving followed by witness combination.
8. **Annotation/protection contribution:** if an annotation is present,
   identify the source contribution it governs and its local permission while
   retaining unrelated effects/evidence. Annotation absence preserves the
   approved full-protection rule. The source-position-to-contribution map and
   realized removal conditions remain open.
9. **Admission:** define complete Function membership/admission independently
   of `Q` success, on the original relation and fixed joint fiber. Production
   Option A / Option 2 containment remains a separate proof gate.

The source-generated relation may be relational rather than a deterministic
generator. That is a candidate presentation, not a proof that it has a
principal or unique solution. Any completed interpretation must still prove
the required existence, source adequacy, principal-solution preservation and
scope/generalization laws.

## Event receipt is a separate judgment

Static generation cannot name a particular runtime entry or concrete provider.
Given an admitted instance of the generated joint relation and an actual
entry event, a separate candidate judgment would instantiate the receipt:

```text
P ; Phi_C ; xi ; Entry(event, formal, provider_view)
  |-recv  (boundary_instances, typed_correspondence, receipt)
```

Here `xi = (nu,K,D)` is one whole assignment satisfying the generated
`Phi_C` and its separately established admission condition, with the original
scope and contract/profile references intact. Receipt instantiation cannot
choose a satisfying assignment during generation or replace the relation with
one selected alternative. Establishing that this relation and its admissible
instances preserve principality remains open.

Its unresolved clauses include matching the received provider against the
source formal/interface, instantiating every static path under the same
original source identity, and proving receipt-before-entry realization.
Receipt creation cannot create the static contract/profile, infer the
provider's actual role, or make an expired receiver active. The core receipt
rules currently retain admitted typed-path premises; they do not supply this
source producer.

## Capture attachment and lookup remain later obligations

For the nested candidate, lexical `CaptureUseIncidence` supplies the exact
local lambda, outer formal, callee use and source position. It does not itself
attach typed evidence. After the original relation and an event receipt have
been generated, the later proof must establish both:

```text
original packet + typed capture incidence + closure creation
  |-attach  captured evidence environment

captured evidence environment + typed name occurrence
  |-lookup  transported original packet
```

Both conclusions must preserve the whole original contract/profile, static
slot inventory, typed correspondence and joint `(nu,K,D)` dependencies.
They cannot replace the original source-generation judgment, manufacture a
new receipt, or revive an expired activation. These remain O's and A's
separate proof obligations.

## Exact-candidate prefix and remaining holes

The source/shadow differential establishes the lexical input listed above.
The conditional core rules can produce shared symbolic endpoints and the
ordinary-call obligation. The derivation then stops before clauses 4–9 above:
there is no reviewed constructor from that symbolic prefix to the complete
original typed relation. No conclusion is drawn that such a constructor is
impossible.

The exact single-use candidate does not discriminate general role aggregation.
Before settling clause 4 for mixed or repeated uses, produce a source example
and derivation that distinguishes: one eligible ordinary-value use
determining the shared formal; all relevant uses requiring it; or retaining
role alternatives jointly until the complete source relation resolves them.
No option is selected here. The implementation lane must continue to represent
these unresolved clauses as premises/stubs and must not import behavior from
the Frozen Oracle.

## Required review and stop conditions

Review must check source authority, non-circularity, shared-scope
preservation, annotation-position separation, typed receipt ownership,
Q-independence and the O/A boundary. Reject any clause that takes the
completed `F_cb`, `beta`/profile or receipt it claims to generate as an
unlabeled premise, or that assembles the original fiber from independently
chosen ports. This candidate has no implementation permission.

Frozen Oracle is neither a premise nor a semantics source. No Oracle result,
legacy behavior, shadow acceptance or differential test closes a missing
constructor or theorem.
