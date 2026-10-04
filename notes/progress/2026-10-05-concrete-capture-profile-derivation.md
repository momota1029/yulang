# Concrete capture item to typed callback profile: conditional derivation

Date: 2026-10-05
Status: source-rule derivation candidate; profile construction and production bridge remain open
Scope: derive event eligibility from an already established concrete callback profile, without adding a carrier
Branch: `research/simple-sub-intrusion`
Governing sources: [ordinary computation semantics](../design/2026-10-02-ordinary-computation-semantics-package.md) §§4, 7; [typed-boundary realization](../design/2026-10-02-typed-boundary-realization-draft.md) §§6, 8; [callback context delivery](../design/2026-10-03-callback-context-delivery.md) §§2–2.1; and the user-approved [mixed-row fragment](../design/2026-10-03-concrete-compatibility-boundary.md#9-user-directed-mixed-effect-row-fragment-2026-10-05)

## Selected visibility rule

The ordinary-computation package records the user's 2026-10-02 decision:
direct requests and caller-owned requests exposed by `Force` have equal
eligibility when they are observed under the same concrete typed callback
boundary. The request origin and dynamic event remain distinct evidence; origin
does not veto the concrete boundary contract. This is narrower than allowing
all requests with the same family label.

The existing candidate rule is:

```text
Captureν(q,h) iff
  h is installed by receiver r
  ∧ Active(h,C) ∧ Active(r,C)
  ∧ ∃b,p. b.receiver = r
        ∧ Inc_C(q,h,b,p)
        ∧ Γ_b explicitly admits q.operation at p under ν
```

`Inc_C` is event-specific and receiver/handler scoped. Its derivation uses the
typed boundary path, the event's observation at the corresponding executing
effect port, and the receiver's receipt for that same typed view. The evidence
uses the existing `Flow`, `Observe`, `Path`, occurrence/incidence, and shared
`ν,K,D`; family support by itself supplies none of these facts.

## Conditional concrete-item corollary

Let `τ` be a concrete family/type item at the input computation port `p` of a
role-indexed Handler boundary `b`. Assume source elaboration has already
established the profile clause

```text
Γ_b(p) admits exactly the operation instances compatible with τ under ν
```

and has connected the annotation occurrence to that port. Then, by unfolding
`Captureν`, a request `q` can be captured there exactly when:

1. its operation instance is compatible with `τ` under the source-selected
   operation/type comparison;
2. its current executing view has the required `Inc_C(q,h,b,p)` evidence; and
3. the receiver and handler candidate are active at the actual search point.

This establishes candidate visibility/eligibility, not unconditional selection.
Actual capture additionally requires ordered search to reach `h` and a
selected arm to satisfy its separate `OpCompat` typing condition.

The rule applies equally to a direct event and a caller-owned event exposed by
`Force` inside the same complete `CallView`. It does not require equality
between the event's generating occurrence and the annotation occurrence. It
also rejects a family/type match without the typed observation path, and a
matching event after the receiver/handler incidence has expired.

For the approved `write int` example, this corollary uses only the stated
concrete compatibility instance. It does not promote `int <: 'a` to a general
family variance rule or infer any effect-position meaning for `never`, `Any`,
or the empty row.

### The user-named `foo` fragment

The earlier user-specified type candidate explicitly says its input
`['e, foo]` is under a capture contract admitting `foo` at that boundary. For
that fragment, the profile premise is source-given: at the annotation's input
effect path `p`, `Γ_b(p)` includes the named `foo` operation contract, while
`'e` continues to denote its separate complete abstract view. Consequently,
an event in the `'e`-derived view is eligible for a boundary-local `foo`
handler exactly when its own typed incidence reaches `p`, its operation
instance matches the declared `foo` contract, and the receiver/handler are
active. Its producer may be the callback body or a caller-owned computation
exposed by `Force`; the origin remains in `Rel_C` but does not cancel the
explicit grant.

This derives the intended local `foo` visibility clause from the user's
example and the selected `Captureν` rule. It does not make every concrete
effect item in every Function port a capture grant: role, input/output port,
explicit contract, and typed path still determine the boundary profile. Nor
does it establish the abstract/concrete row-combination or output subtraction
rule.

## Separate subtraction obligation

The capture rule establishes eligibility for one event at one active
receiver-local candidate. It does not alone justify subtracting a whole
`write int` point from a public row. Reverse addition still requires the
corresponding concrete contribution to be attached to the source view, and the
complete output image must contain no unremoved contribution at that same
family/type point before its set-like support can disappear.

The [attachment subtraction probe](2026-10-05-effect-attachment-subtraction-playground.md)
gives a two-event characterization of this distinction: consuming attached
`q0` does not remove `write int` support when a distinct `q1` remains in the
complete output image. The finite result is not a general source proof, but it
rules out the support-wide shortcut within its stated model.

## What is still missing

The premise mapping surface syntax to `Γ_b` is not proved here. In
particular, the source construction must identify the concrete component's
original annotation occurrence, its Handler role and typed port, and the
complete profile positions. An abstract component such as `'e` must retain its
complete correlated `Rel_C` view and shared `K,D`; it cannot be replaced with
the concrete profile's family support. A covariant row remains an allowance,
and the provenanced capture profile is local to its source boundary.

Current `ResolvedExpr`/HIR and `yu-types` do not provide a production
annotation-to-profile path. The source design leaves that elaboration, the
mixed abstract/concrete combination rule, and the complete-image proof open.
The bounded checker in the [membership reconciliation record](2026-10-05-effect-component-membership-playground.md)
checks the selected event-eligibility clause over 256 cases; it does not prove
these missing mappings or the callback production theorem.

No new relation or carrier is proposed. This note derives a conditional local
rule from the selected source visibility judgment and isolates its unproved
profile-construction premise; it does not alter authority or authorize
production inference changes.
