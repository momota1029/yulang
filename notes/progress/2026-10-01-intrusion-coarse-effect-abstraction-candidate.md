# Conservative continuation-summary effect candidate

Date: 2026-10-01
Status: exploratory candidate; not selected or authoritative
Scope: ordinary shallow effects and handler residuals; no weight encoding yet
Implementation authority: none
Reviewed-by: architect, compiler_referee (read-only candidate review)

## Question

Can a sound compositional effect abstraction conservatively account for
shallow resumption without exact continuation-sensitive inference or
linear/affine continuation typing?

The candidate below is a response to that question, not a successor rule. Its
main unresolved dependency is provider/capture eligibility: a family row does
not say which handler may consume a request.

## Candidate abstract judgment

Let `Fam` be the finite set of operation families relevant to a checked module
and its imported interfaces. A computation has an abstract immediate effect
`E ⊆ Fam`. Functions, callbacks, thunks, and continuation values also retain a
latent effect set, which an ordinary call or force adds to the immediate
effect. Sequential composition and control-flow joins use set union.

For an operation request in family `f`, the immediate effect contains `f`.
In a shallow catch with scrutinee effect `E`, let `M` contain only those
families for which every operation that can contribute that family to `E` is
both covered by an arm and eligible for this handler under a separate
provider/capture relation. The candidate handler rule is:

```text
effect(catch e with H) = (E \ M) ∪ effect(value arm) ∪ ⋃ effect(operation arms)
```

Each operation arm receives its continuation `k` with the whole pre-handler
effect `E` as `k`'s latent effect. Invoking `k` therefore contributes `E` by
ordinary application typing. Passing or returning `k` must preserve that
latent effect in the resulting function/value type. The operation arm runs
outside this shallow catch, so its own effect is not implicitly filtered by
`M`. Incomplete coverage, unknown eligibility, or any uncovered operation
keeps its family in `E \ M`.

This rule is intentionally coarse. In the one-request-and-resume fixture,
`k` receives `[choose]` even though its concrete suffix is pure, so the
abstract result may retain `[choose]`. That annotation behavior is a precision
choice in this candidate, not a claim that the exact trace contains a request.
The finite set domain alone does not justify principality: the empty set is
expressible and is the least exact trace bound in that fixture. Any
principality theorem must be stated for the explicit compositional abstract
judgment above, whose continuation summary deliberately forgets suffix
correlation, and prove its least derivable solution property.

No linear or affine usage accounting is needed for this transfer: an arm that
does not invoke or export `k` does not incur its latent effect through ordinary
function application. Every actual invocation, force, or later invocation of
an exported closure must continue to carry that latent effect. Whether the
language's existing typing constructs preserve this property is unproved.

## Soundness sketch and conditions

Relative to the shallow trace transformer in
`2026-09-30-intrusion-shallow-handler-trace-calculus.md`, a candidate
induction has three cases:

1. An unmatched or ineligible request remains in `E \ M`; the trace forwards
   it and reapplies the catch to the forwarded continuation.
2. A covered, eligible request invokes its arm. The arm's own effects are in
   the arm-effect union. If it resumes the raw continuation, `k`'s latent `E`
   covers every family on every suffix path, including another request in
   family `M`.
3. A non-resuming arm has no suffix execution through `k`; its arm effects
   remain, while an input family may be removed only when coverage and
   eligibility are complete for every request that could produce it.

This is only a sketch for direct request trees. It does not establish the
provider/capture relation, effect soundness through higher-order subtype and
scheme instantiation, or a source/runtime correspondence theorem. In
particular, equal `[choose]` rows can have different handler visibility; rows
alone cannot justify `M`.

## Adversarial review result

Independent architect and compiler-referee reviews agree on the following:

- **Blocking for a general rule:** define provider identity and handler
  eligibility independently of family labels. A family may be removed only
  when each possible request in it is covered and eligible; otherwise retain
  it conservatively. Prove that source inference and runtime handler search
  implement the same relation.
- **Major:** state principality as a least-solution property of explicit
  compositional rules with the whole-scrutinee continuation summary. A finite
  powerset codomain by itself does not make the coarse one-request result
  principal. Open rows, higher-order subtyping, SCC schemes, and final
  acceptance remain outside the present argument.
- **Major:** incomplete handlers and residual operations must remain in the
  bound. Non-resumption removes a family only under complete eligible
  coverage. Nested outer handlers and callback ownership need explicit rules.
- No direct-fragment counterexample was found to the whole-scrutinee `k`
  effect, provided ordinary application and escaped closures preserve latent
  effects. This is review evidence, not a completed proof.

## Next characterization and proof matrix

Before considering any weight representation, define and prove the
provider/capture eligibility judgment, then check the effect abstraction
against:

- one request with resume, two sequential requests with resume, and no resume;
- complete coverage, an incomplete family handler, and one uncovered
  operation in an otherwise handled family;
- nested handlers with distinct and repeated families;
- outer-owned versus inner-owned callback under a same-family inner handler;
- delayed thunk forced under a handler;
- repeated callback calls sharing one frame pop;
- residual effects that are passed through and later handled by an outer
  eligible handler.

Only after this matrix should a weight be assigned a denotation. Every proposed
left/right transfer then needs a preservation argument against this abstract
judgment. Method selection, roles, and implementation resolution stay in the
mandatory later gate from the redesign charter unless this proof exposes a
concrete dependency.

No implementation, Oracle weight rule, or equivalence claim is authorized by
this candidate.

## Provider/capture eligibility remains open

The frozen reference directly states these principles:

- callback-origin effects supplied by an outer caller are protected from an
  inner same-family handler unless the receiving boundary exposes them;
- a concrete callback argument row grants matching-family visibility to
  handlers inside that receiving function;
- wildcard surface rows do not erase unrelated hygiene evidence; and
- a shallow operation arm receives the raw continuation.

The nested-provider probes in
`2026-09-30-intrusion-weight-routing-counterexample-search.md` characterize the
first two behaviors as outer result `[1]` without the concrete contract and
inner result `[2]` with `[choose]`. The helper witness records a further Oracle
conflict: its pure `invoke` scheme drops an effect that its callback call can
perform. The successor must propagate that effect and conservatively retain it
when shallow resumption can reach another request. These observations do not
define a provider identity or grant lifetime.

A source semantics will need at least distinct operation-family, request
provenance, callback-boundary, and active-handler identities. Candidate
eligibility notation is:

```text
eligible(request, handler) iff
    handler is active
    and handler covers request.operation
    and visibility evidence authorizes this request at this activation
```

The last condition is intentionally unspecified. Treating a capture contract
as a transferable Boolean attached to a family is unsafe: if it escapes in a
returned closure, a later handler without a matching receiving-boundary
contract may steal the request. The converse shortcut—dropping every grant at
a helper return—could prevent a contract that composes through a helper from
working. The evidence must therefore be scoped to its introducing boundary
and active handler, and its call, force, closure-escape, and scheme-instantiation
transport must be proved without widening its scope. This is a challenge
example, not an established Oracle behavior or a selected successor rule.

Annotation syntax also cannot be collapsed to one “has a contract” bit.
Absent annotations, concrete nonempty rows, concrete empty rows, wildcard
`[_]`, and any effect-only skeleton position with wildcard behavior may impose
different constraints. The frozen effect specification characterizes several
of these paths, while its weight operations remain non-authoritative. The
successor must define the semantic meaning of each supported annotation form
before deriving any encoding.

Independent architect, compiler-referee, and spec-auditor reviews agree that
provider provenance must remain separate from family identity and that the
family-removal side condition must quantify over every possible request path:
each contributing operation must be covered and eligible at the handler
activation being modeled. The references establish the visibility principle,
not the provenance assignment, grant lifetime, closure-escape rule, or
inference/runtime correspondence theorem. Consequently, the notation above is
only a proof target. It does not close the blocker or authorize a data
representation.

The next proof artifact should define a source request-tree judgment with this
eligibility relation and prove a one-step handler simulation: covered eligible
requests enter the matching arm; incomplete, uncovered, or ineligible requests
forward with provenance intact; and any raw-continuation resumption preserves
the whole pre-handler effect bound. Include the callback/hygiene pair,
helper-call composition, delayed thunk force, closure escape, and repeated
callback request before relating the judgment to a runtime representation or
weight calculation.
