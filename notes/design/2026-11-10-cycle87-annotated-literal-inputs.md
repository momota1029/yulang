# Cycle87: checked annotated-literal inputs

Status: Draft proof interface. Date: 2026-11-10.

## Objective and authority

Close the finite input-lowering boundary for scope-resolved bindings whose
values are existing `Inference.Expr.lit` expressions and whose explicit value
annotations are scalar `Inference.Base` types. Spec 3.1 supplies scalar literals;
spec 4.2 says that value annotations check the inferred type against the
annotation and determine the published value type. Spec 6.3 supplies associated
equations and sibling conjunction. The existing Yulang2 oracle C3-ACCEPT-01 and
C3-PARENT support scalar values and sibling examples, not this lowering theorem.
No new runtime run or parser adequacy is claimed.

An unannotated literal gives a lower bound, not the paired equality required by
`CommonRoleOrdinaryKnownness.Evidence`. Do not promote lower bounds into exact
seeds. The new interface requires the scalar annotation syntactically and checks
the literal tag against it. Nonliteral expressions are outside this deliberately
narrow fragment, even when well typed in the language. Failure is not a language
rejection. Annotation effects are not fixed; the theorem concerns value types.

## Data, independent judgement, executable entry

`Binding` stores source name, existing Expr, and explicit scalar annotation.
`Valid` requires every expression to be the literal of its annotation; this is
a decidable fragment check, not successful solving. `lower` extracts named facts
in original order, retaining duplicates. Independent `Seed` reads an original
binding and its checked syntax. Independent `Derives` closes those seeds under
original grouped source equations, without consulting lower, allocation or run.
`Models` constrains the same source-name domain as the inherited entry.

`run` checks all original bindings, lowers them, computes canonical allocation,
checks the grouped source and executes finite saturation/readiness. It takes no
caller facts, ordinary atoms, state, package, fuel, map, model or success proof.

## Theorem types and limits

For every binding in the checked literal fragment and every common value type,
its existing declarative literal typing plus the annotation upper bound holds
iff that value type is equivalent to the annotation. Literal typing alone does
not imply this equality. For every finite binding list and fact, membership in
lower is iff independent Seed, under the explicitly computed syntax validation.
For arbitrary env/roles/wf/awf/src/bindings, run=true iff Valid bindings, valid
source, independent model existence, and independent evidence discharging every
original role clause. Soundness and completeness are both quantified over all
such finite inputs. No principal typing theorem for all expressions is claimed.

Source identities and grouped declarations are still scope-resolved inputs.
Their extraction, invocation sharing, dynamic children, general driver stopping,
final classification and dictionary observations remain open. All five B4
bridges remain. No new policy is chosen and existing questions stay pending.
