# Annotation-scoped effect protection: bounded obligations

Date: 2026-10-05
Status: unreviewed research checkpoint; bounded rule analysis
Baseline: `61a3651376166346a5baa03ec6679c310b0edbdb`
Lease: this file only
Method: authority crosswalk and minimal symbolic discriminators
Implementation authority: none

## Objective and exact authority

Identify the evidence needed to connect the approved annotation on `f` to
its permitted `io` removal, without choosing a removal mechanism, event
attribution rule, or protection lifetime.

The committed [Function formation answer](../../questions/2026-10-05-function-call-view-formation/approved-answer.md),
`function-call-view-formation/q1/a2`, decisions 2–6, establishes:

```text
apply f x = f x
    unannotated f: full effect protection

apply(f: _ -> [io] _, x) = f x
    annotated f: io from f may be removed
```

Decision 3 makes the second statement permission, without enacting removal
by this definition. Full protection does not mean empty effect support;
the permission does not generalize to other effects. Decision 2 links the
internal Handler Function treatment to the later inference from ordinary
value `x`, without rewriting an actual value's role or entry. Decision 4
requires original slot identity/scope and annotation presence/absence in
the formed contract. Decisions 5–6 retain one original `nu,K,D`, admission
independent of comparison success, and leave concrete generation/protection
rules as obligations. These are accepted decisions, not proved source rules.

The [approved annotation-boundary answer](../../questions/2026-10-05-source-annotation-boundaries/approved-answer.md),
decisions 1–4, requires the current endpoint's direct comparison with the
annotation target, target export with local realization evidence, retention
of earlier evidence, and no intermediate concrete adaptation without a
source boundary. Concrete query successes are not composed transitively.

[Callback delivery](../design/2026-10-03-callback-context-delivery.md)
§§1–4 preserves role-before-port interpretation, callback B, ordinary entry,
static slot versus dynamic receiver, and an existing Pure value's actual
role under its invocation view. [Concrete compatibility](../design/2026-10-03-concrete-compatibility-boundary.md)
§9 requires source-witnessed targeted removal in its separate deep-handler
mixed-row fragment; it explicitly leaves annotation-to-occurrence rules
open. That fragment does not supply a rule for this `io` annotation.

The typed-core and typed-boundary documents cited below remain Draft
conditional packages. Their detailed rules are proof inputs here, not new
authoritative source decisions. The protection-release notation Draft is
context only; no argument here identifies `[io]` with `'e?`.

## Smallest evidence obligation

A family label `io` alone cannot identify the annotation occurrence, the
view to which it applies, or the contribution eligible under that view.
An annotation-presence bit alone cannot identify its concrete permission.
An underlying closure identity or shared type-variable identity cannot
identify the applicable alias view or signature position.

The least distinctions that this local obligation must retain are:

1. This source annotation occurrence on the `f` parameter, or the explicit
   absence of such an annotation, with its original slot and source scope.
2. Its admitted Function target and the applicable effect-observation
   position, including the concrete `io` component at that position.
3. The local direct-query realization evidence connecting the incoming
   endpoint to that exported target, with earlier evidence retained.
4. For an actual removal claim, the independently established relation
   from that position/view to the particular observed contribution, plus
   the source evidence for whatever handler action actually removes it.

These are necessary distinctions, not a claim of a weakest sufficient
representation. Existing occurrence, profile, typed-path and evidence
labels are the first substrate; no missing compiler carrier is established.
The smallest useful static label is an annotation occurrence paired with
its typed effect position, retaining the component's concrete contract.
That label still needs a source correspondence to observations: it is not
itself event attribution, a capture grant, or a subtraction witness.

Typed-boundary §6 supplies a candidate correspondence once its profile is
given: a profile at position `p` follows matching typed `Flow` to an
event-specific `Observe(q,view,p0)`, joined with receipt of that same view.
Candidate incidence then checks the actual handler, owner and receiver's
activity under the same assignment. Its `Grant` clause additionally
requires the receiver-local profile to explicitly admit the operation.
Transport retains the source witness; family equality creates no path.

**Exact missing premise:** an admitted source annotation derivation must
map this particular `_ -> [io] _` occurrence to its applicable original
profile position and concrete permission, preserving scope and the local
boundary evidence. The approved answer requires this rule to be specified
and proved; the cited conditional package assumes the profile instead.
This note does not choose the position mapping, compatibility details,
grant/subtraction implementation, or how nested paths are formed.

In particular, “from `f`” is not defined here as lexical body origin.
Typed-core §§6, 9 and callback delivery §§3–4 retain the complete invocation,
including a Value-entry argument force. Caller-owned requests exposed
inside that executing view may have applicable observations. Classifying
those requests requires the missing profile mapping and existing typed
evidence; an origin-only shortcut is not justified by this analysis.

## Minimal symbolic discriminators and conditional consequence

Fix a shared, jointly well-formed `nu,K,D`. Supply any typed observation and
contribution premises independently. The following are proof obligations,
not asserted accepted programs or a complete effect-membership grammar.

| Case | Smallest observation envelope | Required distinction |
| --- | --- | --- |
| U: unannotated `f` | One nonempty `io` contribution at an applicable protected view | Absence of annotation supplies full protection; nonempty support is compatible with protection. |
| A: annotated `f` | One independently qualified `io` contribution at the annotated view | This contract permits removal; it does not establish that a removal action occurs. |
| O: outside the annotation | A qualified `io` contribution and a second `io` contribution at an unrelated view with no typed correspondence to this annotation | Permission for the first cannot be obtained for the second from family equality. |
| J: another effect | One separately admissible contribution of an effect distinct from `io`, without a separate permission | This annotation provides no removal permission for that effect. |

U and A each need only one contribution to expose their protection/permission
contrast; an empty envelope would hide it. For A, a source definition that
contains no established removal action supplies no removal witness. The
approved permission statement therefore cannot discharge an obligation
asserting actual consumption or reduced support. This does not claim that
both removed and unremoved executions are admitted by every completed
context; actual source actions and contracts still decide that question.

O needs two same-family observations to expose a classifier that erases
view/position distinctions. The second observation is outside the annotated
view, not merely a caller-origin request forced inside `f`'s complete view.
J is conditional on separate admission; this note does not assert that a
completed `[io]` Function contract admits arbitrary other effects from `f`.

Conditional consequence: if an admitted annotation derivation supplies the
profile mapping above, and the same original assignment supplies matching
typed transport, observation, receipt and any required live incidence, the
conditional typed-boundary rules can use that occurrence's concrete contract
at the matched position. This cannot derive applicability at an unrelated
position: the path premise is absent. Actual removal additionally requires
its own source handler/image evidence. The implication is an instantiation
of supplied rules, not a proof that raw source establishes their premises.

The symbolic mutants distinguished here are: full protection interpreted
as empty support (U); permission interpreted as guaranteed removal (A);
all `io` observations treated as sharing this annotation (O); and permission
extended to arbitrary effects (J). No mutations were executed or searched.

## Frame obligations and exact non-implications

Annotation checking exports its target, retaining the incoming realization
and predecessor evidence. It does not reconstruct unrelated coordinates
from the target's printed row. A completion must retain original assignment
sharing, predicate identity and `K,D` incidences, annotation/slot scope,
typed view/path correspondence, event/origin evidence, attachments and other
positions' protection. Existing Pure introduction and parameter-entry rules
remain in force. Endpoint export is an authorized change; evidence retention
does not mean that incoming and target endpoints are equal.

Permission formation itself supplies no observation, emission, dispatch,
consumption or support subtraction. For a later actual handler action,
event/image/support changes must follow that action's separate source rules;
the annotation is insufficient evidence for those changes. In particular,
the answer does not establish family-wide deletion, row-component
independence, portwise choice of assignments, arbitrary nested/latent
transport, or an unchanged complete handler image after consumption.

`'e?` has a separate approved local protection-release meaning with
independent attribution/crossing premises. This annotation permission is
not equated to that release operation, its crossing trigger or its lifetime.
Neither the draft notation nor §9's deep-handler example resolves this
annotation's missing source mapping. No syntax, operational semantics,
principal order, solver field or production route is selected here.

## Evidence, resources, omissions and next action

All semantic reads used `git show` at the pinned baseline; policy files were
read from the worktree. Commands inspected the two approved handoffs, their
questions, the source-annotation receipt, the design index, callback §§1–4,
compatibility §9, typed-core §§6–7 and 9, typed-boundary §6, and the notation
Draft. The formation receipt was absent at the baseline (`git show` exited
128); its live worktree version was not consumed. The primary owns bundle
validation, dependency revalidation and whitespace checks.

No independent Oracle, executable experiment, tests, builds, enumeration,
random seeds/ranges or performance samples were used. The symbolic cases
share the approved decisions and the supplied typed-evidence premises;
they expose missing implications without independently validating the source
rules. One lightweight command process at a time; no heavyweight process or
child agent. CPU/RAM and total wall-time usage were not measured.

No claim covers raw-source acceptance, complete profile generation,
exhaustive Function membership, handler image preservation, protection
lifetime, generalization/principality or production conformance. A failed
local annotation query prevents target export. An absent profile mapping,
unmatched typed path, incompatible assignment or missing source removal
witness prevents the corresponding conditional conclusion; no evidence is
added after comparison success to repair it.

Recommended next action: derive the single local source clause mapping
this `f` annotation occurrence to its original effect position/profile and
its `io` permission, with a proof of retained evidence and joint assignment.
If the governing sources do not determine that mapping, return the precise
alternative to the primary for a scoped design decision before a model or
implementation assumes it.

## Commit packet

- Exact leased path: `notes/progress/2026-10-05-annotation-scoped-effect-protection-boundary.md`.
- Baseline: `61a3651376166346a5baa03ec6679c310b0edbdb`.
- Dependency changes: none consumed; all semantic inputs pinned. Primary
  must revalidate relevant current dependencies before integration.
- Claim/review status: unreviewed bounded obligations and conditional
  consequence; no independent certification or closed source theorem.
- Checks run: bounded source reads and leased-path absence check only;
  output hashing reported in the worker return. No executable checks.
- Proposed message: `research: isolate annotation-scoped effect protection obligations`.
- Shared deltas left for the primary/curator: record the annotation-to-profile
  mapping obligation and exact non-implications in the Function formation
  gate; no task/index/theory/authority/question files edited.
