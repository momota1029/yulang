# R21: independent soundness attacks on field-root bridges

Status: FROZEN research-only adversarial analysis, revision 1; independent review pending. No bridge is adopted or proved sound here.
Author: `/root/r21_bridge_falsifiers`, sole author, no descendants.
Baseline: primary-pinned `d2ff62845`; exact dependencies and resource receipt are in the companion handoff.
Parent: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`, OPEN; original conditions closed **0**.

## Objective, method, and limits

This independently attacks the two options specified by the frozen R21 contract: A retains the successful local annotation derivation and exact initializer provenance; B exposes an independent annotation presentation and constructs realization through the actual response use and continuation result. It audits those specifications, not another author's unfinished proposal. Combined consistency with the eventual rule and implementation documents requires the assigned fresh reviewer.

The method is manual source-equation analysis plus small semantic/provenance countermodels. There is no executable model, no assumed-transition checker, no test or build, and no newly verified source admission. The countermodels refute explicitly stated overstrong *candidate rules*; they are not source-qualified counterexamples to the parent theorem. Source mutations and their admission status are detailed in the companion falsifier note.

The governing accepted meanings are R6's distinct request owner `c`, callback realizer `c_outer`, q license, retained exact `h_arg`, and native `AnnotationMember`/`Allowance`; R20's distinct `L`, `A-`, `A+`, `R_response`, response FreshUse `S`, `R_ping`, `R_k`, and `R_catch`; the top-level principles §§1–3; and complete source Call §§2–4. This note neither reselects those meanings nor treats annotations as runtime executions.

## Derivation that either option must respect

At the annotation owner, the existing links are:

```text
L <: A-                     exact initializer check
A+ <: R_response            independently exposed positive annotation
Install(response) = R_response
```

These premises alone do not yield `L=A+`, nor provenance equality of their members. `candidate_signature_effect` constructs Support on a positive annotation presentation and Allowance on a negative one. A positive presentation member has that annotation's origin; it does not become the callback operation's member merely because family and ordinal match. R20 identified the missing typed incidence precisely here.

At the resumption and Catch owners, ordinary checking gives the actual response argument check and result constraints. For a direct request, the raw saved source suffix can be an identity on values; this is a value/provenance fact requiring its source interface, not an equality of the argument and result type endpoints. Catch's output follows the actual arm body's final result. The matcher establishing `h_arg` merely finds the unique resolved `k response` Apply anywhere inside that arm; it does not assert that this Apply supplies the arm's final result.

A useful indexed form of the required evidence is:

```text
FieldAt(presentation-root, owner, initializer-derivation,
        field-position, source-realizer, native-member, license)
UseField(exact-capture, exact-context-use, mapped-field-coordinates)
ResultField(actual-output-provider, actual-result-interface, field-evidence)
```

These are requirements for a proposal's typed evidence, not new adopted judgments. Deriving the third requires the actual result-producing case. It cannot be inferred from existence of the first two alone.

## Minimal result-discard countermodel

Take distinct callback values `a` and `b`, with different source realizer identities `ma` and `mb` and compatible annotated Function types. Let the direct raw continuation be `K(x)=x`. Let the selected handler arm evaluate `K(a)` and then return `b`:

```text
arm(a,b) = let ignored = K(a) in b
Catch-result = b
```

The response argument is genuinely `a`; its exact resumption genuinely returns `a`; nevertheless the arm and Catch result are `b`. Thus the proposed implication

```text
FieldAt(a,ma) and exact h_arg(k,a) => FieldAt(Catch-result,ma)
```

is false as a general provenance rule. Its two premises leave the arm's result unconstrained. In this model the correct final incidence is that of `b`, when separately supplied; the rule cannot borrow `ma`. Choosing `b` with no operation realization additionally blocks manufacture of that lower field. A type effect overapproximation may still contain the same allowed family, so this argument establishes an evidence/provenance error; it does not by itself establish ordinary type unsoundness.

This is a smallest structural discriminator: one request, one exact resumed argument, and one discarded intermediate result. No competing request, repeated use, handler shadowing, or recursive source is needed. A compatible source candidate using the pinned matcher's direct scrutinee is given in the companion note; it was not executed.

A different countermodel concerns the *saved suffix*, rather than the handler arm. For `K(x)=b`, the call result is `b` even before arm finishing; for `K(x)=0` the result is not a callback. The source Call contract preserves actual returned-provider and future interfaces, so neither case licenses a field of `a` at the result. These general contexts are outside the current v1 direct-scrutinee matcher and remain hypothetical/original-open, not current v1 source counterexamples. Divergent/nonreturning K produces no completed result incidence at all.

Syntactic finality is not the repair. `let tmp=K(a) in tmp` forwards the value through a genuine local Install/capture/FreshUse; a rule must derive that route when applicable. `let tmp=K(a) in b` does not forward it. Both contain the same nonfinal K Apply, so a final-Apply test cannot distinguish their semantics. The positive and negative controls are specified in the companion source note.

## Option A audit

A's retained successful check gives a natural owner for the relation between the initializer and its exposed annotation. It can distinguish equal-looking annotations on different local definitions if its evidence records the actual definition, initializer root, comparison occurrence and complete Function-field derivation. It must also retain variance/path, composed polarity, annotation scope, license and q owner. Merely recording the boolean success of `L <: A-` proves none of these associations.

A is refuted if it exports any old member that fits the annotation, uses annotation structural equality as initializer identity, or injects the member as a new lower without a sound source rule. In particular the annotation-positive Support is not m0. A faithful retained derivation may establish a typed realization relation without adding an equality or stronger lower; preservation of accepted assignments under any new generated constraints still needs proof.

Retaining the initializer comparison addresses only the annotation seam. A must also provide actual response FreshUse evidence and the complete result cases above. If it chains directly from a successful response check through `h_arg` to installed g, the result-discard model refutes that chain. A's retained check is not permission to bypass Call or Catch.

## Option B audit

B correctly keeps the response presentation separate from the initializer. This prevents an automatic endpoint equality, but independence is not a source-realization proof. It must construct a relation from the actual callback initializer/member to that independent presentation using an owner-produced typed derivation. Giving the presentation a field licensed only by its own annotation cannot establish that it realizes the original m0. If B needs exactly the missing incidence as an input, it has renamed the premise without discharging it.

B's use/result construction must retain the exact response capture and `context_use`, all mapped typed coordinates, continuation's actual output provider, complete result/future interface, and arm/Catch value case. Returning the response, returning a different provider, discarding it, and nonreturning behavior are different cases. A union of possible result alternatives may retain separate conditional incidences; it cannot give every alternative an unconditional field from the response.

Both options can remain compatible with ordinary source behavior by making certificate derivation accurately reflect each result. Failure to derive the selected field for a discarded-response case must not silently reject otherwise supported source programs or remove those cases from the original theorem. The remaining parent proof must handle the actual result alternative.

## Two uses, shared anchors, and scope

For successful uses u1 and u2, `begin_use` produces distinct `context_use` values. Let phi1 and phi2 be their actual graph maps. A field task for u2 must name phi2's node-indexed member, upper allowance, negative port/root, relevant scopes, relation, actual emitted bound/task, and matching terminal acknowledgement. Consumed evidence for u1 cannot discharge u2, even if some or all old nongeneric row coordinates coincide. Distinct use identity does not require disjoint row identities.

Conversely, a bridge that insists every coordinate become fresh rejects a legitimate shared anchor: `prepare_candidate_fresh_use` keeps old/nongeneric rows and canonicalizes aliases. Copying such anchors solely to simplify evidence changes the ordinary algorithm and cannot be justified by this packet.

Source ownership, declaration/field/license positions and retained h_arg remain fixed source indices; eligible native graph/view/context coordinates follow their actual maps. Scope changes require the real scope/input/root map and license action. Equal effect families across scopes do not supply that action. Ordinary operation-v1 uses `scoped_experiment=false`; its default empty map is no evidence for the original all-scope claim.

## Obligations before adoption or implementation

| Obligation | Required argument | Failure condition |
| --- | --- | --- |
| Soundness of annotation bridge | Source typing plus exact field/provenance constructor preserves accepted assignments; any extra constraint is entailed at its real owner. | Success/family membership manufactures a lower, endpoint equality, or foreign initializer field. |
| Soundness of result bridge | Case derivation follows actual continuation result, provider/future interface, final arm value, Catch root and installed local. | Discarded argument or intermediate result receives unconditional final incidence. |
| Principality | Every old admissible typing extends to new evidence; any new constraint is implied by old semantics. Erasure/reflection and substitutions respect the same old solutions. | Only one chosen callback/provider/annotation witness is retained as a restriction; old solutions are pruned without a semantic reason. |
| Complete Call | Callee, whole argument, entry/return effects, actual output provider, world/scope, future/dependent result and original alternatives remain correlated. | Response argument is substituted for returned provider, or J1/J2/entry/return rows collapse. |
| Termination/resources | Finite source/evidence graph, memoized owner/field/use keys, monotone work with existing terminating solver measure or a separately proved extension. | Recursive Call/FreshUse unfolds proofs indefinitely, generated use identities feed fresh instantiation, or duplicate edges regenerate tasks. |
| Publication/conflict | Provisional evidence becomes consumable only after its required checks and exact drain succeed; later invalidation cannot publish it. | Local comparison success publishes globally despite later typing conflict, missing result case, resource failure or wrong acknowledgement. |

No general theorem in this table is proved here. In particular, finiteness of a source graph alone does not prove solver termination when a rule can create unbounded fresh evidence. Full rollback is not assumed: safe private discard or stopping remains consistent with the top-level principles, provided inconsistent partial evidence is never published.

## Parent application and recommended next action

The contribution is a discriminating result-case obligation and explicit rejected inference rules, not original theorem closure. A and B both remain candidate rule families; neither specification alone derives both R20 seams. The next useful action is for the assigned independent reviewer to check the frozen concrete rules against the arm-discard witness, then require the rule author to derive the exact actual final-result case rather than assuming a response-to-Catch field link. This is complementary falsification; the constructive proof remains the prover's responsibility.
