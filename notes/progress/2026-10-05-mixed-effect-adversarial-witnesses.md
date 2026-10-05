# Mixed effect descriptor bridge: adversarial witnesses

Date: 2026-10-05
Status: independently reviewed research-only countermodels and conditional source derivation
Scope: shortcuts involving joint witness existence, support union, and one-event removal; no descriptor membership rule or production policy
Baseline: `a38e79e6157f641674103073ce1527831d3480eb`
Independent review: compiler_referee; no findings in the bounded review scope; source annotation adequacy, general membership and full production containment remain unverified

## Authority and duplication boundary

The governing inputs are [concrete compatibility](../design/2026-10-03-concrete-compatibility-boundary.md) §§6–9, [source-indexed callback realization](../design/2026-10-04-source-indexed-callback-realization.md) §§2–4,7, [ordinary computation semantics](../design/2026-10-02-ordinary-computation-semantics-package.md) §§4,7 and its §5 handler equations, and approved [mixed-row answer d1](../../questions/2026-10-05-function-effect-row-denotation/approved-answer.md). All reads used the baseline version.

The existing probes were inspected before choosing the method:

| Existing artifact | Already discriminated premise | Treatment here |
| --- | --- | --- |
| [component membership](2026-10-05-effect-component-membership-playground.md), `research_effect_component_membership.py` | Equal family/type support does not establish typed path/current capture incidence; origin equality is an invalid extra condition. | Reuse its distinction in a factorization argument; no new enumeration. |
| [attachment subtraction](2026-10-05-effect-attachment-subtraction-playground.md), `research_effect_attachment_subtraction.py` | An attached, consumed event can coexist with another same-point output event. | Reuse the support condition; no new flag matrix. |
| `research_mixed_effect_subtraction.py` | A selected shallow event disappears while a distinct same-family raw-suffix event survives. | Do not reproduce its 96 histories. Use an outside arm of the derived deep expansion instead. |

The new countermodel below attacks joint existence of component witnesses. The other sections extract the exact lost premise from existing witnesses or ground it in a different source transition. They are not additional probe-count evidence.

## 1. Separately satisfiable views need not have a joint witness

Fix one original nonempty relation fiber `R = Rel_C(nu,K,D)`. Let `z` be a shared witness coordinate retained by two component views at its original scope. It is not a separately instantiated type variable or a projected concrete data value. For the countermodel, it can name two alternatives of a shared typed correspondence witness. Fix `nu`; fix `K = true`; fix `D` to retain the same `z` in both views. No component changes these coordinates or their scopes.

Take the finite model:

```text
R = {w_left, w_right}
z(w_left) = left;  z(w_right) = right
A(w) iff z(w) = left
C(w) iff z(w) = right
```

Thus `R_A = {w_left}` and `R_C = {w_right}` are both nonempty, but `R_A ∩ R_C = ∅`. The original fiber is nonempty. Each candidate subview is satisfiable under the same fixed `nu,K,D`. The failure is their incompatible requirements on the one shared witness, not different type assignments or empty `Rel_C`.

The proposed shortcut changes

```text
exists z. (R(z) and A(z) and C(z))
```

into

```text
(exists z. R(z) and A(z)) and (exists z. R(z) and C(z)).
```

The latter is true and the former false. Renaming the two local binders does not repair the shortcut; it demonstrates the loss of the shared original witness. The source-indexed realization §2 explicitly binds a witness shared by two segments once around their joint formula.

This two-point model is minimal for this form of failure: on a singleton relation, any two nonempty subsets intersect. It refutes the unrestricted logical implication only. It does not assert that a particular Yulang mixed annotation generates these predicates. The still-open source component clause must show how its actual predicates satisfy the joint requirement. Independent marginal nonemptiness cannot supply that proof, and joint emptiness cannot be used as acceptance evidence.

## 2. Support union cannot certify a nonconstant retained obligation

Let `S(w)` project a complete decorated observation to family/type support. An exact retained obligation `P(w)` can be represented by a predicate on support alone only if it is constant on each projection fiber:

```text
S(u) = S(v) implies P(u) = P(v).
```

Necessity follows immediately from any proposed factorization `P = Q ∘ S`. For sufficiency, on the projection image define `Q(s) = P(w)` for any `w` with `S(w)=s`; constancy makes the definition independent of the representative. This is a set-theoretic criterion, not a descriptor elaboration rule.

The existing component-membership probe supplies a two-record witness to failure of this criterion for capture incidence. Keep family `write`, argument `int`, and the same fixed `nu,K,D`:

| Coordinate | `u` | `v` |
| --- | --- | --- |
| Support | `{write int}` | `{write int}` |
| Exact concrete callback contract | present | present |
| Observed typed port and path | matching | matching |
| Receiver activation | active | active |
| Selected handler activation | active | absent |
| Current event capture incidence | established | absent |

Each record has its own decorated configuration. The table does not claim both activation states hold in one configuration. It does not infer an exact event-origin filter. Ordinary semantics §4 ends incidence with the activation, so this is the named predicate already checked in the existing finite model.

Give both records the same abstract allowance and the same concrete support allowance. Their support unions agree; their incidence obligations differ. Therefore a support-union calculation that discards the original configuration/incidence cannot certify this retained obligation. The same issue applies whenever a required original occurrence or attachment predicate is nonconstant on a support fiber; that predicate must be retained or independently proved to factor. No assertion is made that every concrete component has one particular occurrence filter.

This rejects using union as the complete satisfaction/evidence rule. It leaves the conditional support upper bound intact: if the argument and every reached body/result-consumer contribution are bounded on the actual state-threaded joint relation, their support lies within the union of those bounds. Flattening a covariant allowance is also compatible with preserving the obligations separately in existing evidence. The countermodel does not require a new row tree or carrier.

## 3. One attached deep-handler event does not imply family absence

The attachment probe already shows the projection failure abstractly. A source-equation specialization demonstrates why the derived deep form alone does not remove the absent-output premise.

Assume a single input request `q0 : write int` has the exact source-supported eligibility and attachment needed for selection. Its handler arm is schematic source computation:

```text
selected write arm(q0, raw k):
    perform write int            // fresh dynamic event q_arm
    return unit                  // raw k is not used
```

Take pure accepting selection and a current outer context with no handler that consumes `q_arm`. This is an assumed source setup, not inferred from a row annotation. Apply the derived deep expansion `D_H` of ordinary semantics §5. It transforms the supplied `k` into a wrapped continuation, but this arm never calls it. The primitive shallow image still runs the selected arm outside the candidate. Thus `q_arm` reaches the outer context with its own current configuration, identity, origin and typed evidence. No expired incidence is copied to it.

The input `q0` is selected and does not itself become an outward request; the complete image has `q_arm`. Both support points are `write int`, so the output support still contains `write int`. Exact attachment for `q0` and derived deep reapplication are both compatible with this result. This is the two-event minimum for an event being selected while a distinct same-point event supplies outward support. It uses arm emission, not a surviving raw suffix.

This conditional derivation attacks the shortcut “one attached contribution selected in a deep form implies the support point disappears.” It does not contradict the approved targeted-removal fragment: the removal of the targeted contribution and absence of the entire family/type point are different statements. A claim of the latter needs

```text
for every complete output observation w:
    no outward event q in w has support point write int.
```

The complete observation includes selector/arm effects, all resumptions, latent results and later uses. This example supplies one finite output prefix violating that universal condition. Proving that the illustrated annotation admits or excludes this arm belongs to the missing source-to-descriptor clause; this note supplies no annotation typing rule.

## Checks, frozen inputs, and handoff

Method: direct finite-set reasoning plus one conditional unfolding of the selected handler equation. No executable artifact was needed. Each proposed unrestricted shortcut stops at its first witness; no larger search was run.

Checks: baseline sections and all three existing probe sources were read; the two-point intersection, support-factorization argument, and arm-emission prefix were manually derived. `git diff --no-index --check -- /dev/null notes/progress/2026-10-05-mixed-effect-adversarial-witnesses.md` emitted no whitespace diagnostics (exit 1 denotes the new-file difference). These are producer checks, not independent review. No compiler tests/builds, probe reruns, performance measurements, or parallel compute were performed. Runtime experiment processes: zero; measurement samples: zero. Source adequacy, general descriptor membership, full handler-image preservation, soundness/principality, and production containment remain unverified.

Frozen dependency Git blob IDs at the baseline:

| Input | Blob |
| --- | --- |
| Concrete compatibility | `07e2c58a928540c730dd67e74f2e65161ea6a9b5` |
| Source-indexed callback realization | `6f412b19dd91b4a32aa2421d2668ac2203dc6ed2` |
| Ordinary computation semantics | `640bbfa85630d1dd496a3fd1ccb757536385d720` |
| Approved mixed-row answer | `77e28d7826634421a98e556a0023b29c762420ad` |
| Component-membership note / checker | `fd3b4fea304a43c0bdceb68fb9af3feca7a92c90` / `1bed9254bb1be14760df142639480759be7f284d` |
| Attachment-subtraction note / checker | `15ccc59ef531e4c5e84fe4e41cdb36d7b321ecb4` / `2682423938b22f62f372aca8cf0abd376ad341f5` |
| Shallow-resumption checker | `aac1388c49abd585b818395a0b23b09e6ca00e2f` |

Only this note is within the output lease. No compiler, authoritative source, question bundle, or shared task/index/theory record was changed. The next useful bridge proof must construct the actual joint component predicate over the original witness scope, preserve its incidence/attachment obligations through flattening, and prove complete-output absence for each claimed support removal. These are proof premises, not proposed production policy. Primary-owned record synchronization and independent review remain deferred to integration.
