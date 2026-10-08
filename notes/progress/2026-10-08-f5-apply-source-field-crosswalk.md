# One F5 Apply candidate-to-source field crosswalk

Date: 2026-10-08
Baseline: `9bc2c5353a4c48d6bfcd0116fb8ae77402a7fdc7`
Branch: `research/simple-sub-intrusion`
Status: bounded read-only static correspondence
Claim class: structural source incidence and missing producer characterization
Authority: none; no implementation or cutover gate closed

## Frozen occurrence

Use the inner `f x` in `my apply f = { my step x = f x; step }` through the
opt-in `lower_module_with_shadow_local_binding` path and
`CandidateValueObservation::solve`. Let `c` be the Apply occurrence, `u_f` and
`u_x` its callee/argument Name occurrences, and `d_f`/`d_x` their outer/inner
formal declarations. Shadow HIR checks those exact resolutions and capture
ownership. The candidate recipe records `Apply { callee: Parameter(p_f),
argument: Parameter(p_x), result: call.value }`.

For the actual session allocation, define `P_f` and `P_x` as the live rows
assigned to those parameter recipe positions, `R_c` as the call value row and
`S_c` as the call effect row. Candidate endpoint construction creates
polarized Terms over these rows. This is a static owner trace; no runtime IDs
or solver execution are asserted.

## Field-by-field mapping

| Selected source object | Candidate object | Correspondence status |
|---|---|---|
| Original Apply/callee/argument incidence and lexical owners | Exact HIR occurrences, resolutions, and recipe positions | Present structurally; does not establish source typing. |
| `A_f`, the captured outer formal endpoint | Positive live row `P_f` used as the callee Term | Row identity is shared correctly; interpreted environment, complete value descriptor, provider and world evidence are absent. |
| `A_x`, the inner input endpoint | Positive live row `P_x` | Structural approximation; no independently interpreted whole input contract. |
| Complete `J_f` and `J_x` Name-return images | Parameter references and pure-bounded occurrence effects | Absent; no original-environment Return image or its evidence is constructed. |
| Complete dependent `F_c` at original `R_f` | Negative Function Term over `P_x`, pure-effect constants and negative `R_c` | Four-port skeleton only; no dependent telescope, source root `R_f`, or `WF_Dec(F_c;xi)`. |
| Call result `A_c` | Shared value row `R_c` | Structural connection only; semantic result/provider evidence is absent. |
| Invocation effect `E_c` | Separate row `S_c` with pure lower/upper constraints | Structural approximation under unresolved candidate pure model; not tied to a complete invocation image. |
| `VIncl(A_f,F_c;xi,e_value)` | Admitted structural fact `t_f <: t_D` with occurrence/cause/fact provenance | Missing as semantic inclusion evidence. Store admission provenance proves only structural fact admission. |
| Whole argument compatibility | Structural argument port `P_x` | Missing complete `J_x`, `CarrierContract(F_c)`, shared-provider compatibility and evidence. |
| Complete callable execution containment | Row propagation and pure call-effect bounds | Missing `ExecuteCallableImage`, complete event/consumer envelope and containment certificate. |
| `TypedCallCert_Dec`, role and Gen-Call-0 outputs | Candidate identifiers and unresolved-premise list | Missing original profile/root/role/receipt/incidence package. |

The candidate's Apply identity and structural fact/provenance survive in its
private observation, while its semantic premises remain explicitly
unresolved. Neither `SolvedModule` publication nor structural Function
generalization turns these rows into the source objects above.

## Exact source scope and first missing producer

The selected source construction for this component fixes one original
`xi=(nu,K,D)`, shared captured formal `A_f`, both complete Name-return images,
and a dependent `F_c` at `R_f`. It then requires `WF_Dec(F_c)`, `VIncl`, whole
argument/provider compatibility, complete callable execution-image
containment, and a typed-call certificate. Typed-core `VIncl` is defined over
the same decorated values; it is not row inclusion.

The first missing candidate input is the interpreted environment and shared
`xi` needed before treating the callee row as source `A_f`. Conditional on
those source inputs, the first missing Call-produced object is the complete
dependent `F_c` at `R_f`; the negative Function Term supplies only its
structural shape.

Next falsifiable producer question: does any pre-admission owner for this
exact `c` construct and retain a complete `F_c` at the same captured-formal
root and original scope, together with the interpreted-environment dependency
and Gen-Call-0 incidence, independently of solving `t_f <: t_D`? A positive
answer must identify the concrete producer and transfer path.

## Scope and omissions

Inspected the exact shadow local-binding source join, HIR occurrence minting,
candidate preflight/recipe/allocation, session live-row allocation, candidate
Term and fact construction, candidate result retention, selected source Call
construction, and typed-core comparison definition.

This does not establish production conformance, all-source supplier absence,
natural inference completeness, principality, or F5 cutover readiness. No
compiler code, tests, builds, probes, measurements or Git operations were
performed during the trace.
