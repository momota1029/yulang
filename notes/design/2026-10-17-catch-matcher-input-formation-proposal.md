# Outside matcher input formation at `C_out`

Status: Draft; candidate source-definition proposal, independent review NOT RUN.
Scope: the complete ordered `MatchRequest_H` input telescope and entry
judgment after an actual source exit to `C_out`.
Approved drafting scope: option B, `CATCH-EXIT-INPUT-1`; no adoption.
Supersedes: none.
Author: `/root`, Luna primary; sole author.
Assignment: `CATCH-EXIT-INPUT-PROPOSAL-20261017`, handoff revision 1.
Contract: `source-formation-proposals-20261017`, revision 2, SHA-256
`97c39c74400e3da5c615eb9d784a993077c77244850687eeb60808d7a23a6a34`.
Source baseline: `601e55cfaaf131644d770006532727da33e33059`; current checkpoint is
recorded separately in `tasks/agent-loop/current.json`.

## 1. Parent and limit

The original `CATCH-EXIT-INPUT-1` and F1 source/native gates remain OPEN. F1
keeps its original complete source domain, finite typed graph, providers,
occurrences, worlds, contexts, guards, futures, continuations, interactions and
all Call quantifiers. FK1 retains its separate opaque-continuation quantifier.
FIRST-RESULT, H1/H2, JOINT_DEC, complete Call, effects, source-Generalize,
soundness, principality, F5 and production are independent OPEN gates.

The accepted source clause to be connected is:

```text
at C_y: original eligibility of q for H
actual source exit: thread the actual current state and leave H
at C_out, outside H: MatchRequest_H(q,raw) >>= Finish_H(q,raw)
```

This proposal specifies the *candidate input interface* for that existing
ordered matcher. It does not choose which arm succeeds, create a request or
raw handle, restore H, or prove that the current HIR/native path constructs the
input. The proposed input is formed before observing a match outcome. Thus
`NoArm`, false or mismatching guards, and suspended matching are inside the
judgment's domain.

This proposal is independent of the concurrent negative-formal-pair proposal.
Neither proposal assumes the other's adoption.

## 2. Ordered dependent operand telescope

The following telescope fixes dependency order. Notation after a semicolon is
in scope of the preceding fields; fields remain at their original dependent
indices rather than being copied into a new world.

```text
1. Γ0; original rigid/universal binders and source formation context
2. ξ = (ν,K,D); original joint history J_y; typed source graph Ω
3. H; its original ordered arm descriptor, lexical scope, and source owner
4. the actual operation declaration/occurrence op under H's source owner
5. the original current/yielding configuration C_y and source environment ρ_y
6. the actual provider, operation instance, payload carrier, and event origin
7. q : Event(op, provider, payload, C_y, J_y; original dependencies)
8. Δ_q : the complete dependent response and future interface of this q
9. raw : RawHandle(q, Δ_q; original captured environment and pending suffix)
10. Y_H : the original yielded-request derivation for (H,q,raw,C_y)
11. Elig_y : original eligibility evidence for q at H and C_y, when required
12. ε : the actual source exit consuming/leaving H from this yielded state
13. (C_out,J_out,ρ_out) : the actual post-exit state threaded by ε
14. M_exit : complete typed correspondence from original yielded ports to the
    original matcher input ports, including all dependent path/profile maps
15. X_out : current outside matcher owners, their current incidence/ownership,
    operation compatibility inputs, and current guard/pattern environments
16. A_H : the original matcher arm/binder/guard/body interfaces in source order
17. a : the original parent suffix at the output-dependent interface from
    (C_out,J_out), not a suffix reconstructed from printed value types
```

Field dependencies are intentionally explicit:

| Later field | Depends on | Required preservation |
|---|---|---|
| `q` | `op`, provider, payload, `C_y`, `J_y`, `ξ` | Same original emitted event, source origin and observation witnesses. No re-emission at `C_out`. |
| `Δ_q` | The original request typing and `q` | Complete response, admission and future interface for every originally admitted response. No chosen response is supplied at matcher entry. |
| `raw` | `q`, `Δ_q`, original capture and suffix | The same continuation handle, its captured environment and its whole pending computation. No call, reinstallation or `Int -> Int` replacement. |
| `Elig_y` | `q`, `H`, `C_y` and original scope/provider evidence | Historical eligibility remains indexed at `C_y`; it is not a transferable current grant. |
| `ε`, `C_out`, `J_out`, `ρ_out` | The actual yielded state and original exit rule | Use the state actually produced by the exit. Do not identify `C_y` and `C_out` or restore a saved configuration. |
| `M_exit` | `ε`, original typed paths, profiles, dependencies and source clause | Include every typed path and tagged witness needed at the matcher ports. An identity or empty profile is allowed only if the owning source derivation supplies it. |
| `X_out` | `C_out`, original owner/receiver relations and current context | Each candidate outside handler has its own current ownership/incidence evidence. Consumed H is not active merely because its old eligibility remains in the derivation. |
| `A_H`, `a` | Original source declaration and actual post-exit continuation | Keep ordered patterns, guards and body interfaces, plus the parent suffix's real dependent input. |

The telescope carries all original `χ`/`D` profiles, family/type arguments,
provider identities, residual and lineage tags, observations, receipts, entry
and exit evidence, and shared `ν/K/D/J` dependencies that occur in the
original typed graph. It does not discard fields merely because the printed
value skeleton is `Int`, or because a native observer exposes fewer fields.
No source existential is moved; no rigid binder becomes internal to the
matcher.

The complete response schema `Δ_q` remains available for the original later
`τ=(r,C_resume,η)` admissions and their `Future(r)`. Entry formation neither
chooses `r` nor quantifies over a narrowed response set. The original raw
continuation is not replaced by a constant return or specialized to the
selected specimen's visible argument.

## 3. Proposed input judgment and introduction premises

Let `TypedMatchInput_H(𝒯_H)` name the judgment that the entire ordered
telescope above inhabits the original matcher/binder ports. It is a proposed
judgment, not an abbreviation for successful matching and not a source
constructor already established by the current implementation.

**MI-Intro (candidate source rule).** The candidate introduction rule has the
following ordered premises:

1. Original source typing of H's declaration, arm order, patterns, guards,
   binder scopes and body interfaces at their original source occurrences.
2. Original typing of `op` and its provider/payload, and formation of the same
   emitted event `q` at `C_y`, including its original observation and
   dependencies.
3. Formation of `Δ_q` and the same `raw` handle for that request, with its
   entire response, admission and future interface.
4. The original yield derivation `Y_H` and, where the existing matcher clause
   uses it, `Elig_y` at `C_y`.
5. The actual exit derivation `ε` from the yielded state to `C_out`, threading
   its actual configuration, environment and joint history.
6. A source-derived `M_exit` that types the complete original dependent
   operands at their actual matcher input ports. It must be supplied by the
   owning original source/transition formation rule, or by a separately
   approved source definition. Scalar endpoint equality, a stored record,
   archival packaging, parser identity, or successful lookup does not supply
   this premise.
7. Original typing of the outside matcher continuation `a` at the resulting
   output-dependent interface.

Conclusion: `TypedMatchInput_H(𝒯_H)` at the actual `C_out`, with `q` and `raw`
unchanged. Premises 1–5 construct the historical inputs and actual exit;
premise 6 is the still-missing source bridge called `CATCH-EXIT-INPUT-1`.
Stating it in the rule identifies the proof obligation and its owner; it does
not claim that current source rules discharge it. The proposal therefore does
not turn an assumed map into a theorem.

The corresponding candidate matcher entry is:

```text
TypedMatchInput_H(𝒯_H)
-----------------------------------------------
MatchEntry_H(q, raw, C_out, J_out, X_out, A_H; a)
```

`MatchEntry_H` is available before matching begins. Its domain includes every
input that satisfies the original entry typing even when its eventual ordered
matcher outcome is `NoArm`, false/mismatching guard, suspended, or selected.
Successful matching is not a premise of `MI-Intro` or `MatchEntry_H`.

## 4. Proposed eliminations and branch preservation

Eliminating `MatchEntry_H` exposes the original ordered matcher computation
with the unchanged `(q,raw)` and actual `C_out`. Its result must be one of the
outcomes admitted by the original matcher clause:

| Original outcome | Required elimination behavior |
|---|---|
| `Selected(i, witnesses)` | Use the original match/compatibility witnesses and the actual current guard result for arm `i`; bind the same whole request/raw operands at their typed arm ports. No historical H activation is restored. |
| `NoArm` | Preserve the original no-arm/exhaustion path, including its actual forwarding/re-entry behavior where the source clause supplies it. No identity-forward transition is invented. |
| `GuardFalse(i)` or mismatch | Continue through the original ordered matcher/guard rule with its actual current state and pending suffix. False is the source guard's outcome, not negation of an unknown native predicate. |
| `Suspended(s)` | Retain the actual pending matcher/selector/guard frame `s`, remaining arm order, same `q/raw`, `C_out`, joint history, dependent evidence and output interface. Do not publish a successful arm or discard the suspended suffix. |

The exact sum tags and ordering belong to the existing matcher definition. This
proposal requires the matcher to retain these distinctions; it does not assign
new meanings to them. For an effectful selector or guard, the original request
or pending rule applies at that phase. No unresolved selector is treated as a
false guard or as `NoArm` without the original premise.

The consumed handler's former eligibility remains a historical derivation at
`C_y`. At `C_out`, it contributes no live incidence for H. Any outside handler
must use its own current owner, receiver, provider and receipt evidence. The
matcher cannot turn the old q observation into a fresh observation under a
new view, nor cast H's current-incidence conjunct across the exit.

After `MatchEntry_H` is established, the existing `Finish_H(q,raw)` clause
continues with its original selected, no-arm, false/mismatch and suspended
behavior. `raw` retains its complete suffix for every originally admitted
response. In particular, the visible specimen's selected `id` argument does
not specialize the raw interface before that argument's actual Call entry and
admission.

## 5. Native producer/consumer map and exact missing bridge

The following map is conditional design guidance from the pinned constructor
audit. It is not evidence that native code currently creates this telescope.

| Owner | Existing producer/consumer role | Required correspondence still open |
|---|---|---|
| `local_source::Builder::catch` | Retains Catch, arm/body and continuation-binder source identities and lexical scope. | Original typing of the complete request-to-outside-matcher tuple. |
| `candidate_source::Work::CatchArms` and `Action::CatchOperation` | Carry owner, declaration, arm-body occurrence, continuation endpoint and original scrutinee-related ports. | Actual exit, `C_y -> C_out`, and full dependent matcher input ports. |
| `candidate_effect::candidate_catch_operation` | Forms the declaration environment and response/continuation Function constraints. | Dynamic q/raw, original observations/receipts, whole dependent profiles and the matcher entry introduction. |
| `candidate_context::candidate_function_port_admit` | Transports an already formed relation context through argument/result positions. | It cannot invent the missing source introduction or supply a complete source exit map. |
| `candidate_context::candidate_context_execute_relation` | Executes current relation/filter evidence and may retain a scoped observation. | Its current scoped observation is not automatically q's original event/view/receipt/exit tuple. |
| Existing `MatchRequest_H` / `Finish_H` clause | Defines ordered matching and its continuation at the source level. | Its complete typed operand telescope and source-derived entry judgment at `C_out`. |

The first useful implementation task, after a reviewed and explicitly adopted
definition plus a new exact lease, is to trace the actual `Builder::catch` →
`Work::CatchArms` → `Action::CatchOperation` → `candidate_catch_operation`
path for an already retained typed-entry certificate. If none exists, report
that absence. Do not reconstruct it from successful matches, Function endpoint
equality, zero conflicts, parser spelling, or a source-call lookup. Any new
stored field or producer rule needs its own source authority, proof and review.

## 6. Proof obligations, falsifiers and status

The candidate definition leaves these precise proof/implementation premises:

- **CPI-1:** derive a complete ordered matcher telescope from the original
  source/transition clauses, including all field dependencies and each
  field's authentic owner.
- **CPI-2:** prove `M_exit` from the actual yielded request and exit for the
  original source domain; preserve tagged paths, `χ/D`, providers, residuals,
  observations, receipts, scopes and current configuration.
- **CPI-3:** retain the same q/raw and full `Δ_q`/future contract without a new
  emission, admission, response choice or handler activation.
- **CPI-4:** show `C_y` eligibility is historical and `C_out` current
  ownership/incidence is checked only for active outside candidates.
- **CPI-5:** cover every original matcher branch: selected, NoArm, false or
  mismatching guards, and suspension. No successful-match-defined domain.
- **CPI-6:** bridge each source input and output to real native producers and
  consumers without treating current Function rows or observations as a
  complete source typing derivation.

Exact falsifiers include: an input incidence without an original tagged source
path; replacing q, provider or raw; moving historical eligibility into live
`C_out` incidence; changing `C_y` to `C_out` without the actual exit; dropping
one dependency/profile/receipt; choosing an empty profile without its source
typing; specializing `raw` to the successful specimen; defining the domain by
Selected; dropping NoArm/false/suspended cases; or using a successful runtime
observation as source formation evidence.

This proposal makes no source-qualified counterexample claim, proves no
transition, and selects no representation. Independent review and later
explicit user approval are required before adoption. Until then,
`CATCH-EXIT-INPUT-1`, the original F1/FK1 and all dependent proof, native and
production gates remain OPEN. The unrelated negative-pair proposal's review or
adoption cannot close any of these gates.

## 7. Pinned proposal inputs

The active sprint contract contains the complete direct dependency manifest.
The direct input hashes used here are:

```text
ea0b96693114f9cbe9c8e6306b4dcff6fd522baef2c9076277de1a33801a2936 notes/theory/2026-10-17-catch-matcher-input-constructor.md
1e955d4bd3aa33a616370763cb98b42a0d5201306b66d9ca7680e3ae9fa5d933 tasks/agent-loop/inbox/20261017-catch-matcher-input-constructor.md
a1929f54e77335c413cc20230100bc9cad4d98bec4b51f6464db39417a07d63e notes/design/2026-10-16-primitive-interaction-graph-proposal-r2.md
3a0bf3df4657dd0a6ccbb8690d990177ff19f30e10e91c93839b4601c634f61b notes/theory/2026-10-16-parameterized-shallow-image-finite-presentation.md
f963405835082252abbbc54381bf08fdb6a760cf508ae34416d7960fe0a2e729 notes/theory/2026-10-16-primitive-interaction-graph-a2-r2-withdrawal.md
343c3713a05418560888122c0c0d54358b45cc3c484b6cf0048baf16b75c58b7 questions/2026-10-17-catch-exit-matcher-input-formation/question.md
7e345361af200585fee97ae39642ef1c97069b4170c987066d25ee13e9a1a846 questions/2026-10-17-catch-exit-matcher-input-formation/receipt.md
655748936460bac40f757962552fd339320ebeeb583029afdc3d359b24d67108 questions/2026-10-17-catch-exit-matcher-input-formation/approved-answer.md
```
