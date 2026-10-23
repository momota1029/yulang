# R340 — K0 machine source census and proof dependency record

**Status:** primary source census in progress; R340 remains ACTIVE. This note
records source correspondence and the dependency seams from the user-directed
whole-proof audit. It is not the constructive proof, an independent review, or
a promotion of any parent theorem.

## Fixed authority and evidence

Governing audit:
`docs/Yulang Simple-sub 拡張：全体証明への移行監査・証明設計.md`, SHA-256
`b720fc938423bea1b677f7121653e2452b0fb0b9bb2919e9d38c7fccbee64895`.
Its domain is ordinary K0 and its first whole target is S0. R340 is one bounded
D3/M control-and-identity supplier; it does not replace G, the rest of M, or
S0. The original Yulang2/Simple-sub A/B and catalog goal is unchanged.

R340 contract revision 1 SHA-256:
`5de2605641bc28bdea416be1d7eea69a0bff4a689d39b33a2c2738b23cc7642c`.
R339 reviewed D3 note SHA-256:
`4301ed7e184915e75646809102a477f8d4b27f874478e364c03886ae1cfd2666`.
R339 outcome SHA-256:
`07abaf5ee285917a4f49ce94fbf287b115dfcdbd20f8275bdcb6bcc3acec0701`.

The R340 source census checked these exact bytes:

| Source | SHA-256 |
| --- | --- |
| `tools/inference-playground/src/runtime/program.rs` | `df58f9a1d60e39fafe6d85b1e50331b35fde2a9142a2eaea84ad028d3048fdb0` |
| `tools/inference-playground/src/runtime/machine.rs` | `02adc26bcd58cca488a40e78289a264751146d7900c2897db19068b279a8d840` |
| `tools/inference-playground/src/runtime/dispatch.rs` | `f45057373f2ed3a7b6ce915611db093015fb93cdb05984a5e3b23cfd44720873` |
| `tools/inference-playground/src/runtime/receiving.rs` | `2170a3bcbc6710ce3fbf721a05129117f8266b9ecf21c67136db918815303551` |
| `tools/inference-playground/src/runtime/literal.rs` | `2fff177a7ba0cabb4930251e1facc8f9be701ff3ec7baa695ce4c182fa1da35f` |

No compiler source or test was changed or run for this census. The audit itself
remains user-owned and untracked.

## Authentic K0 Apply to machine handoff

The source domain is the audit §4 and R336 rev4 `ValidK0`: one authentic,
nonrecursive definition, ordinary candidate mode, a selected-definition
runtime entry, and only the admitted literal, parameter Name, simple Value
Lambda, Apply, else-complete If, Group and binding-free Block/StatementBlock
forms. It excludes annotations, local bindings, Comp formals, operations,
handlers, Case, member/role/FieldTail and operator dispatch. This is a source
domain premise, not a claim about arbitrary `RuntimeProgram` values.

The lowering preserves the needed identities. Each HIR expression gets a
source label and `SourceSite`; a Lambda instruction retains its exact
parameter ID, Value role for an unannotated K0 formal, body label and saved
lexical environment. An Apply instruction stores `label(callee)` and
`label(argument)` from that same HIR node (`program.rs:818–848`). In particular,
the argument label is not evaluated while lowering. The source occurrence
and child labels can therefore name the Apply whose machine step is audited.

For authentic ordinary K0, contextual dictionaries are absent. The only
`contextual_dispatch = true` assignment is in the ambiguous FieldTail candidate
path (`program.rs:402–413`), which K0 excludes. Runtime dictionaries are built
only when that flag is true (`program.rs:1231–1241`). Operator/FieldTail
rewrites are separate constructors (`program.rs:1060–1105`) and are outside
K0. Thus `Machine::substitute_environment` returns its input unchanged before
reading a substitution when `program.dictionaries.is_none()` or the
substitution is `None` (`machine.rs:2509–2513`). This discharges the specific
possible substitution error between `new_invocation` and `ReceiverReturn` for
this authentic K0 route; it does not prove the source/capture environment
realization relation.

Selected-definition entry is available through `RuntimeProgram::start`, which
looks up the exact selected definition and forwards it to the selected schedule
(`machine.rs:383–393`). The whole-module entry has a different completion
contract and is not the root-result theorem entry (`program.rs:376–378`,
`machine.rs:2351–2370`). `run` advances the private machine one step at a time;
budget exhaustion returns `ResourceExhausted` while retaining the live state
for resumption (`machine.rs:576–588`). This is a pause, not a completed call.

The actual Apply transition is direct: evaluating `Instruction::Apply { callee,
argument }` pushes `Frame::Callee { argument, environment, site }`, then sets
`Evaluate { code: callee, environment }` (`machine.rs:878–888`). The frame
therefore retains the entire delayed argument label, its caller environment,
and the same Apply site. `return_value` pops only the current top frame; an
empty stack completes with the returned handle (`machine.rs:989–994`). This
distinguishes the authentic waiting Callee frame from a free-standing callee
evaluation configuration.

At that Callee return, the machine allocates an inert `Delay { code: argument,
environment }`, derives its receiving view, and looks up the executable by the
actual returned `ValueHandle` (`machine.rs:1162–1180`). The Closure arm reads
the exact formal, role, body and saved capture environment from that executable
(`machine.rs:1204–1212`). It creates a fresh invocation and saves the prior
owner (`machine.rs:1226–1228`, `1701–1719`), then for a Value closure pushes
`ReceiverReturn` followed by `ValueEntry` and executes that same Delay
(`machine.rs:1259–1274`). The stack order is therefore
`κ · ReceiverReturn(activation, previous) · ValueEntry(...)` while the whole
argument is being evaluated. On the argument return, `ValueEntry` binds the
same received value under the exact `Binder::Parameter(parameter)` in the
saved closure environment and starts the exact body (`machine.rs:1382–1410`).
The matching `ReceiverReturn` remains below the body continuation.

Nested Value calls use the same actual transition. A nested closure return
pops its own `ReceiverReturn`; `leave_owner` checks the current owner and active
receiver stack, retires that invocation, and restores its saved previous owner
(`machine.rs:1370–1380`, `1721–1749`). This supplies the concrete owner-stack
operations for the continuation-parametric induction. It does not establish
that every arbitrary stack has that shape; the proof must derive the invariant
from the authentic Apply and actual K0 transitions. K0 excludes the other
source constructs that install handler, operation, Comp and role evidence.

Errors stop the machine as `Unavailable`; the census claims no successful
return, progress, or owner coherence for a prefix that stops partway through a
fallible transition. A matching non-stopped return is the bounded control
boundary under review. Divergence and budget pause remain allowed.

## Six-column proof dependency record

This record follows audit §10.1. A `PASS` is always limited to the exact
domain and supplier stated in that row. In particular, a conditional
source-typing induction does not establish that a completed native graph
contains or entails all its source constraints.

| Claim | Exact domain | Code owner | Premise supplier | Falsifier / counterexample search | State |
| --- | --- | --- | --- | --- | --- |
| **D0 / K0 contract** | Ordinary single-definition authentic `ValidK0`; independent finite Value/effect algebra and source rules; selected-definition entry; finite explicit `Reifiable₀` witness | `yu-hir` local source identities; `candidate_source.rs`; `shadow_apply.rs`; `RuntimeProgram::start` | Audit §§4, 6, 9–10; R336 rev4 (`4bcbe71e…`); R336 review (`d03b7a23…`); R340 contract | Authentic HIR accepted despite excluded form/mode/dependency, or source/runtime entry differs from fixed contract | **Fixed, bounded.** Not a machine-checked formalization. |
| **G-sound / D1 constructor** | `ValidK0 ∧ CompleteK0Construction ∧ ρ ⊨ H(C_s) ∧ Reifiable₀(ρ)`; conclusion types the body at the authentic DefinitionValue root and body Effect endpoint | `candidate_source.rs`; source action admission in `shadow_apply.rs` / `lib.rs` | R336 rev4 and fresh review; R337 context/metadata result as cited by R338; audit §6 G | Missing K0 source occurrence/relation, wrong Name formal endpoint, absent body-to-root Value Link, or mismatch in any displayed constructor rule | **Bounded conditional PASS.** Does not prove `ρ ⊨ H(C_s)` from a final native graph. |
| **G-complete** | Every legal independent K0 typing must factor through one source-fixed finite constrained interface with the stated widening | `candidate_source.rs`; source rule/interface in the proof model | Audit §§6 G, 6 P; no complete supplier in R336–R340 | A legal source derivation with no satisfying assignment to the authentic generated constraints or no legal widening | **OPEN.** Keep separate from G-sound. |
| **L0** | Successful ordinary K0 construction prefixes; all live rows remain level 1, so no high-level extrusion copy or copy-derived intrusion | `lib.rs` allocators and K0 source-level admission; `candidate_extrusion.rs`; `candidate_intrusion.rs` | R336 rev4 and bounded independent review; audit §4.4 | Authentic K0 constructor/allocator creates a live row above level 1 or reaches the guarded copy branch | **PASS, bounded.** No solver or program termination claim. |
| **J / ordinary context metadata** | Authentic ordinary K0 successful construction prefixes and listed relation/bound/rewrite/replay/context lifecycle | `candidate_context.rs`; ordinary relation admission and replay in `lib.rs`, `candidate_extrusion.rs` | R337 proof/census; R338 composition's accepted context/metadata review disposition | Reachable K0 transition creates nondefault flow/Allowance/nonidentity context or a context mutation omitted from the induction | **Accepted only for the bounded context/metadata supplier.** Full D1/native preservation remains open. |
| **F / successful FreshUse map** | A successful `prepare_candidate_fresh_use` in audit §8.1's well-formed finite DAG, ordinary no-payload region; prepare only | `candidate_scheme.rs`; fresh row allocators and term constructors | User audit §8 and its explicit premises | Repeated representative gets a different image, distinct classes alias, or a child constructor/port is not mapped by the same row image | **Proved, limited to prepare and pure simultaneous renaming.** No restoration, eligibility or source-generalization theorem. |
| **N / native solution preservation** | Independently interpreted K0 state; source admission is an added formula; a preserving step needs its exact transfer/entailment premise and valid work ownership | `lib.rs`; `candidate_context.rs`; `candidate_extrusion.rs`; `candidate_intrusion.rs`; `candidate_scheme.rs` | R338 owner-record/replay candidate and review; R339 D2 proof/review; audit §6 N | A completed-state model violating an original source inequality, an unentailed retirement/cache hit, or a reachable omitted mutator | **Partial only.** Admission adds `q`; owner-record and selected replay facts have bounded evidence; R339 proves retirement for actual `candidate_replay_bound` children only. Initial/designated/processing/FunctionPort families, general cache/coverage and whole N remain OPEN. R338 duplicate-admission delta is OPEN/incomplete. |
| **M / R340 Apply control and identity** | Authentic ordinary K0 Apply; actual stack prefix and owner; callee/argument continuations only when the matching transitions occur; Value closure route | `program.rs`; `machine.rs`; `dispatch.rs`; `receiving.rs` | R340 producer candidate when frozen; source census above; audit §6 C; R339 D3 review | Callee frame/payload is consumed or changed, nested return fails to restore owner, or the actual handle/Delay/formal/body differs | **ACTIVE.** R340 proves only the missing control/identity prefix. Canonical-form/ValueReal, capture-environment transport, argument/body preservation, general progress and full M stay OPEN. |
| **W / graph witness construction** | Conflict-free completed/saturated K0 graph, including cycles, producing one finite/regular assignment and reification witness as specified | Native row/bound/term graph, export only if later justified | Audit §§4.2, 6 S; no supplier yet | A conflict-free supported graph with no admissible witness, or a witness that fails a live constraint | **OPEN.** No successful run implies model existence. |
| **Z / solver termination** | Every finite authentic K0 input under idealized sufficient IDs/memory; actual ordinary inference transitions | Source collectors, worklists, typed drain, relation/cache generations, replay and intrusion | Audit §6 Z; no supplier yet | Infinite fresh event/reopen trace or a reachable nondecreasing administrative cycle | **OPEN.** Resource refusal is not termination evidence. |
| **S0 / first whole target** | `ValidK0 ∧ NativeComplete₀(s,S) ∧ ρ ⊨ H(S) ∧ Reifiable₀(ρ)` with source typing independent of solver success | G source mapping; native state/work interpretation; actual selected-definition machine | Audit §6 S and §10.3 D1–D5; needs G-sound, G→H bridge, rest of N, M and runtime realization | Same-domain completed graph/model that fails independent typing, or a reachable typed K0 state that violates preservation/progress | **OPEN.** Explicit graph witness remains a premise until W removes it. |
| **P / K0 constrained principality** | One source-fixed finite `Σ_s` factoring every legal K0 typing/use with one consistent substitution and allowed widening | `candidate_source.rs`; graph/scheme construction and publication | Audit §6 P; G-completeness, N/W and exact interface | Legal typing/use observation not represented by the fixed interface, or one substitution failing source typing | **OPEN.** Do not infer failure from subtyping/effects or compact-renderer limits. |
| **X/Q/E/D and original A/B** | Later extrusion/intrusion, generalization/instantiation, contextual effects, descriptors, full source/catalog | Their existing source/native/runtime owners | Audit §§5–7, 9–12 and prior R330–R339 evidence | Source-qualified source-typing/evidence mismatch or a minimal counterexample to the named theorem | **OPEN, later gates.** K0 sequencing does not weaken the original product or A/B goal. |

## Composition seams and next proof packet candidate

1. **G → final native state → S0 is the first unresolved bridge.** For an
   assignment `ρ` satisfying `H(S_complete)`, prove under one explicit row
   restriction/transport map that every authentic generated source constraint
   in `H(C_s)` is satisfied. This is not part of the definition of
   `NativeComplete₀`. `CompleteK0Construction` establishes admission, not
   survival/entailment in the independently interpreted final `H(S)`.
2. **R340 → M is only one supplier.** The Apply prefix result can establish
   actual code/handle/Delay/frame/owner identity. It does not supply
   source-typing adequacy for the actual closure, capture-environment
   substitution transport, or all argument/body transitions.
3. **S0 + M must share witnesses.** The source, assignment `ρ`, lowered
   program and reachable machine configuration must all describe the same
   authentic definition. D3's control lemma cannot be composed with a
   different source or independently chosen Function ports.
4. **W and Z remain later gates.** W removes the explicit graph-solution
   premise; Z adds normal inference completion. Neither is implied by S0 or
   runtime progress. Program termination is not a target.

After the R340 outcome is frozen and reviewed, the next candidate packet is
**N-source-coverage**: for every authentic K0 source admission (including the
Definition root Link and FunctionPort demand), connect the same source row map
through `admit_collected_fact` / `start_typed_drain`, actual terminal or
replay/cache handling, and retirement/acknowledgement to the final `H(S)` used
by `NativeComplete₀`. Reuse R338's source-admission distinction and the R339
`candidate_replay_bound` child result only within their exact premises. The
first bounded searches should target the still-open initial, designated,
processing and FunctionPort obligation owners; a completed graph whose model
violates an original `C_s` inequality is the falsifier. This is only an
unfunded preparation note: it starts no sprint, grants no lease, and leaves
all UNKNOWN quarantines untouched.

R340's final D3 review must also challenge source-domain mismatches, the row
map and body/effect endpoints, and any attempt to use the control lemma as full
runtime simulation. The proof candidate, fresh review and final resource
receipt will be appended only after their exact artifacts freeze.

## R340 closeout and superseding dependency correction

This closeout supersedes the status, the `M / R340 Apply control and
identity` and `S0 / first whole target` rows above, and the preceding
prospective-review paragraph. The preceding 16,711 bytes are preserved
unchanged as the original census revision 1, SHA-256
`5b9fd45dc51a902c96a23586b4965a674b8429554340d8c3d01d4410746ecf5f`.
The reviewed proof is `notes/theory/2026-10-23-r340-k0-apply-continuation.md`,
SHA-256 `7ae75ef26d6bfa441989e9655dda89fbed2927d0061f5d8445246d587a0d7737`;
its handoff is `tasks/agent-loop/inbox/20261023-r340-k0-continuation-prover.md`,
SHA-256 `45ec9bcca22faa00228ab5daf7c59af2b462ec4380831f9b922fd4893977c87d`.

The fresh non-contributor compiler referee returned the following bounded
dispositions: authentic Apply handoff **PASS**; K0 prefix and owner
preservation **PASS**; invocation and argument-return identity **PASS,
conditional** on the proof's explicit Value-closure realization premise;
remaining realization, capture transport and full-M suppliers **OPEN**. The
referee found no source-qualified compiler counterexample. The referee also
accepted a **MAJOR proof-graph finding** in revision 1's S0 row: it conflated
S0's source-typing implication with the separate runtime-safety composition.
This finding concerns the dependency record, not the bounded Apply proof.

The corrected six-column entries below supersede only the two named rows.
They follow audit §6 S: S0 is the source-typing implication; its later
composition with machine simulation is a separate claim. The correction does
not close either whole theorem, and its new census bytes have not received an
independent delta review.

| Claim | Exact domain | Code owner | Premise supplier | Falsifier / counterexample search | State |
| --- | --- | --- | --- | --- | --- |
| **M / R340 Apply control and identity** | Authentic ordinary K0 Apply; actual stack prefix and owner; callee/argument continuations only at matching transitions; Value-closure route under the stated typed-realization premise | `program.rs`; `machine.rs`; `dispatch.rs`; `receiving.rs` | Frozen R340 proof and source census; audit §6 C; fresh R340 review | An authentic reachable K0 prefix changes the waiting Callee payload, fails to restore its saved owner, or uses a different handle, whole Delay, activation, formal or body | **Bounded conditional PASS** for handoff, prefix/owner preservation, invocation and argument-return identity. The independent delta review of this closeout is pending. Canonical-form/ValueReal adequacy, capture-environment transport, remaining argument/body preservation, general progress and full M remain OPEN. |
| **S0 / source-typing implication** | `ValidK0(s) ∧ NativeComplete₀(s,S) ∧ ρ ⊨ H(S) ∧ Reifiable₀(ρ)`; conclusion is the independent derivation `∅ ⊢₀ s : ρ(v_s) ! ρ(ε_s)`. `NativeComplete₀` has the audit's source-collection/admission and core-work conditions; it does not require runtime completion or successful execution. | Authentic K0 source rules and source-to-native constraint mapping; independently interpreted native graph/state and `H(S)` | G-sound constructor induction; the G → final-`H(S)` source-constraint transport/coverage bridge; exact `NativeComplete₀` and `Reifiable₀` definitions. No machine simulation or runtime realization premise belongs here. | A same-domain completed native graph with a model satisfying `H(S)` and `Reifiable₀`, yet whose authentic source fails the independent typing judgment; also a demonstrated source-constraint omission in the bridge | **OPEN.** The explicit graph solution remains a premise until W removes it. G-sound is bounded conditional evidence; the final-state source-constraint bridge and remaining N coverage are open. |
| **S0 + M / selected-definition runtime safety composition** | The same authentic `s`, assignment `ρ`, lowered program and selected definition as S0, plus an actual typed initial runtime configuration satisfying the realization invariant. Derive preservation and progress for its reachable selected-definition states; budget pause remains resumable, and host OOM is not claimed safe. | `program.rs`; `machine.rs`; `dispatch.rs`; `receiving.rs`; source/runtime realization owners | S0 source typing; full M simulation and runtime realization, including ValueReal/canonical-form adequacy, capture-environment transport and all required transitions; R340 supplies only its bounded Apply control/identity prefix | A reachable typed state violates preservation or progress, or the source, `ρ`, program and runtime configuration cannot be tied to the same authentic definition/witness | **OPEN.** Neither S0 alone nor the R340 prefix result proves this composition. |

Review/integration receipt: the referee's frozen-input pins matched on its
initial and final checks. Requested role/model/effort were
`compiler_referee` / `gpt-6.1-sol` / `medium`; observed model and effort are
UNKNOWN. The reviewer returned a final message and has stopped; exact
cessation timestamp was not supplied. Charge the full 600-second review grant
conservatively. The 300-second integration/state-sync grant is also charged
conservatively in the R340 closeout. No tests, builds, probes, source changes,
or reviewer Git operations occurred. R340's total 3,600-second cap is charged
with no carryover.
