# R339 D3 — K0 Value-call prefix simulation

**Status:** primary source trace and conditional prefix lemma; fresh review
pending. This is not full runtime soundness, progress, D3 completion, or S0.

## Scope and pins

This note follows the user-directed audit at SHA-256
`b720fc938423bea1b677f7121653e2452b0fb0b9bb2919e9d38c7fccbee64895`,
sections 4.1–4.5, 6 C/S and 10.3. The source domain is its authentic ordinary
single-definition K0; the machine entry is selected-definition. The source
typing rule and native `H(S)` remain independent of runtime execution. The
shared theorem boundary is the R336 conditional source judgment and its root
Value/body Effect endpoints, with the R337 ordinary context premise. No
assumption of `NativeComplete`, solution existence, successful execution or
empty `candidate.unresolved()` is introduced here.

Branch/head: `research/simple-sub-intrusion`,
`f647390d6a3502c0d8814d46870d55685cee1753`.

| Runtime/source owner | SHA-256 |
| - | - |
| `tools/inference-playground/src/runtime/program.rs` | `df58f9a1d60e39fafe6d85b1e50331b35fde2a9142a2eaea84ad028d3048fdb0` |
| `tools/inference-playground/src/runtime/machine.rs` | `02adc26bcd58cca488a40e78289a264751146d7900c2897db19068b279a8d840` |
| `tools/inference-playground/src/runtime/literal.rs` | `2fff177a7ba0cabb4930251e1facc8f9be701ff3ec7baa695ce4c182fa1da35f` |
| `tools/inference-playground/src/runtime/receiving.rs` | `2170a3bcbc6710ce3fbf721a05129117f8266b9ecf21c67136db918815303551` |

The same-source boundary is real but limited: `RuntimeProgram::from_candidate_world`
checks that the candidate observes the supplied HIR and has no candidate
conflicts before constructing runtime evidence (`program.rs:319–328`). That
does not return a typing derivation or prove source/runtime simulation. The
selected-definition entry is `Machine::start` and
`start_source_schedule` (`machine.rs:369–393`); when the source schedule is
exhausted, the selected path evaluates or returns the selected definition's
cached value (`machine.rs:2324–2348`). This preserves the root body's result
contract rather than the whole-module completion Unit described by the audit.

## Independent source judgment and realization

For source `Apply f a`, use the audit's independently stated typing rule: the
callee is typed by the four-port Function demand with the actual argument's
Value/Effect, the result Value and invocation Effect; callee-evaluation and
invocation effects are included in the application Effect. This rule is not
defined by `Instruction::Apply` or by successful candidate solving.

Define runtime realization before execution. Let `Val₀` be the independent K0
source-value domain: unit, integer, boolean and string literals, and closures
`⟨λx.e, σc⟩` carrying an authentic Lambda occurrence and source capture
environment. `CodeReal₀(e,k)` holds when `k` indexes lowered code whose
`SourceSite` has the same source root and occurrence as authentic source e,
and whose instruction is the HIR-lowering constructor for e.

A source value environment σ maps parameter IDs to typed source values.
`EnvReal₀(σ,η)` holds pointwise when each binding x↦(τ,v) in σ resolves from
runtime environment η by `Binder::Parameter(x)` to a cell containing
`ReceivedValue r`, and `ValReal₀(τ,v,r.value)` holds. K0 excludes local
binding, modules/imports, catch/case binders and other pattern forms, so this
lexical relation does not identify them with parameters.

Define `ValReal₀(τ,v,h)` between a source value v and actual `ValueHandle` h
by independent representation clauses: literal cases match the corresponding
`RuntimeValueKind` payload (integer and string spelling follows `literal.rs`);
for a function type τ, the source value must be `⟨λx.e, σc⟩` with an independent
source typing derivation at τ, and h must have `RuntimeValueKind::Closure`
with executable entry
`Closure { parameter: x, unit_pattern: false, record_pattern: None,
role: Value, body: k, environment: ηc }`. The runtime body label k must
satisfy `CodeReal₀(e,k)`, and `EnvReal₀(σc,ηc)` must hold.
Write `ClosureReal₀(τ,v,h,ηc)` for this function clause, making the actual
handle h and saved environment ηc part of the witness. Two closures from the
same Lambda occurrence may therefore realize the same source code with
different capture environments. These clauses refer only to source values,
source identities and machine storage; they are not defined by later machine
success. This packet defines the realization criterion but does not prove its
adequacy from K0 source typing.

The conditional input configuration is `State::Evaluate { code: k_f,
environment: ηcaller }`, related by `CodeReal₀`/`EnvReal₀` to the source
evaluation of f under σcaller. If source evaluation yields function value v_f
and machine evaluation returns handle h, the prefix lemma requires
`ClosureReal₀(τ_f,v_f,h,ηc)` for the Function-typed callee. Deriving these
source/runtime results and the typed-value/canonical-form supplier from the
full K0 typing relation is not proved here; this is the exact open premise for
extending the local transition calculation to all K0 Apply cases. A callee
which realizes a primitive, continuation or computation-entry consumer is
outside this bounded Value-closure lemma.

## Source-to-runtime transition trace

The correspondence for the named prefix is:

| Source/runtime event | Native owner and consequence |
| - | - |
| Authentic source `Apply f a` | `program.rs:843–849` lowers `LocalSourceForm::Apply` to `Instruction::Apply { callee, argument }` using the two child labels. The containing code keeps the source site. |
| Evaluate callee in caller environment | `machine.rs:878–888` pushes `Frame::Callee { argument, environment: ηcaller, site }` and evaluates the callee label in ηcaller. |
| Produce an actual closure handle (when the source callee evaluates a Lambda) | `program.rs:818–842` lowers the authentic Lambda formal, body and Value role. `machine.rs:856–877, 2589–2617` allocates a fresh `ValueHandle` and stores `ExecutableValue::Closure` with those exact fields and the current capture environment. Re-evaluating the same Lambda site can therefore create distinct handles with distinct environments. For a non-syntactic callee, this identity is supplied by `ClosureReal₀`. |
| Receive actual callee h | `machine.rs:1162–1180` allocates a whole `ExecutableValue::Delay { code: a, environment: ηcaller }` before invocation. It then looks up the executable using the returned `ValueHandle h`, not a SourceSite or Lambda occurrence. |
| Match actual Value closure | `machine.rs:1214–1230` reads the actual closure's formal, role, body and saved capture environment. The Value-closure branch uses the handle's source only as the provider `SourceSite`. |
| Establish invocation owner | `machine.rs:1701–1724` allocates a fresh invocation ID, stores the call site and provider site, pushes the active receiver and saves the prior owner. It does not use the provider site as closure identity. |
| Preserve closure environment and frame order | `machine.rs:1242–1266` applies the runtime dispatch substitution to the saved closure environment, pushes `ReceiverReturn { activation, previous }`, then pushes `ValueEntry { parameter, body, environment: ηc' }` and executes the Delay. For ordinary K0 with no dispatch substitution, ηc'=ηc; otherwise the relation must follow the actual substituted environment. |
| Evaluate the whole delayed argument | `machine.rs:2451–2464` executes a Delay by switching to `State::Evaluate { code: a, environment: ηcaller }`. The argument expression is not replaced with a fresh value chosen from a separate port witness. |
| Bind and enter exact body | `machine.rs:1395–1415` handles the ValueEntry result, binds the received Value to `Binder::Parameter(parameter)` in ηc', and sets `State::Evaluate { code: body, environment: ηbody }`. The closure body and binder are those stored on the same actual handle h. |

The RuntimeProgram Lambda lowering selects `ParameterRole::Value` for the
unannotated K0 Lambda (`program.rs:810–842`); `ValidK0` requires no annotation,
`unit_pattern=false` and `record_pattern=None`. Its grammar also excludes hidden
operator lowering and Sequence result forms. Literal payload decoding is handled
separately in `literal.rs`; it is not needed as a premise for the
frame/closure identity argument.

## Conditional prefix lemma

**Lemma D3-call-prefix (conditional).** Fix a well-formed K0 HIR program and
the same candidate/HIR pair accepted by `from_candidate_world`. Let an
independently typed source `Apply f a` have a runtime configuration related by
`CodeReal₀` and `EnvReal₀` at the callee. Suppose source evaluation of f yields
function value v_f and the related machine evaluation returns actual handle h,
with `ClosureReal₀(τ_f,v_f,h,ηc)` identifying h as the Value-entry closure
for that typing derivation. Then the actual machine transition sequence enters
exactly the argument Delay under ηcaller and places an exact `ValueEntry` for
h's binder/body and ηc' above the matching `ReceiverReturn`. If the related
source/runtime evaluation of a returns source value v_a and actual received
value r with `ValReal₀(τ_a,v_a,r.value)`, the machine binds that same
`r.value` to h's parameter in ηc' and begins h's body. Together with the
actual capture-environment substitution premise, this yields the corresponding
extended `EnvReal₀` relation for the source body environment.

**Proof.** The Apply lowering and evaluator create the `Callee` frame with the
source argument label and caller environment. The `Callee` arm allocates the
Delay from those exact stored fields, performs executable lookup by h, and
enters only the matching `Closure` arm. `new_invocation` returns a fresh
activation and the prior owner; the arm pushes the owner-restoring frame below
the ValueEntry frame and executes the just-created Delay. The Delay executor
restores its exact code/environment pair as the next evaluation. On its Value
return, the ValueEntry branch uses its stored parameter and saved closure
environment to bind the actual received value, then selects the stored body.
No step changes h, the argument label/environment, parameter or body. The
machine branch order and stored fields therefore establish the stated prefix.
The missing theorem-level step is deriving `ClosureReal₀` for every relevant
well-typed callee without assuming successful runtime execution. ∎

## Limits and falsifiers

This is a source-qualified transition lemma, not the full M theorem. It does
not establish that a K0 source typing derivation always supplies a runtime
realization, that every Value-typed function value is a matching closure, that
the argument or body terminates, that the function result has its declared
type, or that effects/continuations are preserved. The preserved owner frame
is identified, but normal return restoration is not promoted here. Budget
pause, divergence and symbolic latent effects remain possible.

The direct falsifier is a reached Value-call trace where the actual handle's
closure, saved environment, argument code/environment, formal binder, body,
activation owner or continuation frame differs from the corresponding
source/runtime relation. An unreachable fabricated handle or a primitive,
continuation or Comp consumer is not a K0 counterexample. No such authentic
trace was established from this static inspection.

**Disposition:** conditional D3 source/native evidence; typed canonical-form
supplier and global runtime simulation remain OPEN. **Code disposition:**
`NO_SAFE_CODE_SLICE`; no source-qualified implementation defect was found.
No tests, Cargo, execution probes or code changes were made. Independent review
of this exact artifact is pending.
