# Source relay return instance: corrected constructor frontier

Revision: 2. Status: primary-corrected research candidate; independent review pending.
Sprint: `SOURCE-RELAY-RETURN-INSTANCE-20261026/r1`.
Baseline: `cc99471f36b167a8cfd526c5853f1c12077aaf58`.
The independently typed source derivation T has **not** been constructed.
No ReturnView or FL12 instance, Lean theorem, or production authority follows.

## 1. Rejected attempt and corrected source instance

The source-worker candidate incorrectly assigned Value entry to
`thunk:[] (int -> int)`. It conflated retained computation C with returned
value W and described an absent ground-result rewrite. The primary rejected
those claims. Exact rejected bytes and hashes are preserved in
`tasks/agent-loop/inbox/source-relay-return-instance-20261026-primary.md`;
the original source handoff remains frozen failure evidence. This revision
supersedes its mathematical/source claims, not its historical execution receipt.

The actual fixture in `tools/inference-playground/src/runtime/machine.rs` is:

```yulang
my relay (thunk:[] (int -> int)) = thunk
my main = relay (\x -> x)
```

Keep the original lexical identities for `relay`, `thunk`, `main`, and `x`.
C denotes the Call's delayed argument computation; W denotes the identity
closure returned when that computation executes. These are distinct objects
from the same execution. A common `xi=(nu,K,D)`, scope, provider, receiver and
world below are obligations for that prospective source derivation, not
evidence that an interpreted instance has been supplied.

## 2. Correct constructor and native spine

| Source constructor | Selected behavior | Pinned native owner |
|---|---|---|
| Parameter(`thunk`) | Explicit outer `[]` selects retained Computation entry. It supplies annotation permission, not a closed effect upper bound. | `program.rs` Lambda/schema formation; `machine.rs:1297` Computation branch |
| Lambda(`relay`) entry | Receive whole delayed C, retain its view/receipt, bind it as Computation, enter the body. No Value-entry Force/rebind occurs here. | `machine.rs:1297–1328`; `receiving.rs:224–259` |
| Name(`thunk`) and Result consumer | Read retained C. The designated Result consumer executes the known computation. Reading the binding is not itself a returned Function packet. | `machine.rs:2469–2500`, `NameConsumption::Execute` |
| Delay of argument expression | Inert formation retains `\x -> x`; designated execution constructs closure W. Forming W does not call W. | delayed argument dispatch and Lambda construction; prior reviewed producer correspondence |
| Return from C | End C's execution occurrence and retain W's existing received record. No groundness test or result-path image is constructed. | `machine.rs:1087–1096`, `RootCompReturn` |
| Prospective invocation of W | Unannotated `x` has Value entry: execute its argument, actual Return/rebind, then Name(`x`)/Result. This is a separate invocation and live world. | `machine.rs:1284–1296`, Value branch and `ValueEntry` |

This is static source/native owner correspondence, not a run or a complete
source derivation. The fixture returns W and contains **no subsequent Call
of W**. A later consumer must come from a genuine independently admitted
future context, not a second actual source occurrence invented for this fixture.

Source-Generalize §3.1 supplies the selected Parameter, Lambda, Name, Result,
Delay, Elimination and Call schemas. Result's computation consumer is essential.
The earlier relay returning-identity argument used the wrong rule and is
withdrawn. For W, Name/Return can preserve an actually rebound integer and
its provider/current world once that binding has its original valid certificate.
That local fact does not prove admission or complete invocation observations.

## 3. First unfilled leaf in the attempted derivation

Choose the argument producer before Delay, relay Call and result export.
At the new Lambda `\x -> x`, retain actual decomposition `Act(W,U_id,r)`,
original captures and scope. Membership at its original complete Function
descriptor F requires contextual membership §2 / semantic-input realization §3.1:

1. For every independently admitted complete challenge `d in D_F`, prove
   `ActualAdm(W,U_id,d)` for the same whole carrier, actual receipt/context
   preconditions, current configuration/world, assignment and `xi`.
2. For every complete, pending, administrative and zero-step observation of
   that invocation and every admitted continuation/future development, prove
   membership in `P_F(d)` with its full typed-state/descriptor envelope,
   original provider, operation witness, scopes and incidences.

This includes finite prefixes of divergence and requests/resumptions; it
requires no Return. There is no need to enumerate or construct every challenge
inhabitant. The missing proof must handle an arbitrary independently admitted
challenge using original constructor laws. Challenge formation cannot assume
body safety or U's acceptance.

This leaf is first in the chosen traversal, not necessarily the unique earliest
dependency in every derivation. Relay's complete interface, inert Delay license
and execution obligations, world/capture validity, annotation realization and
native-to-source judgment bridge also remain unestablished for the whole instance.

### Why existing results do not fill this leaf

- Source-Generalize's Lambda schema requires actual entry, body proof at the
  independent challenge, body consumer and complete invocation. Local L1–L5
  assumptions are not proofs for this initializer.
- Contextual membership §4 explicitly leaves new closure introduction open.
  Its Name/Name Call and selected two-closure recursive pair do not establish
  identity Lambda introduction.
- Semantic-input realization §4.2 proves Name/Return from an existing jointly
  valid binding. Its §4.3 Name Delay starts from existing value membership;
  it does not introduce this new Lambda.
- Complete source-interface construction retains real producer/interface
  operands and incidences. A static slot name does not create semantic validity.

No supplied descriptor/challenge law has been disproved. An arbitrary replacement
for `D_F` or `P_F` is not a counterexample to the fixed source meaning. This is an
unfilled premise exposed by the attempted derivation, not an impossibility theorem
or an execution counterexample.

## 4. Result projection remains conditional

Reviewed runtime-Function-result source construction starts from an independently
valid T. Its consumption event c retains C's operand packet and result edge.
Its dependent return slot is filled only by actual W/current-world result from
that same event. The established construction then generates the result-prefix
action and preserves both tagged inputs: C's result-position evidence and W's
independently produced evidence.

This attempt supplies neither T nor W's complete producer membership. It has
not instantiated `ElimExport`, `CallableExport`, ReturnView or FL12. No concrete
`rho_C`, full `mu`, result-path profile or complete later Call consumer is
constructed here. Retaining native W does not supply these source objects.
Equal endpoint shapes cannot repair the missing proof or merge C/W inputs.

Outer `[]` is permission with an open row, not a closed pure effect row.
No vacuity argument removes effectful or nonreturning admitted challenges.
No nested-effect source discriminator has been constructed; its own valid
Lambda/Delay/consumer instance remains required. This is not a counterexample.

## 5. Formalization and implementation boundary

Lean construction is **NOT_ISSUED: SOURCE_CONSTRUCTOR_PREMISE_UNESTABLISHED**.
`Contracts.lean` supplies abstract `SourceProblem.sourceJudgment` and obligations,
not a concrete interpretation of these source rules. Paper core typing and
existing `TypedCall` interfaces cannot be renamed into T. A narrow source calculus
or assumed T/profile/`LocalLaws` is not an acceptable substitute. No Lean checker
has run for this sprint.

Rust remains `NO_SAFE_CODE_SLICE`: `program.rs` retains Lambda/formal schema
owners; `receiving.rs` establishes computation view/receipt; `machine.rs`
consumes C and preserves W. These equations do not supply the missing complete
source introduction or authorize new result/request metadata semantics.
No compiler/runtime file changed.

Next decisive evidence: construct both membership clauses from the original
independently fixed contracts at W's actual Lambda, then the rest of this same
source derivation. A complete applicable derivation found in the governing
sources would overturn the prerequisite gap. Only then can the reserved Lean
packet and same-instance result extraction proceed. Original A/B, full execution
safety, source/native correspondence and production remain OPEN.

## 6. Dependencies and evidence class

All 31 contract pins match baseline. Additional material selected source:
`notes/theory/2026-10-08-call-semantic-input-realization.md`, SHA-256
`fd781ba2d76b239724b86183985c612fe3bbd3542ff8d47860705c9c3752226a`,
also matches baseline. The pinned Lean tree includes `Contracts.lean`.
Evidence is static source inspection and an attempted derivation with explicit
missing premises. No tests, probes, builds, runtime run or axiom-audit result is
claimed. Independent review and primary adjudication are recorded separately;
they cannot make the missing T true.
