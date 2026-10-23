# R343 primary source census — K0 machine-step safety

Status: frozen primary census, revision 1. This is source correspondence
evidence, not a proof, independent review or compiler repair.

Baseline: `research/simple-sub-intrusion` at
`2ddee9031fc43bb5fdf7b93424b86822de599407`, equal to upstream. Contract:
`tasks/agent-loop/sprints/r343-k0-machine-step-safety-20261023.md`.
The user audit hash is
`b720fc938423bea1b677f7121653e2452b0fb0b9bb2919e9d38c7fccbee64895`.
Runtime owner pins are copied verbatim from the frozen R343 contract and were
matched against this baseline.

## K0 source and entry boundary

Use exactly audit §4.1: one argument-free, nonrecursive selected Definition;
no root annotation/where clause or dependency on another definition, module or
import; canonical Unit/Bool/ASCII-decimal Integer/verified quoted String or
DecodedString; parameter-resolved Name; annotation-free simple Value Lambda
with `unit_pattern=false` and no record pattern; Apply; else-complete If; Group;
binding-free Block/StatementBlock. Ordinary candidate and the same authentic
HIR are fixed. Other instruction families remain outside K0.

`RuntimeProgram::start` resolves the selected `DefId`, validates the supplied
execution-root schedule, constructs the machine with empty frames/values and
one root environment, then enters the selected definition through
`begin_root` / `complete_selected_definition` (`machine.rs`, start and root
owners). The theorem must pin the exact selected-definition entry used by the
proof. It must not use whole-module completion as a substitute for a typed
root result. The root is source code for the selected definition; K0's lack of
global Name/import dependencies keeps the dynamic expression path inside that
single root.

`RuntimeProgram` lowering retains source-root/occurrence labels and maps
authentic Group/Ascription to `Instruction::Forward`; K0's Group therefore
adds no semantic value operation. Lambda lowering retains the parameter ID,
body label, Value role, and absence of unit/record patterns mandated by K0.
If/Apply/Block lowering preserves child labels and source order
(`program.rs:544–603, 748–879, 962–979`). Integer/String conversion is owned
by `literal.rs`; the K0 spelling restriction is needed to rule out decoder
failure without assuming runtime success.

## Reachable transition owners

Machine states and outcomes are explicit (`machine.rs:140–270`). `step`
performs one `Evaluate`, `Return`, or other state transition and records a
returned `RuntimeUnavailable` as a stopped outcome (`machine.rs:650–676`).
`run(step_budget)` calls `step` at most that many times; an exhausted caller
budget returns `ResourceExhausted { steps }` while leaving a non-stopped state
available for a later `run` (`machine.rs:578–592`). A stopped normal outcome is
not converted into a budget pause.

K0 `Evaluate` owners (`machine.rs:678–929`):

| Source form | Actual operation | State/frame effect |
| --- | --- | --- |
| Unit/Bool/Integer/String/DecodedString | decoder then `ground_data` | append actual value and ground view; return that handle |
| parameter Name | resolve exact parameter binder with lexical `lookup`; preserve the received record through K0 dispatch metadata; `consume` validates the same view/handle | Return the same received value |
| Value Lambda | `data` plus `ExecutableValue::Closure` | exact source site, formal, body and current numeric environment are stored under the new value handle; Return that closure |
| Apply | push `Frame::Callee` with the whole argument label and caller environment | evaluate callee first in that same caller environment |
| If | push `Frame::Condition` for first test; else branch directly when no arms (excluded by K0) | tests and selected branch use the same lexical environment |
| Group | lowered `Forward(inner)` | evaluate the authentic child in the same environment |
| binding-free Block/StatementBlock | `begin_local` selects the ordered expression/final expression | `Frame::BlockExpression` records the prefix continuation; no local binding frame is reachable |

The exact actual closure call is in `return_value`'s `Frame::Callee`
(`machine.rs:1162–1370`). It allocates one inert `ExecutableValue::Delay`
containing the entire argument label and caller environment, derives its view,
then dispatches by the returned *value handle*'s executable entry. The K0
Function canonical-form supplier is what must exclude non-closure arms. For a
Value closure the machine creates one invocation, substitutes the actual saved
environment using the returned value's dispatch metadata, pushes
`ReceiverReturn` and `ValueEntry`, and forces that Delay. Do not equate
`SourceSite` with closure identity or evaluate only an argument prefix.

`Frame::ValueEntry` verifies the K0 pattern shape, binds the exact received
argument handle/view/dispatch under the exact parameter ID, extends the saved
closure environment and evaluates the actual body (`machine.rs:1382–1421`,
`2538–2557`). It does not create a replacement argument value.
`Frame::ReceiverReturn` leaves the exact invocation owner and restores the
previous owner before returning the same handle (`machine.rs:1370–1381`).
R342 proves the narrow environment/value and body-entry suppliers; R343 must
establish their inductive use at every reachable state without assuming the
body returns.

`Frame::Condition` checks the returned payload is Boolean and selects the
corresponding branch, advancing through ordered tests or the explicit else
(`machine.rs:1482–1525`). K0's independent typing and Bool canonical form must
exclude `ExpectedBoolean`. `Frame::BlockExpression` resumes `begin_local` in
the recorded environment (`machine.rs:1526–1528`); K0 permits expression
prefixes only, and the final expression supplies the block result. Group has
no frame. `Frame::Root` caches the actual returned record and resumes the
selected root schedule; after its final slot,
`complete_selected_definition` publishes the cached selected result
(`machine.rs:1659–1670, 2280–2348`). The proof's result relation must be for
this exact source definition/value pair.

Name dispatch can extend only dispatch metadata in K0 and leaves the actual
value handle, view and interface intact under the R342 inspected cases;
`dispatch.rs` is pinned because the exact substitution path is part of the
environment invariant. `receiving.rs` is pinned because the view/value match
is an actual guard and part of the R340/R342 realization witnesses.

## Outcome partition and unresolved proof obligations

- `Running` after `step` is an active next machine state, not proof that the
  source terminates.
- `Completed(handle)` is normal selected-definition completion only when the
  root and cached `ReceivedValue` correspondence is preserved.
- `ResourceExhausted { steps }` is an external step-budget pause; the machine
  remains resumable. It does not imply a semantic transition failed.
- `Unavailable(IdentityExhausted)` is a checked finite identity/resource
  failure. Keep it distinct from semantic unavailability.
- For authentic typed K0, `ExpectedCallable` and `ExpectedBoolean` should be
  unreachable by R336's function/Bool canonical forms plus state preservation.
  `MissingBinding`, `UninitializedBinding`, `LiteralDecoding`, and
  `InvalidSourceReference` require authentic source ownership, correct
  lowering/labels, lexical environment realization and valid storage/view
  invariants. These are exact proof obligations, not established by this
  census. Calls to operation/handler/effect/member/record/case/Comp paths are
  excluded by K0. A concrete reachable failure would falsify the bounded
  statement; an absent supplier remains OPEN.

The claim excludes host OOM behavior. Do not turn an unchecked allocation
failure or a Rust panic into a safe refusal claim. No execution probe or test
was run for this census. The only source evidence is direct read-only
inspection at pinned bytes. Compiler code was not modified.

## Falsifier inventory

| Owner | Exact falsifier |
| --- | --- |
| `RuntimeProgram::start`, `begin_root`, selected completion | authentic selected K0 source enters another body, loses the selected root, or completes a different handle |
| K0 lowering and `evaluate` | authentic supported form maps to a different label/constructor, decoder rejects a permitted canonical literal, or parameter Name is not the exact lexical binder |
| `Frame::Callee` | typed K0 function value lacks the matching actual closure executable; argument Delay is not the whole source child/caller environment; value dispatch chooses another executable |
| `ValueEntry`, `bind`, closure environment | body entry receives a different handle, binder, environment, view or dispatch metadata than the actual argument and saved closure |
| `Condition` | typed Bool test reaches non-Boolean payload or selects a different source branch/order |
| `BlockExpression` / `Forward` | a binding-free block changes prefix order, evaluates an excluded binding, or does not return the final child value |
| `ReceiverReturn` / `Root` | owner restoration or root publication changes the source-relevant value/owner or publishes before return |
| `step` / `run` | budget depletion publishes a partial value or loses resumable active state; a nonterminal active K0 state has no checked next step |
| any K0-reachable guard | a semantic `Unavailable` occurs with all stated source/runtime invariants, or a missing invariant is hidden by assuming successful execution |

The census is primary-owned correspondence, not independent certification.
The required fresh reviewer must inspect the frozen census against the same
source pins and the full proof transition table.
