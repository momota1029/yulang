# R342 — K0 value/environment realization: source census

Status: Luna primary's source correspondence census; static and conditional.
This is not the proof supplier, an independent review, runtime execution, or
closure of D3/M.

## Authority, baseline and inputs

This census follows the user-directed audit
`docs/Yulang Simple-sub 拡張：全体証明への移行監査・証明設計.md`,
SHA-256 `b720fc938423bea1b677f7121653e2452b0fb0b9bb2919e9d38c7fccbee64895`,
especially §§4.1–4.5, 6 C/S and 10.3. Its source scope remains authentic
ordinary, selected-definition K0. The selected contract is
`tasks/agent-loop/sprints/r342-k0-value-environment-realization-20261023.md`;
its frozen hash is recorded in `current.json`.

The D0 independent source judgment, finite Value preorder (including bounded
joins/meets and four-port Function variance), K0 grammar and exclusions are
pinned to R336 rev4, SHA-256
`4bcbe71ec9f2372baca884e3db737c16fc19ad2a51103965ade5ca4c2ecf4973`.
The runtime call-prefix dependency is R340, proof SHA-256
`7ae75ef26d6bfa441989e9655dda89fbed2927d0061f5d8445246d587a0d7737` and
source census SHA-256
`de3902d834a68f0d4f5b269f4bddac7d900d44bfe8dc118b05b451372cf24078`.
R341 retains the unchanged conditional S0 result under its exact premises; it
does not provide runtime realization.

| Inspected runtime owner | SHA-256 |
| --- | --- |
| `tools/inference-playground/src/runtime/program.rs` | `df58f9a1d60e39fafe6d85b1e50331b35fde2a9142a2eaea84ad028d3048fdb0` |
| `tools/inference-playground/src/runtime/machine.rs` | `02adc26bcd58cca488a40e78289a264751146d7900c2897db19068b279a8d840` |
| `tools/inference-playground/src/runtime/dispatch.rs` | `f45057373f2ed3a7b6ce915611db093015fb93cdb05984a5e3b23cfd44720873` |
| `tools/inference-playground/src/runtime/literal.rs` | `2fff177a7ba0cabb4930251e1facc8f9be701ff3ec7baa695ce4c182fa1da35f` |
| `tools/inference-playground/src/runtime/receiving.rs` | `2170a3bcbc6710ce3fbf721a05129117f8266b9ecf21c67136db918815303551` |

Inspection was read-only. No tests, Cargo/builds, runtime probes or source edits
were performed. Line references below identify the pinned versions above.

## Authentic K0 forms and lowered identity

R336 rev4 fixes the source domain: one nonrecursive definition, empty outer
environment, ordinary candidate mode, selected-definition entry, authentic
HIR, and only Unit/Bool/decoder-valid Integer/String literals, parameter Name,
annotation-free single-binder Value Lambda, Apply, else-complete If, Group,
and binding-free Block/StatementBlock. Statement blocks contain expression
prefixes and a final expression. No local bindings, recursion, Comp entry,
annotations, imports/dependencies, role/member/operator/interpolation,
Case, records, tuples, variants, operations or handlers enter K0. In
particular `DecodedString` is a carrier form from interpolation lowering, not
an authentic standalone K0 expression.

`RuntimeProgram::from_hir_with_roots` resolves each authentic
`LocalSourceIndex` and maps it to `Label(offset + ordinal)` after checking the
index belongs to that source (`program.rs:544–603`). It constructs each `Code`
with the source root, occurrence and range (`program.rs:962–979`). The K0
lowering cases retain these source identities and use their actual child
indices:

| Source form | Runtime instruction and relevant owner |
| --- | --- |
| Unit, Bool, Integer, String | `Unit`, `Boolean`, `Integer`, `String`; lowering at `program.rs:748–755`, evaluation at `machine.rs:678–703`. Integer and string payloads pass through `literal.rs`; see below. |
| parameter Name | `Name { resolution: Parameter(id), consumption: Observe }` for an unannotated Value Lambda formal; role table/lowering at `program.rs:709–747, 756–808`. The spelling is not used to resolve the runtime cell. |
| Value Lambda | exact `parameter.id`, `body` label and `role: Value`; lowering at `program.rs:818–842`. K0 guarantees no unit/record pattern or annotation. |
| Apply | exact `callee` and whole `argument` labels; lowering at `program.rs:843–849`. The containing `Code.site` identifies this Apply occurrence. |
| If | authentic ordered tests/branches and `else_branch`; lowering at `program.rs:872–879`. K0 supplies an else branch. |
| Group | `Forward(inner)`; lowering at `program.rs:810–813`; it evaluates the exact child under the same environment. |
| binding-free Block/StatementBlock | `Block`/`StatementBlock` with exact prefix/final labels; lowering at `program.rs:852–871`. K0 excludes binding entries. |

The source-schedule selected-definition entry is `RuntimeProgram::start` and
`complete_selected_definition` (`machine.rs:383–417, 2324–2348`); it evaluates
or returns the selected definition's cached body value. The whole-module
completion path instead manufactures Unit and is outside this theorem.
`from_candidate_world` authenticates candidate/HIR identity but does not
produce an independent typing derivation or prove this simulation.

## Values, parameter lookup and closure identity

The K0 literal-value correspondence has a concrete representation owner.
Integer decoding accepts nonempty ASCII digits and removes leading zeroes
(`literal.rs:1–9`); string decoding checks the source delimiter and interprets
the supported escapes (`literal.rs:12–58`). Bool is copied, Unit uses its
dedicated runtime kind, and already decoded strings are not a separate K0
source case. The proof still needs the audit's decoder-valid source premise;
the runtime decoder alone cannot supply it.

For `Instruction::Name(Parameter(id))`, `Machine::evaluate` calls `lookup`
with exact `Binder::Parameter(id)` equality (`machine.rs:773–834`). `lookup`
walks the environment parent chain and returns the matching cell
(`machine.rs:2488–2498`). A present cell yields its actual `ReceivedValue`;
`consume` validates its receiving view and, for `Observe`, returns that same
received record (`machine.rs:2372–2388`). K0's unannotated Value parameter
selects `Observe`, not computation execution. This establishes an operational
identity path conditional on the environment containing that authentic
parameter cell; it does not prove that an independently typed source value
has a runtime realization.

Evaluating `Instruction::Lambda` allocates a fresh `ValueHandle` whose value
kind is Closure and whose executable stores the exact formal, pattern flags,
role, body label and current environment (`machine.rs:856–877, 2589–2617`).
The environment is therefore the closure's actual lexical capture, not an
inferred reconstruction from a `SourceSite`. Two evaluations of one Lambda
occurrence may allocate different handles and capture environments. Proving
that a source function value is related to this handle requires the separate
canonical-form/value-realization argument.

## Apply, Delay, actual handle and exact ValueEntry

For an authentic Apply, `Machine::evaluate` pushes
`Callee { argument, caller environment, Apply site }` and evaluates the exact
callee label (`machine.rs:878–888`). R340 proves the protected continuation
prefix from that source Apply; it does not assume the Callee frame exists or
that evaluation returns.

At an actual matching callee return, `Frame::Callee` allocates a Delay from
the stored whole argument label and caller environment, then looks up the
executable by the actual returned `ValueHandle` (`machine.rs:1162–1180`). The
Value-closure arm reads that handle's stored formal, role, body and capture
environment (`machine.rs:1204–1212`). It creates the invocation at the Apply
site and pushes `ReceiverReturn` below the exact `ValueEntry`. K0's role is
Value, so it executes the whole Delay; no separate port witness chooses an
argument value (`machine.rs:1225–1274`). Executing that Delay enters the stored
argument code in its caller environment (`machine.rs:2451–2461`).

At a matching argument return, `Frame::ValueEntry` binds the actual returned
value/view/dispatch under `Binder::Parameter(formal)` and enters the body
label saved from the same executable closure (`machine.rs:1382–1410`).
`bind` allocates one cell and `extend` places the exact binder/cell over the
saved capture environment (`machine.rs:2529–2541`). Lookup finds the new
formal first and resolves other parameters through the parent chain. This is
the concrete source owner for same-value binding and exact body entry. The
typed body-environment conclusion still depends on independent realization
of the argument and capture environment.

## Dictionary and dispatch branches

`RuntimeProgram::from_candidate_world` initializes contextual dispatch off.
The sole write that turns it on is the ambiguous field-tail selection case
(`program.rs:402–412`; exact assignment search found no other writer). Runtime
dictionaries are `Some` iff that flag is on; their entries come from
field-tail contexts, and `dictionary_names` contains only Name steps from
those words (`program.rs:1231–1248`). Authentic K0 contains no field-tail or
member use, so its constructed program takes the dictionary-absent branch.
This follows from the fixed source domain and constructor, not from assuming
all environments are dispatch-free in the general machine.

Both generic branches were inspected:

* With no dictionary, `substitute_environment` returns the exact environment;
  `dispatch_name` returns the exact `ReceivedValue` (`machine.rs:2509–2528`).
* With a dictionary but no substitution, `substitute_environment` still
  returns the exact environment. With both present, it composes the existing
  and new substitution using ordered `Then` and creates a binder-free wrapper
  whose parent is the exact old environment (`machine.rs:2509–2518`,
  `dispatch.rs:78–94`). `lookup` walks through this parent, so parameter cell
  identity is preserved. It is not valid to assume substitution is inert or
  idempotent.
* With a dictionary, `dispatch_name` may update only the `dispatch` field of
  the copied `ReceivedValue` using the exact cell/site and optional Name
  instantiation (`machine.rs:2520–2528`, `dispatch.rs:161–185`). Its value
  handle, view and interface remain those of the input record. An authentic
  K0 program has no dictionary Name steps, so it uses the absent branch above;
  the present-branch observation is an owner fact, not an extension of K0
  semantics.

Consequently the authentic K0 closure's saved lexical bindings and
same-value ValueEntry cell survive the only reachable K0 branch. For a future
dictionary-bearing source domain, the wrapper/Name result preserves lexical
lookup and value identity while dispatch metadata follows the ordered
substitution; that broader dispatch relation remains its own proof obligation.

## Source lane disposition and remaining suppliers

The inspected owners agree with R340's conditional body-entry trace. No
source-qualified mismatch was found in authentic K0 lowering, closure handle
lookup, saved lexical environment, argument Delay, parameter cell, or body
entry. There is no authorized source edit: **NO_SAFE_CODE_SLICE**. This
disposition is based on direct inspection of the pinned `program.rs`,
`machine.rs` and `dispatch.rs` owners; it does not certify the proof lane.

Open obligations remain precise:

| Supplier | Remaining evidence |
| --- | --- |
| K0 Function canonical form / `VREAL` | Derive closure shape for a Function-typed source value from the independent D0 judgment and preorder, including subsumption, joins/meets and environments. Relate every finite authentic K0 evaluation result to its actual runtime value. A finite returned value is conditional; do not assert evaluation returns. |
| `CAPTURE` | Show the source closure capture environment is pointwise realized by the actual saved environment, then preserved through any applicable environment substitution and body extension. |
| `M-REST` | Same-witness result/future-port relation, body return, effect/continuation preservation, full preservation/progress and unavailable-step exclusion. R342 does not claim these. |

The exact falsifier is an authentic finite typed K0 value/evaluation whose
runtime handle has a mismatched literal payload, closure formal/body/capture,
parameter cell or source-relevant lookup; or a Function-typed source value
that violates the proved canonical form. A missing induction premise is
recorded as OPEN, not as a compiler counterexample. R341's conditional S0,
full N/cache/coverage, W/Z, model existence, principality, original A/B,
export transport, whole M and production remain open.
