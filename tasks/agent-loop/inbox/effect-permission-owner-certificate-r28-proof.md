# R28 proof leaf — stage 1 frozen handoff

Assignment: /root/r28_proof; registered lean_prover leaf; session R28-20261030.
Revision: 1. Outcome: candidate, constructed but unchecked. Parent and production OPEN.
Primary's runtime launch message grants stage 1 <=350 seconds, total <=1000.
No children, Git, compiler edits, dependencies, root imports or shared records.

## Frozen inputs and artifact

Contract revision 1: tasks/agent-loop/sprints/effect-permission-native-callback-grant-20261030-r28.md
SHA-256 fa1a6f2e450169748e0696fb607963147a46cc4e6c464087cdefcacec383d89a.
Schema SHA-256 fb46c1c031ee9132385c2170c22cbf8ea5eb27a8dc176ce0ba6356b7cf4a71ea.
Inputs SHA-256 ca55123ef61014258f9d60d327cf0a3b0db069231bcdfa3563b812913ff901f1.
Source baseline c9e315208cb04bcc4fe8c3595d929fb76538f1cd. The input manifest pins
machine.rs 4fe3de685650761767be313285321e548964b41900c3aae7f5f434d48034395d
and receiving.rs e6b22598a0d11a21fba260cdbc5b4ace3690cf9b21e51beb61d8cc967511fffd.
These are admission pins, not a claim that the concurrently edited Rust candidate
has those current bytes. Fresh Rust source and JSON hashes are needed on resume.

Only changed source:
`isolated/ep-owner-certificate-r28/project/notes/theory/lean/YulangClosure/NativeCallbackGrantBridge.lean`
SHA-256 7089b047821ed82e715b4230c47e36f5fec231bf431ec6d26501137f8a358c18.
Read-only R26 overlay freshly hashed unchanged:
0621f43739c12ce1e7919a50de129414a4748d8359bf46740babd69f4854011e.
This handoff is the only other changed path. No scratch/cache/generated writes.

## Source claim and correspondence

Read root AGENTS.md, AGENTS.pre-sprint.md, rules/goal-driven-sprints.md,
rules/design-authority.md, the proof skill and both references, R28 contract,
schema and inputs, current.json and agent-loop README, pinned Lean config and
relevant Lean README. The original parent is
`YulangClosure.SourceProblem.InferenceSoundness` in Contracts.lean:

```lean
∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
  ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a
```

Preservation manuscript §§1,3,5 retains every original supported program,
complete Call/effects, original scope and one shared source witness. The
birth-level/SCC correction §§2–6 uses paths entirely within one immutable
Value birth level; it does not prove the lawful joint lift. The selected
annotation policy §§1.1–1.2,3–5 separates permission, actual inflow and residual;
unknown dependencies and independent write contributions survive. These sources
were read directly; no research draft supplies semantic authority here.

Native owner map inspected directly:

- receiving.rs CallbackResultSchema::from_parameter: resolved concrete result
  row on the reviewed unit-to-int callback; no symbolic row variables.
- callback_entry/receipt: invocation receiver, incoming value/view, fresh entry
  view, source lambda/formal receipt.
- callback_entry_for_apply: direct parameter Name's owner/view/formal receipt,
  source Name root/occurrence; machine.rs operation Apply selects actual
  Parameter/Observe Name before calling this constructor.
- callback_use: entry/source view/value and freshly minted result view/receipt.
- callback_execution/execution/authentic_execution: owning execution-table
  index and exact result view/receipt.
- observe/local_grant/callback_grant: event, observer bound, authenticated
  execution, active candidate receiver and resolved family joins. The Name
  join is **not** a callback_grant guard; it belongs to the preceding direct
  Name Apply construction.
- machine.rs OperationResultConsumer: opens callback execution; native request
  execution allocates event and observations. Catch checks resolved declaration,
  live installation and local Grant before committing the exact arm.

The artifact defines independent raw entry/Name/use/receipt observations,
checks their joins, then projects a finite R26 slice. Site keys preserve only
root and occurrence, setting byte spans to zero: existing native guards do not
establish a theorem about complete byte-span identity. Original raw Site values
remain in records. No spelling, row-root equality or result-value identity is
used. Generic validators are mathematical record checks; they are not yet
proved equal to the Rust functions or instantiated from authenticated output.

## Theorem types as written — NOT printed or kernel checked

All names below have prefix `YulangClosure.NativeCallbackGrantBridge`.

```lean
constructor_success_use {e : NativeEntry} {n : NativeName} {u : NativeUse}
  (success : validateConstructors e n u = true) :
  UseReady (entry e) (name n) (callbackUse e n u)

constructor_success_port {b : NativeObservation}
  (constructors : validateConstructors b.entryRecord b.nameRecord b.useRecord = true)
  (execution : validateExecution b = true) :
  PortReady (portSlice b) b.request (permission b.entryRecord)

constructor_success_catch {b : NativeObservation} {c : NativeCatch}
  (constructors : validateConstructors b.entryRecord b.nameRecord b.useRecord = true)
  (execution : validateExecution b = true) (caught : validateCatch b c = true) :
  CatchReady (catchSlice b c) b.request (consumerKey c.consumer) (permission b.entryRecord)

permission_does_not_emit (s : State) (p : Permission) :
  ({s with permissions := p :: s.permissions} : State).pending = s.pending ∧
  ({s with permissions := p :: s.permissions} : State).emitted = s.emitted
```

No theorem assumes UseReady, PortReady, History, native Grant or the desired
result. Success of these candidate record validators still requires actual
source/native evidence. In particular this stage does not establish native
local_grant/callback_grant success or construct source annotation formation.

## Execution and resource receipt

Actual read/hash/search/write commands ran through exec_command, exits 0 except
an early exploratory rg over nonexistent guessed contract/input directories
(the shell's final pipeline exit was 0 and no proof claim relied on that search).
The meaningful hash command was `sha256sum` on the artifact, R26 overlay and the
three R28 inputs; results appear above. `rg` on the changed source found no
sorry/admit/project axiom/checker bypass declaration. No Lean, Lake, checker,
Cargo, runtime or external network process was invoked by this leaf. No actual
Lean version output, diagnostics, printed types or axiom report exists yet.
Read toolchain pin: leanprover/lean4:v4.35.0. Manifest packages: []. Lake config:
YulangClosure, -j1, -M1024. Toolchain/manifests remain unchanged.

First explicit clock read: 2026-10-29 22:29:51 UTC; post-construction clock:
22:31:37 UTC. Charge the full stage-1 cap of 350 seconds conservatively; reserve
650 seconds for a fresh primary resume. Lean audits used: 0/2; audit time: 0/120.
No heavy process launched, cache touched or process left running.

## Parent application and first remaining premise

The candidate implications can supply the R26 UseReady/PortReady/CatchReady
premises for a finite supplied slice. They do not construct an R26 History or
an original source derivation. First missing evidence: Rust owner's frozen
JSON and source hashes authenticate the direct Name Apply/store joins,
execution observation, active local Grant query, actual emitted request and
exact Catch/arm. The callback's concrete resolved effect identity must have an
injective encoding; annotation polarity/shape must come from source formation.
Then Luna opens the serialized audit window and resumes this leaf to instantiate
records, run the pinned checker (at most two audits/120 aggregate seconds),
inspect all printed theorem types and full axiom outputs, and resolve actual
compiler diagnostics. Independent review belongs to Luna's fresh reviewer.

Omitted/open: authenticated concrete instance; proof that these candidate
validators coincide with native constructors; complete local Grant branch
projection; byte-span identity; effect type arguments (selected callback has
none); symbolic rows; computation-formal/RootComp; full History; companion
owner/template/native evidence; source constraint propagation/freshening/
extrusion; original joint source strategy; principality; termination; production.
No source scope or parent quantifier has been reduced to claim closure.

Writes stopped: stage-1 artifact and this revision are frozen on return. No
descendants, generated outputs, scratch files or live processes. Resume only
on a fresh primary receipt with authenticated JSON and an audit window.
