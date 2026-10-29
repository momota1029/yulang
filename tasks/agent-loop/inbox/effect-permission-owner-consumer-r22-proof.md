# R22 proof handoff

Sprint: CALLBACK-RESULT-OWNER-CONSUMER/20261030-R22.
Contract: `tasks/agent-loop/sprints/effect-permission-owner-consumer-20261030-r22.md`.
Assignment revision: 2, FROZEN CANDIDATE / CONSTRUCTED-BUT-UNCHECKED.
Author: `/root/effect_permission_owner_consumer_r22_lean`; no children/coauthors.
Requested model/effort: gpt-6.1-sol/high; observed runtime model/effort UNKNOWN.
Baseline: `fcd38f02a33cb28b2c5c56dc6f1a48b8838e1dc4`.

## Authority and original scope

Read root AGENTS.md, AGENTS.pre-sprint.md, rules/goal-driven-sprints.md,
current.json, agent-loop README, fixed R22 packet, Lean skill and its sources /
execution references. Semantic authority is
`notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1.1–1.2
(SHA256 a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18):
the exact annotated callback returns 1, annotation grants permission without
creating inflow, and independent write remains outward. The companion file
SHA256 is 0530c7ce6ef6d881d3106c9f69b42a992d701928f163c4c34c8b14f89408b6c7.
These are two independent source occurrences; no cross-source evidence join.

Original parent: `notes/theory/2026-10-13-intrusion-source-preservation-proof.md`
§§1,3,5 (SHA256 3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271),
with `2026-10-24-birth-level-scc-intrusion.md` correction. Quantifiers still range
over every supported original source program, lawful finite construction history,
and actual retained extrusion occurrence, with the original scopes and shared
witness. No original A/B, soundness, principality, termination or production
claim is discharged here.

Original operational manuscript located at
`docs/yulang-operational-type-safety-ja.tex`, sec:types, sec:machine, thm:safety.
Its opening correction explicitly withdraws source correspondence for uniform
renaming of historical receiver evidence. Consulted corrected value/continuation
§§1–4 and correlated-handler-observation §§1–3; these are candidate-machine
mathematics and are not semantic authority for this runtime. Also read the
whole-proof closure §4 source/native premises and the authoritative inference
principles. The old callback transport and bridge drafts are source locators,
not proofs of production behavior.

## Exact artifact and representation

Writes only:

- `notes/theory/lean/YulangClosure/CallbackResultOwnerConsumer.lean`;
- this handoff;
- `isolated/ep-owner-consumer-r22/lean-scratch` (unaltered configuration copies,
  isolated project/module, temporary outputs only).

Module imports only Init. It does not import or edit the broken/unleased
FormalPermissionSourceTransport, public root, compiler, toolchain, manifests,
lockfiles, expected outputs, central records or other workers' files.

Fully qualified namespace: `YulangClosure.CallbackResultOwnerConsumer`.
`allocateEntry`/`allocateUse` retain independent original formal and actual-use
receipts and inherited image/unknown fields. `CallbackGrant` represents the
callback branch's successful-lookup guard conjunction, not source typing:
active original invocation, exact request event and observer, authentic historic
execution, entry/use/result-view/receipt joins, original-owner/formal/source
site equality, and separate family permission membership.

`Step` represents the delimiter control projection of machine.rs transitions:
dormant OperationResultConsumer preparation; result consumer opening its fresh
execution; template View replay; normal return/request-unwind close of the exact
view/receipt/occurrence; receiver retirement. Stack order is explicitly top
first, reversed from Rust Vec storage order. `Delimited` is a frame projection
invariant, independent of grant/typing definitions. Close retains historical
arena and current original-owner activity. Retiring that original receiver
invalidates callback grant without rewriting historical receipts.

Omissions remain explicit: source schema shape/formation and arena-lookup
success; receipt-index/name-read authentication; complete machine states and
all ordinary frame constructors; fresh-handle arena construction correspondence;
RootComp companion boundary/image search; payload matching/arm ordering,
installation validation, committed Catch selection and returned value; general
closures, annotations, operation type arguments, foreign continuations and the
whole source language. `operationFilter` covers only the resolved operation-ID
mismatch retaining the same write event; it does not prove the outer consumer.
No Rust-to-Lean bridge is assumed. No concrete trace instance is asserted.

Candidate theorem declarations (exact signatures are in the module; printed
kernel types and per-root axiom reports are NOT YET AVAILABLE):

- allocated_entry_owner;
- allocated_use_owner;
- step_preserves_delimiters;
- close_preserves_observation;
- close_preserves_grant;
- retired_receiver_rejected;
- sibling_event_rejected;
- sibling_receiver_rejected;
- absent_permission_rejected;
- distinct_operation_keeps_event.

## Execution gate and next premise

No Lean/Lake execution has occurred. Packet forbids audits until the sole Cargo
invocation is terminal. No checker, model or runtime receipt is invented.
Installed native Lake file exists at
`/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`;
its version has not yet been executed in this assignment.
Project pin is Lean 4.35.0, no external packages. Input configuration hashes:

- lean-toolchain ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c;
- lakefile.toml 212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4;
- lake-manifest.json 058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3.

First application premise: authenticated concrete Rust source/arena transitions
from this invocation, including source root/occurrence, original receiver,
entry/use/view/receipt IDs and the same operation request observation. Rust
producer owns this premise; Luna authenticates it. Subsequent premises are the
actual committed local Catch/return 1 and the independently authenticated
RootComp signal/write/outer-receive chain. These remain OPEN.

Audit plan when Luna reports Cargo terminal: skill checker in isolated project,
TMPDIR within leased scratch; at most two serialized audits, each <=90 seconds,
combined <=120 seconds, one CPU and <=1 GiB RSS. Preserve first errors and repairs.
Independent review and production authority remain Luna-owned.

Resource state: no heavy process launched, no dependencies installed, no Git
operations. Source construction frozen on Luna instruction; audit blocked.

## Frozen revision 2 / writes stopped

Luna's explicit freeze: stop writes until the Rust source review/Cargo gate is
resolved; resume this lane only after a concrete authenticated trace exists.
No audit is authorized or executed at this freeze. Version/exit/axiom results:
NOT_RUN / NOT_AVAILABLE for every candidate declaration. Execution unavailable
by packet sequencing, rather than a mathematical counterexample or missing Lean.
The runner script is prepared only; its resource limits and command are a plan,
not measured usage. Construction CPU/peak RSS were not measured. No actual Rust
source-review ACCEPT, Cargo execution, decoder, or concrete trace is asserted.

Additional constructor/guard work in this revision:

- checkedEntry / checked_entry_origin derive original entry owner, schema,
  entry-view kind, formal receipt identity/owner/slot from the successful option
  equation, after the actual incoming-view lookup.
- checkedApply / checked_apply_identity retain the original formal and actual
  Name receipts separately, and validate entry kind/formal/value/view/receiver
  plus actual callee source root and occurrence. The formal-slot comparison here
  intentionally matches Rust's occurrence-only test; grant checks full Site.
- checkedUse / checked_use_owner derive original invocation owner and exact
  source view/value, use entry handle and fresh actual Apply receipt fields from
  the successful source guard equation.
- checkedExecution / checked_execution_identity derive exact use/result-view/
  receipt/Apply joins and fresh execution occurrence from successful execution.
  Arena publication/readback and fresh-handle counter authentication remain open.
- grant_owner_lifetime extracts the same original live receiver, actual request
  event, historical authentic execution, actual-use receipt owner, formal receipt
  owner and independent formal permission from the actual guard conjunction.

OperationResultConsumer opening order relative to operation ReceiverReturn and
substitution, real request emission, arena joins, committed Catch selection,
return 1, and the companion RootComp write chain require the authenticated Rust
trace. No theorem silently substitutes the delimiter projection for these facts.

No imported project dependencies and no root import changes. Source grep found
only `import Init`, no sorry/admit/project axiom/checker bypass declarations.
There is no per-root axiom receipt until actual pinned execution is authorized.
The checker harness uses TMPDIR inside the leased scratch and bounds each planned
attempt to checker55/wrapper60 seconds, at most two serialized attempts. It has
not run; `audit-1.log/json` and `audit-2.log/json` do not exist.

Frozen module SHA256: `8b76265d486786844bb1e649ac676fe49988b903e742532d40b86104c8783f27`.
The exact fully qualified prefix below is
`YulangClosure.CallbackResultOwnerConsumer.`. These are source-declared
signatures, NOT printed/accepted kernel types:

```lean
theorem allocated_entry_owner (schema : Schema) (receiver value incomingHandle
    entryHandle viewHandle receiptHandle : Nat) (incoming : View) :
    (allocateEntry schema receiver value incomingHandle entryHandle viewHandle receiptHandle incoming).2.2.owner =
      .invocation receiver ∧
    (allocateEntry schema receiver value incomingHandle entryHandle viewHandle receiptHandle incoming).2.2.formal =
      some schema.formal

theorem allocated_use_owner (entryHandle useHandle resultView receiptHandle receiver
    sourceView value : Nat) (apply : Site) (source : View) :
    (allocateUse entryHandle useHandle resultView receiptHandle receiver sourceView value apply source).2.2.owner =
      .invocation receiver ∧
    (allocateUse entryHandle useHandle resultView receiptHandle receiver sourceView value apply source).2.2.slot = apply ∧
    (allocateUse entryHandle useHandle resultView receiptHandle receiver sourceView value apply source).2.1.kind =
      .callbackResult useHandle

theorem checked_apply_identity {e : Entry} {entryHandle value viewHandle formal : Nat}
    {owner : Owner} {callee : Site} {entryView incoming : View}
    {formalReceipt nameReceipt : Receipt} {selected : Nat}
    (built : checkedApply e entryHandle value viewHandle formal owner callee entryView incoming
      formalReceipt nameReceipt = some selected) :
    selected = entryHandle ∧ owner = .invocation e.receiver ∧
    e.view = viewHandle ∧ formalReceipt.formal = some formal ∧
    nameReceipt.slot = callee

theorem checked_entry_origin {schema : Schema} {owner : Owner}
    {value incomingHandle entryHandle viewHandle receiptHandle : Nat}
    {incoming : View} {out : Entry × View × Receipt}
    (built : checkedEntry schema owner value incomingHandle entryHandle viewHandle receiptHandle incoming = some out) :
    owner = .invocation out.1.receiver ∧ out.1.schema = schema ∧
    out.1.view = viewHandle ∧ out.1.formalReceipt = receiptHandle ∧
    out.2.1.kind = .callbackEntry entryHandle ∧ out.2.2.owner = owner ∧
    out.2.2.view = viewHandle ∧ out.2.2.formal = some schema.formal ∧
    out.2.2.slot = schema.lambda ∧ incoming.value = value

theorem checked_use_owner {e : Entry} {owner : Owner}
    {value sourceView entryHandle useHandle resultView receiptHandle : Nat}
    {apply : Site} {source : View} {out : Use × View × Receipt}
    (built : checkedUse e owner value sourceView entryHandle useHandle resultView receiptHandle apply source = some out) :
    owner = .invocation e.receiver ∧ e.value = value ∧ e.view = sourceView ∧
    out.1.entry = entryHandle ∧ out.1.sourceView = e.view ∧
    out.2.2.owner = owner ∧ out.2.2.view = resultView ∧
    out.2.2.slot = apply ∧ out.2.2.formal = none

theorem checked_execution_identity {u : Use} {useHandle viewHandle receiptHandle : Nat}
    {view : View} {receipt : Receipt} {arena : ExecutionArena}
    {out : Execution × ExecutionArena}
    (built : checkedExecution u useHandle viewHandle receiptHandle view receipt arena = some out) :
    u.resultView = out.1.view ∧ u.receipt = out.1.receipt ∧
    receipt.view = out.1.view ∧ receipt.formal = none ∧ receipt.slot = u.apply ∧
    out.1.occurrence = arena.length ∧ out.2 = arena ++ [(viewHandle, receiptHandle)]

theorem step_preserves_delimiters {before after : Machine}
    (step : Step before after) (inv : Delimited before) : Delimited after

theorem close_preserves_observation (s : Machine) (rest : List Frame)
    (xs : List Execution) (o : Observation)
    (auth : Authentic s.executions o.execution) :
    Authentic ({s with frames

theorem close_preserves_grant (s : Machine) (rest : List Frame)
    (xs : List Execution) (g : GrantOperands) (nextObserver event receiver family : Nat)
    (grant : CallbackGrant g s.executions nextObserver event receiver family s.active) :
    CallbackGrant g ({s with frames

theorem grant_owner_lifetime {g : GrantOperands} {s : Machine}
    {nextObserver event receiver family : Nat}
    (grant : CallbackGrant g s.executions nextObserver event receiver family s.active) :
    g.entry.receiver = receiver ∧ s.active receiver = true ∧
    g.observation.event = event ∧ Authentic s.executions g.observation.execution ∧
    g.actualReceipt.owner = .invocation receiver ∧
    g.formalReceipt.owner = .invocation receiver ∧ family ∈ g.entry.schema.families

theorem retired_receiver_rejected (g : GrantOperands) (s : Machine)
    (nextObserver event receiver family : Nat) :
    ¬ CallbackGrant g s.executions nextObserver event receiver family
      (fun id => if id = receiver then false else s.active id)

theorem sibling_event_rejected (g : GrantOperands) (arena : ExecutionArena)
    (nextObserver event receiver family : Nat) (active : Nat → Bool)
    (different : g.observation.event ≠ event) :
    ¬ CallbackGrant g arena nextObserver event receiver family active

theorem sibling_receiver_rejected (g : GrantOperands) (arena : ExecutionArena)
    (nextObserver event receiver family : Nat) (active : Nat → Bool)
    (different : g.entry.receiver ≠ receiver) :
    ¬ CallbackGrant g arena nextObserver event receiver family active

theorem absent_permission_rejected (g : GrantOperands) (arena : ExecutionArena)
    (nextObserver event receiver family : Nat) (active : Nat → Bool)
    (absent : family ∉ g.entry.schema.families) :
    ¬ CallbackGrant g arena nextObserver event receiver family active

theorem distinct_operation_keeps_event (signalOperation writeOperation writeEvent : Nat)
    (distinct : signalOperation ≠ writeOperation) :
    operationFilter signalOperation writeOperation writeEvent = some writeEvent
```

First remaining premise/owner: the Rust producer supplies concrete successful
source-schema and arena constructor/readback transitions from the exact source
occurrence and invocation; Luna authenticates the frozen trace. If a guard or
transition fails, preserve that actual first failure, keep the corresponding
application open, and return it to Luna. Independent review remains unassigned
by this leaf. Original parent claims and production gates stay OPEN.

Writes stopped after this revision and the frozen manifest below. No children,
scheduling, Git, installs, third-party contact or unleased writes occurred.
