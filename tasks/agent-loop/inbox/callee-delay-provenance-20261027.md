# CALLEE-DELAY-PROVENANCE-20261027/r1 — proof handoff

State: STOPPED; constructive local data refinement CHECKER-ACCEPTED; fresh
independent source/construction review PENDING. Original source/native parent,
whole-language safety, Effect hygiene, principality, progress/termination and
production remain OPEN. No source-qualified counterexample was established.

## Authority, runtime and frozen inputs

Contract SHA-256 `83548a4c9896155c2f0b4493a0f86519361ed27691968e0915a4927c0b96d3b0`.
Dependency baseline `f0acc5d1ab103adf4f41f49088b754231b665c1b`.
All 18 contract pins were verified against workspace bytes and `git show HEAD:path`
before writes; observed HEAD then was `9731c7b1562b12509a212bf461143dcc15cac3da`.
Primary's initial assignment HEAD was `9d167d117`; no direct dependency changed.
The exact dependency manifest is under the isolated proof root below. The 244
tracked Lean/config source inputs copied into the private project were compared
again to the workspace after checking and remained identical. No shared cache
was used or written.

Runtime agent `/root/callee_delay_proof`; independent runtime session ID UNKNOWN.
Requested model/effort `gpt-6.1-sol/high`; observed model/effort UNKNOWN. No
subagents, nested agent CLI, Git mutation, installs or dependency changes.

Applied `.agents/skills/yulang-lean-proofs/SKILL.md` and its execution/source
references, root AGENTS.md/AGENTS.pre-sprint.md, goal-driven-sprints and the fixed
packet. The original manuscript is
`notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §§1,3 (original A/B
scope and shared source strategy), with the authoritative birth-level correction
`notes/design/2026-10-24-birth-level-scc-intrusion.md` §§2–6. Whole-language target:
`docs/yulang-whole-proof-closure-ja.md` §§1–3. Corrected value/continuation draft:
`notes/theory/2026-10-24-corrected-core-value-continuation.md` §§1,5–7; the draft is
not semantic approval or proof of the native bridge. The source Call realization
manuscript's receipt/Force distinction was located in
`notes/theory/2026-10-08-call-semantic-input-realization.md` §§4–6; its obligations
are not supplied by this local theorem.

## Exact construction and source owners

All new names below are under `YulangClosure.OriginalCalleeDelayProvenance`.

- Rust `machine.rs:1181–1198,2701–2718`: `Raw`, `RuntimeValue`, `ValueKind`,
  `Executable`, `allocate`, `allocate_facts`, `allocate_preserves_old` represent
  dense values and a separate sparse executable map. The handle is exactly old
  values.length. Source site, Computation kind, label, decoded code and saved
  environment are retained. Old values/map entries are derived unchanged and
  the fresh handle is distinct from every old value index.
- Rust `machine.rs:2028–2045,2585–2596`: `Code`, `Instruction`,
  `directFormalRoot`, `direct_formal_path`, `allocate_keeps_formal_path` follow
  program lookup, Parameter/Execute test, lexical binder lookup, initialized
  cell lookup, then Computation role. Existing Arena/native-walk correspondence
  requires its original Valid/older-parent conditions; this packet does not
  assert them for every Rust environment or infer them from successful lookup.
- Rust `receiving.rs:208–222`: `Metadata`, `delayMetadata`, `appendView`,
  `prepare`, `inherited_metadata`, `default_metadata`, `prepared_view`,
  `prepared_preserves_views` construct a separate fresh view at old views.length.
  Inherited image and unknown are copied exactly; absent inheritance gives
  (None,true); the new kind is Ordinary. Other old kinds are retained opaque
  tags. No receipt store/index mutation occurs. Missing inherited-view lookup
  is marked as a Rust indexing/panic boundary, not RuntimeUnavailable.
- `project`/`Represents`, `append_view_refines`, `prepare_refines` give the
  component data refinement from the dense lists/sparse executable insertion
  to the established suffix machine. The list append equation is proved via
  existing vector_store_push, not assumed in a simulation record.
- Rust `machine.rs:1223–1299`: `run`, `allocated_value_prefix`,
  `allocated_demand_represents` compose preparation with the established
  `OriginalValueEntryDemand.invoke` Closure/Value suffix. The provider site is
  read from the existing callee RuntimeValue. The same constructor-allocated
  handle enters execute, the argument environment is its saved environment,
  receiver-return/value-entry frames come from the suffix, and the resulting
  projected demand is derived by Represents. This covers any decoded Source
  expression argument, not merely Name arguments. The success premises are the
  concrete program/metadata/old-value/provider/Closure lookups, Value role,
  receiver capacity and existing plain-substitution branch; there is no assumed
  Force result or source/native simulation premise. The appended view, complete
  receipt store/index and dictionary are preserved through that plain prefix.
- `dictionary_failure_order` applies the existing
  `OriginalValueEntryDemand.dictionary_failure_after_allocation`: Delay
  value/view exist before receiver allocation; failed dictionary composition's
  changed dictionary survives with receiver allocation but no entry frames.
  The raw compose equation remains at the dictionary owner. This is a failure
  poststate theorem, not a rollback or cleanup claim.
- `inherited_failure_order`: inherited-view indexing failure retains the already
  allocated value/executable, with no view append, invocation allocation,
  substitution or frame setup. `run` also retains a provider-index boundary.

`OriginalIdentityCarrier.Allocation` is not used as evidence for either concrete
Rust map. Its optional closure-store allocation remains a distinct prior result.
No root import was changed; this module is independently buildable.

## Receipt consumer, parent application and exact remaining obligation

Pinned source owners: `OriginalFormalShared.receiptBinder`, the original
Value-entry clause in `OriginalFormalShared.entryPremises`,
`OriginalRecursivePair.InvocationMove.receipt` then `.force`, and
`OriginalIdentityRealization.receipt_recovers_call` (also exposed by
`OriginalValueEntryDemand.source_call_recovery`).
`source_receipt_record` derives the existing full record
(owner = current invocation, view = entry.carrier.view, site = entry.slot,
formal = some entry.formal). `preforce_receipts_unchanged` and
`allocated_demand_represents` preserve the *entire* native receipt store/index;
no history is identified by count and no hypothetical missing record is
inferred merely from a size comparison.

Rust `machine.rs:1438–1465` enters the ValueEntry frame only after Force returns.
Its callback branch validates current invocation, schema/formal/source-root,
nonunit/nonrecord pattern and returned Value role. Rust
`receiving.rs:300–335` then validates the returned value against its incoming
view, allocates a new callback view, and calls receipt at that new view with
owner Invocation(entry_receiver), site schema.lambda and formal schema.formal.id.
Thus source pre-Force receipt, pre-Force demand, and post-Force callback receipt
remain distinct: callback receipt concerns the returned callback value/new view,
not automatically the Delay argument value/view. The callback checks, callback
entry store and later callback-use consumer are not formalized in the new module.

Applying the local result to the parent removes independently chosen Delay
handle/view from the native Closure/Value demand prefix. It does not construct
source Parameter receipt admission. The first source-consumer premise still
missing at this cut is exactly

```lean
Admitted operator readout admissions
  (environment.extend (invocationBinder parameter) invocation)
  (receiptBinder parameter) receipt
```

for a receipt/readout genuinely derived from this prepared native pre-Force
state, together with the corresponding decode equation required by
`OriginalIdentityRealization.receipt_recovers_call`. Its owner is the primary's
original source/native Parameter interpretation lane. No equation currently
proves that this source receipt payload carries the same original invocation,
carrier view, formal site, owner and checked full CallInput as this demand; no
existing theorem makes the later callback record equal to it. Do not fill this
premise by assuming a simulation law or minting a receipt in the model.

Independent earlier input ownership remains explicit: the frontend must align
program label/body/Parameter-Execute instruction with the original source
expression, and the raw selected Closure/RuntimeValue with its original source
Parameter/provider. `Code.body` and `Code.instruction` are independent decoded
data; no frontend correctness equation is asserted by their structure. Raw
lookup/preservation theorems are not a compiler theorem. The previously open
Return-assignment versus `OriginalNameForceExtraction.Native.fields` equation,
source demand/event readout, guards/world laws, full Call/effects and common
source witness remain open. No hypothesis or supported source form was removed
from the original A/B statement.

Represented: inert allocation for all decoded argument syntax; direct formal
and default inheritance; dense old-value/view preservation; selected ordinary
Closure/Value plain entry; dictionary failure order; panic/projection boundaries;
original source receipt record. Omitted from claimed operational coverage:
frontend decoding and source/closure introduction, full Rust memory/panic
semantics, primitive/continuation/operation/Computation-entry alternatives,
dictionary-success execution, actual Force/Return, callback receipt execution,
unit/record callback binding, annotated-view semantic meaning and source admission.
`run` reuses the suffix outsideProjection boundary and is not asserted to match
all other Callee branches. Those branches remain in the unchanged parent domain.

## Actual verification

Native executable resolved by read-only `elan which lake`:
`/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`.
Actual commands from notes/theory/lean, exit 0:

```text
lake --version
Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)
lake env lean --version
Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
```

All checking ran serially in the isolated project under
`/tmp/yulang-callee-delay-provenance-20261027/proof/project`, with
LEAN_NUM_THREADS=1, pinned project -j1 -M1024, at most 120 sec per invocation.
Exactly six checker invocations used 56.231813675 aggregate wall seconds; no
checker budget remains. Invocations 1 and 2 failed and are retained. The first
had a reserved `syntax` field name and reduction/type mismatches; the second
exposed True-versus-equality/rewrite issues. Failed recovery-generated sorry
warnings are failure evidence, not delivered holes. Invocations 3/4 built the
intermediate/final module (29 jobs); 5 passed the skill helper for all 16 authored
roots; 6 passed the complete reusable census. No final warning or failure.
No full-root/default build was claimed or required for this isolated no-import
packet; no root integration claim follows from the target build.

Complete exact command arrays/exits/durations:

```json
[
  {
    "n": 1,
    "command": [
      "/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake",
      "build",
      "+YulangClosure.OriginalCalleeDelayProvenance"
    ],
    "exit": 1,
    "seconds": 50.033930075999706
  },
  {
    "n": 2,
    "command": [
      "/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake",
      "build",
      "+YulangClosure.OriginalCalleeDelayProvenance"
    ],
    "exit": 1,
    "seconds": 0.9676984389998324
  },
  {
    "n": 3,
    "command": [
      "/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake",
      "build",
      "+YulangClosure.OriginalCalleeDelayProvenance"
    ],
    "exit": 0,
    "seconds": 0.9694815650000237
  },
  {
    "n": 4,
    "command": [
      "/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake",
      "build",
      "+YulangClosure.OriginalCalleeDelayProvenance"
    ],
    "exit": 0,
    "seconds": 1.0675054180001098
  },
  {
    "n": 5,
    "command": [
      "python3",
      "/home/momota1029/rust/yulang/.agents/skills/yulang-lean-proofs/scripts/check_lean.py",
      "--project",
      "/tmp/yulang-callee-delay-provenance-20261027/proof/project",
      "--lake",
      "/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake",
      "--timeout",
      "120",
      "--module",
      "YulangClosure.OriginalCalleeDelayProvenance",
      "--theorem",
      "YulangClosure.OriginalCalleeDelayProvenance.append_view_refines",
      "--theorem",
      "YulangClosure.OriginalCalleeDelayProvenance.allocate_facts",
      "--theorem",
      "YulangClosure.OriginalCalleeDelayProvenance.allocate_preserves_old",
      "--theorem",
      "YulangClosure.OriginalCalleeDelayProvenance.direct_formal_path",
      "--theorem",
      "YulangClosure.OriginalCalleeDelayProvenance.allocate_keeps_formal_path",
      "--theorem",
      "YulangClosure.OriginalCalleeDelayProvenance.inherited_metadata",
      "--theorem",
      "YulangClosure.OriginalCalleeDelayProvenance.default_metadata",
      "--theorem",
      "YulangClosure.OriginalCalleeDelayProvenance.prepare_refines",
      "--theorem",
      "YulangClosure.OriginalCalleeDelayProvenance.prepared_view",
      "--theorem",
      "YulangClosure.OriginalCalleeDelayProvenance.prepared_preserves_views",
      "--theorem",
      "YulangClosure.OriginalCalleeDelayProvenance.allocated_value_prefix",
      "--theorem",
      "YulangClosure.OriginalCalleeDelayProvenance.allocated_demand_represents",
      "--theorem",
      "YulangClosure.OriginalCalleeDelayProvenance.dictionary_failure_order",
      "--theorem",
      "YulangClosure.OriginalCalleeDelayProvenance.inherited_failure_order",
      "--theorem",
      "YulangClosure.OriginalCalleeDelayProvenance.source_receipt_record",
      "--theorem",
      "YulangClosure.OriginalCalleeDelayProvenance.preforce_receipts_unchanged"
    ],
    "exit": 0,
    "seconds": 2.4264815900005487
  },
  {
    "n": 6,
    "command": [
      "/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake",
      "env",
      "lean",
      "-j1",
      "-M1024",
      "AuditOriginalCalleeDelayProvenance.lean"
    ],
    "exit": 0,
    "seconds": 0.7667165869997916
  }
]
```

The audit prints full types and #print axioms for **all 254 originating
constants, including all 78 originating theorem declarations (16 authored plus
62 generated)**. Every complete line is retained in `check-06.log`, not truncated
in that file. It rejects project axioms and transitive axioms other than propext,
Classical.choice and Quot.sound. The named helper independently checked each of
the 16 authored declaration kinds. Exact authored types/axioms are reproduced
below; generated theorem types/axioms are in the complete census log. Final
source search for sorry/admit/project axioms/kernel bypass/native_decide across
both new files and directly used prior proof owners had no matches (rg exit 1).
This is author-owned mechanical kernel checking, not independent review, verified
Rust execution, semantic adoption or production certification.

## Frozen hashes, artifacts and cessation

Only these repository paths changed:

```text
3acb041c530b19e78703b3f3030edd1b304ab7c20329974f0afc2d387428dbfe  notes/theory/lean/YulangClosure/OriginalCalleeDelayProvenance.lean
18516d704c6d884505a59343083c023ed583c7213fb6ca858dfbf12c3c23eba6  notes/theory/lean/AuditOriginalCalleeDelayProvenance.lean
tasks/agent-loop/inbox/callee-delay-provenance-20261027.md  (this handoff; external hash receipt)
```

Private evidence (all beneath the exact leased proof root):

```text
a603b549de4aada6377c2d5b0b78a01bcaf62ec2821a8abe8b4641953bcf0eb5  /tmp/yulang-callee-delay-provenance-20261027/proof/authored-theorems.json
e0526ce0189a0163e9bb3c3db038df04bdaed7188aca2622809bd24a844f6528  /tmp/yulang-callee-delay-provenance-20261027/proof/authored-types-and-axioms.txt
e8742f6a3e17523665b29b85303222963ae603ed7a48c23a9794842c78ed2241  /tmp/yulang-callee-delay-provenance-20261027/proof/check-01.log
29e37d0304a903ccd39508fb06f14976d6beaece7ce80c33999bb7998c4a67a6  /tmp/yulang-callee-delay-provenance-20261027/proof/check-02.log
b2e9520cc019a3f64514c546636134df1dcb6271586f336bc066302162efc9d6  /tmp/yulang-callee-delay-provenance-20261027/proof/check-03.log
f410e70f00fa64178659aad987c89e28bf6caf0965e896a66ca7e4d467107178  /tmp/yulang-callee-delay-provenance-20261027/proof/check-04.log
41ceec9c8ac39af0feb6ed7bc2054eace86b045784fa7db7505503a9851e8d85  /tmp/yulang-callee-delay-provenance-20261027/proof/check-05.log
5a065e452bc321bd4bd241e1a0d844b2929f5c8317e04e2a462c1af235ab80f8  /tmp/yulang-callee-delay-provenance-20261027/proof/check-06.log
b9a8f33b338fe41cab01aff08f85e0d5a31e398175491e131619dc7b52062a96  /tmp/yulang-callee-delay-provenance-20261027/proof/check.py
b74f1551e1cf8a93af2fbfa3b8f4cc8186e2d9f22d68df546b2049ba2c47192c  /tmp/yulang-callee-delay-provenance-20261027/proof/commands.jsonl
8b8af06d1c7b453d82f19557eb10a4dffef392dda4a53023def7fd114be0de8c  /tmp/yulang-callee-delay-provenance-20261027/proof/dependency-manifest.json
eec7c122d5bf084152e430c69546d317547f074dca4b4b3197ef6674b9aaf778  /tmp/yulang-callee-delay-provenance-20261027/proof/failed-check-01-source.lean
4d6c4dec83f9c3c59743a844cc5397e1ac4479453ae9f8363faec2c8aa5cf4f8  /tmp/yulang-callee-delay-provenance-20261027/proof/failed-check-02-source.lean
00477e12358c20fe12696a86fa01cd6b0df2cf31ab21393f7ef537da820628ce  /tmp/yulang-callee-delay-provenance-20261027/proof/snapshot-manifest.json
```

Scratch source/cache outputs remain only in proof/project/.lake and the private
project. Failed source snapshots and raw logs remain intact. No compiler/Rust,
test/expectation, question, shared status/index, root import, rule/config,
toolchain/manifest/lockfile or Git file was edited. No install or global-default
change. All six checker drivers/process groups have returned; no worker child
exists. Resource ceiling observed: six calls/56.232 sec, single checker owner,
no heavy process left; total assignment remained below 1500 sec. OS peak memory
and CPU totals were not measured and are UNKNOWN. Proof and audit bytes were
frozen after invocation 4/6 respectively; this handoff is the final write.
Worker state: STOPPED; all writing and checking stopped before review/transfer.
Primary owns independent verification, review, adjudication and integration.

## Exact printed authored theorem types and complete axiom results

Fully qualified prefix: `YulangClosure.OriginalCalleeDelayProvenance`.
The complete originating census, including generated declarations, is the
hashed `check-06.log` above. These are the 16 authored roots as actually printed
by successful skill invocation 5:

```text
@YulangClosure.OriginalCalleeDelayProvenance.append_view_refines : ∀ {C Dict Rest Schema : Type}
  (r : YulangClosure.OriginalCalleeDelayProvenance.Raw C Dict Rest Schema) (handle : Nat)
  (data : YulangClosure.OriginalCalleeDelayProvenance.Metadata),
  YulangClosure.OriginalCalleeDelayProvenance.Represents
    (YulangClosure.OriginalCalleeDelayProvenance.appendView r handle data)
    (have __src := YulangClosure.OriginalCalleeDelayProvenance.project r;
    {
      world :=
        have __src := (YulangClosure.OriginalCalleeDelayProvenance.project r).world;
        { environments := __src.environments, cells := __src.cells,
          receiving :=
            have __src := (YulangClosure.OriginalCalleeDelayProvenance.project r).world.receiving;
            {
              views :=
                (YulangClosure.OriginalCalleeDelayProvenance.project r).world.receiving.views.push
                  { value := handle, data := data },
              receipts := __src.receipts, index := __src.index },
          control := __src.control, rest := __src.rest },
      dictionary := __src.dictionary, nextReceiver := __src.nextReceiver, frames := __src.frames,
      executables := __src.executables, state := __src.state })
'YulangClosure.OriginalCalleeDelayProvenance.append_view_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

@YulangClosure.OriginalCalleeDelayProvenance.allocate_facts : ∀ {C Dict Rest Schema : Type}
  (r : YulangClosure.OriginalCalleeDelayProvenance.Raw C Dict Rest Schema) (site : YulangClosure.OriginalSource.Site)
  (label environment : Nat) (code : YulangClosure.OriginalCalleeDelayProvenance.Code),
  r.program label = Option.some code →
    (YulangClosure.OriginalCalleeDelayProvenance.allocate r site label environment).values.length =
        r.values.length + 1 ∧
      (YulangClosure.OriginalWorldReadout.vectorStore
                (List.map Option.some
                  (YulangClosure.OriginalCalleeDelayProvenance.allocate r site label environment).values)).cell
            r.values.length =
          Option.some { source := site, kind := YulangClosure.OriginalCalleeDelayProvenance.ValueKind.computation } ∧
        (YulangClosure.OriginalCalleeDelayProvenance.project
                  (YulangClosure.OriginalCalleeDelayProvenance.allocate r site label environment)).executables
              r.values.length =
            Option.some (YulangClosure.OriginalValueEntryDemand.Executable.delay code.body environment) ∧
          (YulangClosure.OriginalCalleeDelayProvenance.allocate r site label environment).views = r.views ∧
            (YulangClosure.OriginalCalleeDelayProvenance.project
                  (YulangClosure.OriginalCalleeDelayProvenance.allocate r site label environment)).world =
              (YulangClosure.OriginalCalleeDelayProvenance.project r).world
'YulangClosure.OriginalCalleeDelayProvenance.allocate_facts' depends on axioms: [propext, Classical.choice, Quot.sound]

@YulangClosure.OriginalCalleeDelayProvenance.allocate_preserves_old : ∀ {C Dict Rest Schema : Type}
  (r : YulangClosure.OriginalCalleeDelayProvenance.Raw C Dict Rest Schema) (site : YulangClosure.OriginalSource.Site)
  (label environment handle : Nat),
  handle < r.values.length →
    (YulangClosure.OriginalWorldReadout.vectorStore
              (List.map Option.some
                (YulangClosure.OriginalCalleeDelayProvenance.allocate r site label environment).values)).cell
          handle =
        (YulangClosure.OriginalWorldReadout.vectorStore (List.map Option.some r.values)).cell handle ∧
      (YulangClosure.OriginalCalleeDelayProvenance.allocate r site label environment).executables handle =
          r.executables handle ∧
        r.values.length ≠ handle
'YulangClosure.OriginalCalleeDelayProvenance.allocate_preserves_old' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

@YulangClosure.OriginalCalleeDelayProvenance.direct_formal_path : ∀ {C Dict Rest Schema : Type}
  (r : YulangClosure.OriginalCalleeDelayProvenance.Raw C Dict Rest Schema) (label environment cell : Nat)
  (code : YulangClosure.OriginalCalleeDelayProvenance.Code) (parameter : YulangClosure.OriginalSource.Name)
  (received : YulangClosure.SourceIdentityWorld.Received Nat),
  r.program label = Option.some code →
    code.instruction = YulangClosure.OriginalCalleeDelayProvenance.Instruction.parameterExecute parameter →
      YulangClosure.NativeClosureEnvironment.lookupKey parameter r.skeleton.world.environments environment =
          Option.some cell →
        r.skeleton.world.cells.cell cell = Option.some received →
          YulangClosure.OriginalCalleeDelayProvenance.directFormalRoot r label environment =
            if received.interface = YulangClosure.SourceIdentityWorld.Entry.computation then Option.some received.view
            else Option.none
'YulangClosure.OriginalCalleeDelayProvenance.direct_formal_path' depends on axioms: [propext]

@YulangClosure.OriginalCalleeDelayProvenance.allocate_keeps_formal_path : ∀ {C Dict Rest Schema : Type}
  (r : YulangClosure.OriginalCalleeDelayProvenance.Raw C Dict Rest Schema) (site : YulangClosure.OriginalSource.Site)
  (label environment : Nat),
  YulangClosure.OriginalCalleeDelayProvenance.directFormalRoot
      (YulangClosure.OriginalCalleeDelayProvenance.allocate r site label environment) label environment =
    YulangClosure.OriginalCalleeDelayProvenance.directFormalRoot r label environment
'YulangClosure.OriginalCalleeDelayProvenance.allocate_keeps_formal_path' does not depend on any axioms

@YulangClosure.OriginalCalleeDelayProvenance.inherited_metadata : ∀ {C Dict Rest Schema : Type}
  (r : YulangClosure.OriginalCalleeDelayProvenance.Raw C Dict Rest Schema) (handle : Nat)
  (view : YulangClosure.SourceIdentityWorld.View Nat YulangClosure.OriginalCalleeDelayProvenance.Metadata),
  (YulangClosure.OriginalWorldReadout.vectorStore (List.map Option.some r.views)).cell handle = Option.some view →
    YulangClosure.OriginalCalleeDelayProvenance.delayMetadata r (Option.some handle) =
      Option.some
        { image := view.data.image, unknown := view.data.unknown,
          kind := YulangClosure.OriginalCalleeDelayProvenance.ViewKind.ordinary }
'YulangClosure.OriginalCalleeDelayProvenance.inherited_metadata' depends on axioms: [propext]

@YulangClosure.OriginalCalleeDelayProvenance.default_metadata : ∀ {C Dict Rest Schema : Type}
  (r : YulangClosure.OriginalCalleeDelayProvenance.Raw C Dict Rest Schema),
  YulangClosure.OriginalCalleeDelayProvenance.delayMetadata r Option.none =
    Option.some
      { image := Option.none, unknown := Bool.true,
        kind := YulangClosure.OriginalCalleeDelayProvenance.ViewKind.ordinary }
'YulangClosure.OriginalCalleeDelayProvenance.default_metadata' does not depend on any axioms

@YulangClosure.OriginalCalleeDelayProvenance.prepare_refines : ∀ {C Dict Rest Schema : Type}
  (r : YulangClosure.OriginalCalleeDelayProvenance.Raw C Dict Rest Schema) (site : YulangClosure.OriginalSource.Site)
  (label environment : Nat) (data : YulangClosure.OriginalCalleeDelayProvenance.Metadata),
  YulangClosure.OriginalCalleeDelayProvenance.delayMetadata r
        (YulangClosure.OriginalCalleeDelayProvenance.directFormalRoot r label environment) =
      Option.some data →
    YulangClosure.OriginalCalleeDelayProvenance.prepare r site label environment =
        (YulangClosure.OriginalCalleeDelayProvenance.appendView
            (YulangClosure.OriginalCalleeDelayProvenance.allocate r site label environment) r.values.length data,
          Except.ok r.views.length) ∧
      YulangClosure.OriginalCalleeDelayProvenance.Represents
        (YulangClosure.OriginalCalleeDelayProvenance.prepare r site label environment).fst
        (YulangClosure.OriginalCalleeDelayProvenance.project
          (YulangClosure.OriginalCalleeDelayProvenance.appendView
            (YulangClosure.OriginalCalleeDelayProvenance.allocate r site label environment) r.values.length data))
'YulangClosure.OriginalCalleeDelayProvenance.prepare_refines' depends on axioms: [propext]

@YulangClosure.OriginalCalleeDelayProvenance.prepared_view : ∀ {C Dict Rest Schema : Type}
  (r : YulangClosure.OriginalCalleeDelayProvenance.Raw C Dict Rest Schema) (site : YulangClosure.OriginalSource.Site)
  (label environment : Nat) (data : YulangClosure.OriginalCalleeDelayProvenance.Metadata),
  have post :=
    YulangClosure.OriginalCalleeDelayProvenance.appendView
      (YulangClosure.OriginalCalleeDelayProvenance.allocate r site label environment) r.values.length data;
  (YulangClosure.OriginalCalleeDelayProvenance.project post).world.receiving.views.cell r.views.length =
      Option.some { value := r.values.length, data := data } ∧
    (YulangClosure.OriginalCalleeDelayProvenance.project post).world.receiving.views.size = r.views.length + 1 ∧
      (YulangClosure.OriginalCalleeDelayProvenance.project post).world.receiving.receipts =
          (YulangClosure.OriginalCalleeDelayProvenance.project r).world.receiving.receipts ∧
        (YulangClosure.OriginalCalleeDelayProvenance.project post).world.receiving.index =
          (YulangClosure.OriginalCalleeDelayProvenance.project r).world.receiving.index
'YulangClosure.OriginalCalleeDelayProvenance.prepared_view' depends on axioms: [propext, Classical.choice, Quot.sound]

@YulangClosure.OriginalCalleeDelayProvenance.prepared_preserves_views : ∀ {C Dict Rest Schema : Type}
  (r : YulangClosure.OriginalCalleeDelayProvenance.Raw C Dict Rest Schema) (site : YulangClosure.OriginalSource.Site)
  (label environment : Nat) (data : YulangClosure.OriginalCalleeDelayProvenance.Metadata) (handle : Nat),
  handle < r.views.length →
    (YulangClosure.OriginalCalleeDelayProvenance.project
                  (YulangClosure.OriginalCalleeDelayProvenance.appendView
                    (YulangClosure.OriginalCalleeDelayProvenance.allocate r site label environment) r.values.length
                    data)).world.receiving.views.cell
        handle =
      (YulangClosure.OriginalCalleeDelayProvenance.project r).world.receiving.views.cell handle
'YulangClosure.OriginalCalleeDelayProvenance.prepared_preserves_views' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

@YulangClosure.OriginalCalleeDelayProvenance.allocated_value_prefix : ∀ {C Dict E Rest Schema : Type}
  (ops : YulangClosure.OriginalValueEntryDemand.Operations Dict E)
  (r : YulangClosure.OriginalCalleeDelayProvenance.Raw C Dict Rest Schema) (site : YulangClosure.OriginalSource.Site)
  (label environment : Nat) (code : YulangClosure.OriginalCalleeDelayProvenance.Code)
  (data : YulangClosure.OriginalCalleeDelayProvenance.Metadata)
  (received : YulangClosure.SourceIdentityWorld.Received Nat)
  (provider : YulangClosure.OriginalCalleeDelayProvenance.RuntimeValue)
  (closure : YulangClosure.OriginalValueEntryDemand.Closure Schema),
  r.program label = Option.some code →
    YulangClosure.OriginalCalleeDelayProvenance.delayMetadata r
          (YulangClosure.OriginalCalleeDelayProvenance.directFormalRoot r label environment) =
        Option.some data →
      received.value < r.values.length →
        (YulangClosure.OriginalWorldReadout.vectorStore (List.map Option.some r.values)).cell received.value =
            Option.some provider →
          r.executables received.value =
              Option.some (YulangClosure.OriginalCalleeDelayProvenance.Executable.closure closure) →
            closure.source.formal.entry = YulangClosure.OriginalSource.Entry.value →
              r.skeleton.nextReceiver < ops.receiverLimit →
                ops.dictionaries = Bool.false ∨ received.dispatch = Option.none →
                  have prepared :=
                    YulangClosure.OriginalCalleeDelayProvenance.appendView
                      (YulangClosure.OriginalCalleeDelayProvenance.allocate r site label environment) r.values.length
                      data;
                  have start := YulangClosure.OriginalCalleeDelayProvenance.project prepared;
                  have post :=
                    have __src :=
                      YulangClosure.OriginalValueEntryDemand.setup
                        (YulangClosure.OriginalValueEntryDemand.allocate start site provider.source) closure
                        start.nextReceiver start.world.control.current closure.savedEnvironment;
                    { world := __src.world, dictionary := __src.dictionary, nextReceiver := __src.nextReceiver,
                      frames := __src.frames, executables := __src.executables,
                      state := YulangClosure.OriginalValueEntryDemand.ControlState.evaluate code.body environment };
                  YulangClosure.OriginalCalleeDelayProvenance.run ops r site label environment received =
                    ({ values := prepared.values, views := prepared.views, executables := prepared.executables,
                        program := prepared.program, skeleton := post },
                      Except.ok ())
'YulangClosure.OriginalCalleeDelayProvenance.allocated_value_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

@YulangClosure.OriginalCalleeDelayProvenance.allocated_demand_represents : ∀ {C Dict E Rest Schema : Type}
  (ops : YulangClosure.OriginalValueEntryDemand.Operations Dict E)
  (r : YulangClosure.OriginalCalleeDelayProvenance.Raw C Dict Rest Schema) (site : YulangClosure.OriginalSource.Site)
  (label environment : Nat) (code : YulangClosure.OriginalCalleeDelayProvenance.Code)
  (data : YulangClosure.OriginalCalleeDelayProvenance.Metadata)
  (received : YulangClosure.SourceIdentityWorld.Received Nat)
  (provider : YulangClosure.OriginalCalleeDelayProvenance.RuntimeValue)
  (closure : YulangClosure.OriginalValueEntryDemand.Closure Schema),
  r.program label = Option.some code →
    YulangClosure.OriginalCalleeDelayProvenance.delayMetadata r
          (YulangClosure.OriginalCalleeDelayProvenance.directFormalRoot r label environment) =
        Option.some data →
      received.value < r.values.length →
        (YulangClosure.OriginalWorldReadout.vectorStore (List.map Option.some r.values)).cell received.value =
            Option.some provider →
          r.executables received.value =
              Option.some (YulangClosure.OriginalCalleeDelayProvenance.Executable.closure closure) →
            closure.source.formal.entry = YulangClosure.OriginalSource.Entry.value →
              r.skeleton.nextReceiver < ops.receiverLimit →
                ops.dictionaries = Bool.false ∨ received.dispatch = Option.none →
                  have prepared :=
                    YulangClosure.OriginalCalleeDelayProvenance.appendView
                      (YulangClosure.OriginalCalleeDelayProvenance.allocate r site label environment) r.values.length
                      data;
                  have start := YulangClosure.OriginalCalleeDelayProvenance.project prepared;
                  have demand :=
                    have __src :=
                      YulangClosure.OriginalValueEntryDemand.setup
                        (YulangClosure.OriginalValueEntryDemand.allocate start site provider.source) closure
                        start.nextReceiver start.world.control.current closure.savedEnvironment;
                    { world := __src.world, dictionary := __src.dictionary, nextReceiver := __src.nextReceiver,
                      frames := __src.frames, executables := __src.executables,
                      state := YulangClosure.OriginalValueEntryDemand.ControlState.evaluate code.body environment };
                  YulangClosure.OriginalCalleeDelayProvenance.Represents
                      (YulangClosure.OriginalCalleeDelayProvenance.run ops r site label environment received).fst
                      demand ∧
                    demand.world.receiving = start.world.receiving ∧
                      demand.world.receiving.views.cell r.views.length =
                          Option.some { value := r.values.length, data := data } ∧
                        demand.world.receiving.receipts =
                            (YulangClosure.OriginalCalleeDelayProvenance.project r).world.receiving.receipts ∧
                          demand.world.receiving.index =
                            (YulangClosure.OriginalCalleeDelayProvenance.project r).world.receiving.index
'YulangClosure.OriginalCalleeDelayProvenance.allocated_demand_represents' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

@YulangClosure.OriginalCalleeDelayProvenance.dictionary_failure_order : ∀ {C Dict E Rest Schema : Type}
  (ops : YulangClosure.OriginalValueEntryDemand.Operations Dict E)
  (r : YulangClosure.OriginalCalleeDelayProvenance.Raw C Dict Rest Schema) (site : YulangClosure.OriginalSource.Site)
  (label environment : Nat) (data : YulangClosure.OriginalCalleeDelayProvenance.Metadata)
  (received : YulangClosure.SourceIdentityWorld.Received Nat)
  (provider : YulangClosure.OriginalCalleeDelayProvenance.RuntimeValue)
  (closure : YulangClosure.OriginalValueEntryDemand.Closure Schema)
  (node :
    YulangClosure.NativeClosureEnvironment.Node YulangClosure.OriginalSource.Name
      (YulangClosure.OriginalValueEntryDemand.Dispatch C))
  (changed : Dict) (error : E),
  YulangClosure.OriginalCalleeDelayProvenance.delayMetadata r
        (YulangClosure.OriginalCalleeDelayProvenance.directFormalRoot r label environment) =
      Option.some data →
    received.value < r.values.length →
      (YulangClosure.OriginalWorldReadout.vectorStore (List.map Option.some r.values)).cell received.value =
          Option.some provider →
        r.executables received.value =
            Option.some (YulangClosure.OriginalCalleeDelayProvenance.Executable.closure closure) →
          r.skeleton.nextReceiver < ops.receiverLimit →
            ops.dictionaries = Bool.true →
              received.dispatch ≠ Option.none →
                YulangClosure.NativeClosureEnvironment.nodeAt r.skeleton.world.environments closure.savedEnvironment =
                    Option.some node →
                  ops.compose node.dispatch.substitution received.dispatch r.skeleton.dictionary =
                      (changed, Except.error error) →
                    have prepared :=
                      YulangClosure.OriginalCalleeDelayProvenance.appendView
                        (YulangClosure.OriginalCalleeDelayProvenance.allocate r site label environment) r.values.length
                        data;
                    YulangClosure.OriginalCalleeDelayProvenance.run ops r site label environment received =
                      ({ values := prepared.values, views := prepared.views, executables := prepared.executables,
                          program := prepared.program,
                          skeleton :=
                            have __src :=
                              YulangClosure.OriginalValueEntryDemand.allocate
                                (YulangClosure.OriginalCalleeDelayProvenance.project prepared) site provider.source;
                            { world := __src.world, dictionary := changed, nextReceiver := __src.nextReceiver,
                              frames := __src.frames, executables := __src.executables, state := __src.state } },
                        Except.error (Sum.inr (YulangClosure.OriginalValueEntryDemand.Failure.dictionary error)))
'YulangClosure.OriginalCalleeDelayProvenance.dictionary_failure_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

@YulangClosure.OriginalCalleeDelayProvenance.inherited_failure_order : ∀ {C Dict E Rest Schema : Type}
  (ops : YulangClosure.OriginalValueEntryDemand.Operations Dict E)
  (r : YulangClosure.OriginalCalleeDelayProvenance.Raw C Dict Rest Schema) (site : YulangClosure.OriginalSource.Site)
  (label environment : Nat) (received : YulangClosure.SourceIdentityWorld.Received Nat),
  YulangClosure.OriginalCalleeDelayProvenance.delayMetadata r
        (YulangClosure.OriginalCalleeDelayProvenance.directFormalRoot r label environment) =
      Option.none →
    YulangClosure.OriginalCalleeDelayProvenance.run ops r site label environment received =
      (YulangClosure.OriginalCalleeDelayProvenance.allocate r site label environment,
        Except.error (Sum.inl YulangClosure.OriginalCalleeDelayProvenance.Boundary.inheritedViewIndex))
'YulangClosure.OriginalCalleeDelayProvenance.inherited_failure_order' depends on axioms: [propext]

@YulangClosure.OriginalCalleeDelayProvenance.source_receipt_record : ∀ {C Dict Rest Schema : Type}
  (r : YulangClosure.OriginalCalleeDelayProvenance.Raw C Dict Rest Schema)
  (entry :
    YulangClosure.OriginalRecursivePair.EntryData YulangClosure.OriginalSource.Name Nat
      YulangClosure.OriginalSource.Site),
  have before :=
    YulangClosure.OriginalRecursivePair.enterWorld (YulangClosure.OriginalCalleeDelayProvenance.project r).world
      entry.call entry.provider;
  (YulangClosure.OriginalRecursivePair.receiveWorld before entry).receiving.receipts.cell
      before.receiving.receipts.size =
    Option.some
      { owner := before.control.current, view := entry.carrier.view, site := entry.slot,
        formal := Option.some entry.formal }
'YulangClosure.OriginalCalleeDelayProvenance.source_receipt_record' depends on axioms: [propext]

@YulangClosure.OriginalCalleeDelayProvenance.preforce_receipts_unchanged : ∀ {C Dict Rest Schema : Type}
  (r : YulangClosure.OriginalCalleeDelayProvenance.Raw C Dict Rest Schema) (site : YulangClosure.OriginalSource.Site)
  (label environment : Nat) (data : YulangClosure.OriginalCalleeDelayProvenance.Metadata),
  have prepared :=
    YulangClosure.OriginalCalleeDelayProvenance.appendView
      (YulangClosure.OriginalCalleeDelayProvenance.allocate r site label environment) r.values.length data;
  (YulangClosure.OriginalCalleeDelayProvenance.project prepared).world.receiving.receipts =
      (YulangClosure.OriginalCalleeDelayProvenance.project r).world.receiving.receipts ∧
    (YulangClosure.OriginalCalleeDelayProvenance.project prepared).world.receiving.index =
      (YulangClosure.OriginalCalleeDelayProvenance.project r).world.receiving.index
'YulangClosure.OriginalCalleeDelayProvenance.preforce_receipts_unchanged' does not depend on any axioms

```
