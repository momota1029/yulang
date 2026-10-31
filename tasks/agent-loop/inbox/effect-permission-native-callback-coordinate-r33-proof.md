# R33 proof handoff — frozen revision 1

Assignment `/root/effect_permission_r31_lean`, R33 session. Exact lease: this
handoff and `notes/theory/lean/YulangClosure/NativeCallbackCoordinatesR33.lean`.
Single author; no descendants. Requested routing Sol/high; observed model/effort
metadata UNKNOWN. Independent review and primary adjudication pending.

Outcome: kernel-accepted conditional coordinate decoder and translation into
R32's covered finite keys. Native token minting/source ownership and native
cross-snapshot rejection remain OPEN. No native runtime, Grant, request emission,
History, original A/B or production authority follows.

## Inputs and governing source

Read R33 contract/manifest, frozen R32 Rust/source review, actual R32 definitions,
installed pinned List/Option lemmas, and the exact archived coordinate serializer.
Root AGENTS.md, goal-driven sprint rules and Lean proof skill/source/execution
references were read in this leaf session and remain governing. Original claim:
source-preservation §§1,3,5 with birth-level correction §§2–6; effect policy
§§1.1,1.2,3,4. Every original supported source program/history/retained occurrence,
original scopes, complete Call/effects, correlated evidence and one shared
strategy remain quantified by that parent. No semantic authority is assigned to
research drafts; no source-language reduction or stronger parent assumption.

- `tasks/agent-loop/sprints/effect-permission-native-callback-coordinate-20261031-r33.md`: `77ea1171f71415e889d7391bfac042d3e44f6bd5b1bc1b5e094a5186f0c3aaca`.
- `tasks/agent-loop/sprints/effect-permission-native-callback-coordinate-20261031-r33-inputs-r1.json`: `85d4b904897d911a9b6bc379d1369747a79698756a148573867e7eb72c2a8cc0`.
- `tasks/agent-loop/inbox/effect-permission-native-callback-coordinate-r33-rust.md`: `2225b717a0a9dc2607cd9380b9273ba516d3354cd683091cdb5811e88d96a391`.
- `tasks/agent-loop/artifacts/native-callback-coordinate-r33.patch`: `1d31e7888974eceed85ef65439e48d98bda531a5153477ba77ac184ef22e83d1`.
- `notes/theory/2026-10-13-intrusion-source-preservation-proof.md`: `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271`.
- `notes/design/2026-10-24-birth-level-scc-intrusion.md`: `ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae`.
- `notes/design/2026-10-10-annotation-effect-hygiene-integration.md`: `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18`.

Exact entire R32 dependency is the unchanged 48,478-byte prefix, SHA
`bf2908ae347814c71ddc32ffae0f64a62103b855d96655a47aa1b9db0dc9690c`.
It retains exact R31 prefix SHA
`a0a8b53e1f73ed44e92ee01b3e87531d310775af0804999d30d6fbb0a68e378d`
and exact R26 prefix SHA
`0621f43739c12ce1e7919a50de129414a4748d8359bf46740babd69f4854011e`.
No dependency source was changed. R32 independent review is reused only for its
finite mathematical scope; no new independent review is claimed here.

R30 archive SHA
`5c3c991dec9e54ad3e2665a1c722a0abf2d80a9efe719664606824558351a790`;
`machine.rs` member was freshly streamed and verified at SHA
`b74c8345e6e07155f482440bb9299b5fc12763accb666ca8f543156dd4a87425`.
No extraction. `effect_identity_json`/`operation_identity_json` at archived
machine.rs:4096–4114 find typed family and operation positions within
`machine.program._hir.source_effect_declarations()`. These nested HIR indices
are distinct from R32's local table indices. Serializer rows at :4125–4127
map every retained family. Debug renderings do not establish identity.
The frozen Rust handoff establishes the token seam: neither pinned runtime
member serializes a snapshot token, and the RuntimeProgram constructor/token
owner is absent from this archive. No native source token owner was invented.

## Definitions and represented cases

New namespace: `YulangClosure.NativeCallbackCoordinatesR33` (N below).
`HirEffect` stores its complete structural family ID and ordered list of
structural operation IDs. `HirSnapshot` stores an abstract token, ordered effects
and the complete structural source permission row. `FamilyCoordinate` has a
token and effect index; `OperationCoordinate` adds the operation index within
that effect. Natural indices represent serialized input, including malformed
input; successful lookup theorems derive finite bounds. No unchecked Fin cast,
assumed raw-index/local-index equality, spelling, Debug or source-span identity.

`decodeFamilyCoordinate` checks the token and list lookup. The operation decoder
checks the token, both nested lookups and the structural operation-family join.
It returns the original stored SourceOperationId, without reconstructing it from
a name or reducing it to one coordinate. Missing/out-of-range entries, foreign
tokens and inconsistent family IDs reject with none.

`decodeFamilyRow` traverses every coordinate in order, rejecting the whole row
on any failing member. `translatePermissionRow` checks the decoded vector equals
the complete snapshot row, preserving order and duplicates. Empty, extra,
omitted, reordered or repeated coordinates are accepted only when that exact
resolved row equals the source snapshot row. There is no filtering/defaulting.
`translateCoordinates` decodes request, consumer, selected-operation and full
row against that one supplied snapshot. The selected arm's SourceNodeKey is a
separate native-provenance obligation, not an operation coordinate.

## Theorem types and full axiom coverage

Exact printed types and complete per-theorem #print axioms follow below.
Final successful run checked all definitions plus 59 theorem declarations:
22 R26 + 8 R31 + 11 R32 + 18 R33.

| New N theorem | Premises/conclusion summary | Complete axioms |
| --- | --- | --- |
| `family_wrong_token` | Token inequality implies family decoder returns none | propext |
| `operation_wrong_token` | Token inequality implies operation decoder returns none | propext |
| `family_out_of_range` | Effect index at least effect-list length implies none | propext |
| `operation_effect_out_of_range` | Outer effect index out of range implies none | propext |
| `operation_out_of_range` | Selected effect lookup plus inner index out of range implies none | propext |
| `operation_wrong_family` | Effect/operation lookups plus unequal structural family implies none | propext |
| `family_decode_exact` | Successful decode implies matching token and exact selected effect identity | propext |
| `family_decode_bounded` | Successful decode supplies finite outer bound and exact indexed structural family | propext |
| `operation_decode_exact` | Successful decode implies matching token, exact nested lookups and family identity | propext |
| `operation_decode_bounded` | Successful decode supplies both finite bounds, exact indexed operation and family join | propext |
| `operation_family_decode` | Successful operation decoding entails its family coordinate decodes to the same structural family | propext |
| `row_decode_length` | Successful row decoding retains coordinate vector length | propext, Quot.sound |
| `row_bad_member_rejected` | A member coordinate decoding to none rejects the whole row | propext, Quot.sound |
| `permission_row_exact` | Successful row translation returns exactly the complete source row, the successful raw row decode and equal length | propext, Quot.sound |
| `incomplete_row_rejected` | Successful raw row decode differing from source row rejects translation | propext |
| `bad_row_rejected` | Failed raw row decode rejects translation | propext |
| `translation_exact` | Successful request/consumer/arm/row translation supplies all four individual successful decodes | propext, Quot.sound |
| `translation_to_r32` | Successful translation derives snapshot-owned identities, exact row/length, all three token joins, constructed R32 coverage and operation/family round trips | propext, Quot.sound |

All R33 statements quantify arbitrary Token/Module/Parse/Green types with the
required decidable equalities; the complete printed premises make the narrower
requirements of individual lemmas explicit. New axioms: thirteen use only
propext, five use propext and Quot.sound; no project axiom, sorryAx, native
assumption or Classical.choice in the final dependency reports.

`translation_to_r32` first inverts the successful actual coordinate computation,
then exposes the exact snapshot effect/operation memberships. It constructs
R32 coveringTable from those decoded IDs and the preserved full row, derives
all operation/family coverage, and consumes those facts through R32's
referenced_operation_round_trip and permission_row_round_trip. It returns
request/consumer/selected-operation decoder equations for their R32 keys and
family decoder/equivalence obligations for every source-row member. No coverage
is supplied by a caller, and no raw HIR index is identified with a local key.

## Parent application and precise remaining seam

This discharges only the conditional nested-coordinate translation step into
R32's finite table. It supplies R32 structural IDs and row coverage when the
modeled decoder succeeds. Applying R32 covered_checked_catch still separately
requires authentic UseReady/annotation/Name/Apply joins, actual execution/origin,
typed request/consumer/arm equality, event/payload joins, active invocation and
selected dynamic Catch installation/arm provenance. These are not conclusions
of coordinate decoding or assumed true by this handoff.

First remaining owner: native immutable HIR/RuntimeProgram binding constructor.
It must mint/retain a faithful opaque snapshot token and transport it into every
serialized coordinate, with equality reflecting that owner. The archive has no
such token and omits that constructor; the Rust output is an owner-level blocker
proposal, not an applicable source hunk or implementation. Abstract Token
inequality is checked by the proposed Lean decoder, but native foreign-snapshot
rejection is OPEN. Equal tokens on distinct native owners are not ruled out by
these conditional mathematics. No claim about the archived serializer's
cross-snapshot behavior follows.

Native extraction must then authenticate the snapshot's structural identity
atoms and complete AST/annotation-owned row, numeric conversions, operation and
selected-arm SourceNodeKey provenance, observations/Grant guards, invocation
lifetime, request mint/emission and Step/History. General symbolic rows/type
arguments, RootComp, continuation replay, arm-body results 1/23, original scoped
strategy/publication/use, whole-language hygiene/safety/principality/progress/
termination and production remain OPEN. These are retained parent obligations,
not omitted accepted source cases or new original-language restrictions.

## Execution and resource receipt

Command for all three audits:
`bwrap --ro-bind / / --dev /dev --proc /proc /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean --stdin -j1 -M1024`.
Stdin: entire standalone source plus #print and #print axioms for every theorem;
pp.universes true, pp.proofs false. The final audit exited 0, no diagnostics,
empty stderr, all 59 printed theorem types/complete axiom lists captured.
Measured subprocess seconds: attempt 1 = 2.902566182; attempt 2 = 2.974208806;
final attempt 3 = 3.058029423. These are included in the construction interval.

Material failed attempts remain below. Attempt 1 exposed dependent case
rewrites: selected lookups in goals had become reflexive while original lookup
proofs were supplied; the do-notation inversion simplifier also did not match
its Option.bind lemma and dependent elimination failed. Repairs used the actual
case forms and explicit lookup facts. Attempt 2 exposed one inner operation
lookup that still required operationAt rather than rfl; that was repaired.
Failed runs' Lean recovery sorryAx reports are invalid completion evidence and
are preserved as failures. No source sorry/admit was written. The fresh final
audit has none of those dependencies.

Version command: same bwrap mounts and pinned executable with --version; exit 0:
`Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)`.
Skill checker cannot run under this packet's no-Lake/no-build/no-generated-file
boundary; manual approved stdin audit used the pin directly. Read-only bwrap
prevented ordinary filesystem writes; this is not a syscall-capture claim.
Stdout/stderr stayed in memory until written into this exact leased handoff.
No Lake/Cargo/build/target/cache/project copy/installation, external directory,
separate log/scratch/extracted file, source/runtime/config/root import,
scheduling record or Git mutation. Source scan of the complete module found no
sorry/admit/project axiom/native_decide/kernel-check bypass tokens.

Fresh R33 Lean cap 1600 s, no prior allowance transfer. Measured construction,
repair, audit and handoff interval: Unix 1793379645.122113 through 1793380080.7141964 =
435.592083 seconds. Earlier startup reads are unmeasured; no aggregate active-time
or remaining-cap claim is fabricated. This is not R32 time reuse.

Artifact SHA `9d138f84ede8c38161195fad4a324d9f164a72632dcfa575b5a5197d2685a436`; handoff SHA returned after freezing without
self-reference. Writer state STOPPED; writes stopped after revision 1; no
descendants, unreported outputs or generated caches. Independent review pending.

## Preserved complete audit output

### Construction interval marker

Measured construction interval starts Unix 1793379645.122113; startup reads before that unmeasured. Fresh R33 Lean cap 1600 seconds; no R32 transfer.

## Audit attempt 1

Command: `bwrap --ro-bind / / --dev /dev --proc /proc /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean --stdin -j1 -M1024`; stdin full module plus per-theorem types and axioms. Exit 1; measured subprocess seconds 2.9025661820014648.

```text
<stdin>:1066:26: error: Application type mismatch: The argument
  lookup
has type
  s.effects[q.effectIndex]? = some effect
but is expected to have type
  some effect = some effect
in the application
  And.intro lookup
<stdin>:1097:30: error: Application type mismatch: The argument
  effectAt
has type
  s.effects[q.family.effectIndex]? = some effect
but is expected to have type
  some effect = some effect
in the application
  And.intro effectAt
<stdin>:1183:23: error: Application type mismatch: The argument
  decoded
has type
  decodeFamilyRow s coordinates = some row
but is expected to have type
  some row = some row
in the application
  And.intro decoded
<stdin>:1224:9: error: Tactic `cases` failed with a nested error:
Dependent elimination failed: Failed to solve equation
  some out =
    match decodeOperationCoordinate s request, fun requestId => do
      let consumerId ← decodeOperationCoordinate s consumer
      let armId ← decodeOperationCoordinate s arm
      let families ← translatePermissionRow s row
      some { request := requestId, consumer := consumerId, arm := armId, families := families } with
    | none, x => none
    | some a, f => f a
at case `Eq.refl`
<stdin>:1223:35: warning: This simp argument is unused:
  Option.bind_eq_some_iff

Hint: Omit it from the simp argument list.
  [apply] simp only [translateCoordinates, Option.pure_def, Option.some.injEq] at success

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
<stdin>:1223:77: warning: This simp argument is unused:
  Option.some.injEq

Hint: Omit it from the simp argument list.
  [apply] simp only [translateCoordinates, Option.bind_eq_some_iff, Option.pure_def] at success

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
theorem YulangClosure.CallbackHygieneCorrespondence.checked_use_inversion : ∀
  {e : YulangClosure.CallbackHygieneCorrespondence.Entry} {n : YulangClosure.CallbackHygieneCorrespondence.NameRead}
  {u out : YulangClosure.CallbackHygieneCorrespondence.CallbackUse},
  Eq.{1} (YulangClosure.CallbackHygieneCorrespondence.checkedUse e n u) (some.{0} out) →
    Eq.{1} out u ∧ YulangClosure.CallbackHygieneCorrespondence.UseReady e n u :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.checked_use_inversion' does not depend on any axioms
theorem YulangClosure.CallbackHygieneCorrespondence.checked_catch_inversion : ∀
  {s : YulangClosure.CallbackHygieneCorrespondence.State} {r : YulangClosure.CallbackHygieneCorrespondence.Request}
  {c : YulangClosure.CallbackHygieneCorrespondence.Consumer}
  {p : YulangClosure.CallbackHygieneCorrespondence.Permission}
  {x : YulangClosure.CallbackHygieneCorrespondence.Selection},
  Eq.{1} (YulangClosure.CallbackHygieneCorrespondence.checkedCatch s r c p) (some.{0} x) →
    Eq.{1} x { request := r, consumer := c, permission := p } ∧
      YulangClosure.CallbackHygieneCorrespondence.CatchReady s r c p :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.checked_catch_inversion' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.CallbackHygieneCorrespondence.checked_catch_installed_arm : ∀
  {s : YulangClosure.CallbackHygieneCorrespondence.State} {r : YulangClosure.CallbackHygieneCorrespondence.Request}
  {c : YulangClosure.CallbackHygieneCorrespondence.Consumer}
  {p : YulangClosure.CallbackHygieneCorrespondence.Permission}
  {x : YulangClosure.CallbackHygieneCorrespondence.Selection},
  Eq.{1} (YulangClosure.CallbackHygieneCorrespondence.checkedCatch s r c p) (some.{0} x) →
    Exists.{1} fun h =>
      Membership.mem.{0, 0} s.installed h ∧
        Eq.{1} c.handler h.handle ∧
          Eq.{1} c.catchSite h.site ∧
            Eq.{1} c.owner h.owner ∧
              Exists.{1} fun a =>
                Membership.mem.{0, 0} h.arms a ∧
                  Eq.{1} c.arm a.handle ∧ Eq.{1} c.armSite a.site ∧ Eq.{1} c.operation a.operation :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.checked_catch_installed_arm' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.CallbackHygieneCorrespondence.checked_catch_port : ∀
  {s : YulangClosure.CallbackHygieneCorrespondence.State} {r : YulangClosure.CallbackHygieneCorrespondence.Request}
  {c : YulangClosure.CallbackHygieneCorrespondence.Consumer}
  {p : YulangClosure.CallbackHygieneCorrespondence.Permission}
  {x : YulangClosure.CallbackHygieneCorrespondence.Selection},
  Eq.{1} (YulangClosure.CallbackHygieneCorrespondence.checkedCatch s r c p) (some.{0} x) →
    YulangClosure.CallbackHygieneCorrespondence.PortReady s r p :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.checked_catch_port' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.CallbackHygieneCorrespondence.permission_preserves_actual : ∀
  (s : YulangClosure.CallbackHygieneCorrespondence.State) (a : YulangClosure.CallbackHygieneCorrespondence.Annotation),
  Eq.{1}
      { annotations := List.cons.{0} a s.annotations, permissions := s.permissions, installed := s.installed,
          active := s.active, invocations := s.invocations, entries := s.entries, names := s.names, uses := s.uses,
          executions := s.executions, executing := s.executing, emitted := s.emitted, pending := s.pending,
          selections := s.selections, initializing := s.initializing, lifetime := s.lifetime, nextEvent := s.nextEvent,
          nextInvocation := s.nextInvocation }.emitted
      s.emitted ∧
    Eq.{1}
      { annotations := List.cons.{0} a s.annotations, permissions := s.permissions, installed := s.installed,
          active := s.active, invocations := s.invocations, entries := s.entries, names := s.names, uses := s.uses,
          executions := s.executions, executing := s.executing, emitted := s.emitted, pending := s.pending,
          selections := s.selections, initializing := s.initializing, lifetime := s.lifetime, nextEvent := s.nextEvent,
          nextInvocation := s.nextInvocation }.pending
      s.pending :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.permission_preserves_actual' does not depend on any axioms
theorem YulangClosure.CallbackHygieneCorrespondence.emit_conserved : ∀
  {s : YulangClosure.CallbackHygieneCorrespondence.State},
  YulangClosure.CallbackHygieneCorrespondence.Conserved s →
    ∀ (r : YulangClosure.CallbackHygieneCorrespondence.Request),
      YulangClosure.CallbackHygieneCorrespondence.Conserved (YulangClosure.CallbackHygieneCorrespondence.emit s r) :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.emit_conserved' depends on axioms: [propext]
theorem YulangClosure.CallbackHygieneCorrespondence.commit_conserved : ∀
  {s : YulangClosure.CallbackHygieneCorrespondence.State},
  YulangClosure.CallbackHygieneCorrespondence.Conserved s →
    ∀ {r : YulangClosure.CallbackHygieneCorrespondence.Request}
      {c : YulangClosure.CallbackHygieneCorrespondence.Consumer}
      {p : YulangClosure.CallbackHygieneCorrespondence.Permission}
      {x : YulangClosure.CallbackHygieneCorrespondence.Selection},
      Eq.{1} (YulangClosure.CallbackHygieneCorrespondence.checkedCatch s r c p) (some.{0} x) →
        YulangClosure.CallbackHygieneCorrespondence.Conserved
          (YulangClosure.CallbackHygieneCorrespondence.commit s x) :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.commit_conserved' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.CallbackHygieneCorrespondence.step_conserved : ∀
  {before after : YulangClosure.CallbackHygieneCorrespondence.State},
  YulangClosure.CallbackHygieneCorrespondence.Step before after →
    YulangClosure.CallbackHygieneCorrespondence.Conserved before →
      YulangClosure.CallbackHygieneCorrespondence.Conserved after :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.step_conserved' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.CallbackHygieneCorrespondence.history_conserved : ∀
  {initial final : YulangClosure.CallbackHygieneCorrespondence.State},
  YulangClosure.CallbackHygieneCorrespondence.History initial final →
    YulangClosure.CallbackHygieneCorrespondence.Conserved initial →
      YulangClosure.CallbackHygieneCorrespondence.Conserved final :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.history_conserved' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.CallbackHygieneCorrespondence.empty_conserved : YulangClosure.CallbackHygieneCorrespondence.Conserved
  { } :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.empty_conserved' does not depend on any axioms
theorem YulangClosure.CallbackHygieneCorrespondence.emit_events_before : ∀
  {s : YulangClosure.CallbackHygieneCorrespondence.State},
  YulangClosure.CallbackHygieneCorrespondence.EventsBefore s →
    ∀ (r : YulangClosure.CallbackHygieneCorrespondence.Request),
      YulangClosure.CallbackHygieneCorrespondence.EventsBefore (YulangClosure.CallbackHygieneCorrespondence.emit s r) :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.emit_events_before' depends on axioms: [propext]
theorem YulangClosure.CallbackHygieneCorrespondence.step_events_before : ∀
  {before after : YulangClosure.CallbackHygieneCorrespondence.State},
  YulangClosure.CallbackHygieneCorrespondence.Step before after →
    YulangClosure.CallbackHygieneCorrespondence.EventsBefore before →
      YulangClosure.CallbackHygieneCorrespondence.EventsBefore after :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.step_events_before' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.CallbackHygieneCorrespondence.generated_events_before : ∀
  {final : YulangClosure.CallbackHygieneCorrespondence.State},
  YulangClosure.CallbackHygieneCorrespondence.History { } final →
    YulangClosure.CallbackHygieneCorrespondence.EventsBefore final :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.generated_events_before' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.CallbackHygieneCorrespondence.generated_selection_actual : ∀
  {final : YulangClosure.CallbackHygieneCorrespondence.State},
  YulangClosure.CallbackHygieneCorrespondence.History { } final →
    ∀ {x : YulangClosure.CallbackHygieneCorrespondence.Selection},
      Membership.mem.{0, 0} final.selections x →
        Membership.mem.{0, 0} final.emitted x.request ∧
          Eq.{1} x.consumer.operation x.request.operation ∧
            Eq.{1} x.consumer.event x.request.event ∧
              Eq.{1} x.consumer.payload x.request.payload ∧
                Eq.{1} x.consumer.owner x.permission.owner ∧
                  Membership.mem.{0, 0} x.permission.families x.request.operation.family :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.generated_selection_actual' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.CallbackHygieneCorrespondence.empty_inflow_rejected : ∀
  (s : YulangClosure.CallbackHygieneCorrespondence.State) (r : YulangClosure.CallbackHygieneCorrespondence.Request)
  (c : YulangClosure.CallbackHygieneCorrespondence.Consumer)
  (p : YulangClosure.CallbackHygieneCorrespondence.Permission),
  Eq.{1} s.pending List.nil.{0} → Eq.{1} (YulangClosure.CallbackHygieneCorrespondence.checkedCatch s r c p) none.{0} :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.empty_inflow_rejected' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.CallbackHygieneCorrespondence.companion_event_fresh : ∀
  {s : YulangClosure.CallbackHygieneCorrespondence.State},
  YulangClosure.CallbackHygieneCorrespondence.History { } s →
    ∀ {inner : YulangClosure.CallbackHygieneCorrespondence.Selection},
      Membership.mem.{0, 0} s.selections inner →
        ∀ (r : YulangClosure.CallbackHygieneCorrespondence.Request),
          Ne.{1} (YulangClosure.CallbackHygieneCorrespondence.minted s r).event inner.request.event :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.companion_event_fresh' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.CallbackHygieneCorrespondence.commit_preserves_other_event : ∀
  (s : YulangClosure.CallbackHygieneCorrespondence.State) (x : YulangClosure.CallbackHygieneCorrespondence.Selection)
  (write : YulangClosure.CallbackHygieneCorrespondence.Request),
  Membership.mem.{0, 0} s.pending write →
    Ne.{1} write.event x.request.event →
      Membership.mem.{0, 0} (YulangClosure.CallbackHygieneCorrespondence.commit s x).pending write :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.commit_preserves_other_event' depends on axioms: [propext]
theorem YulangClosure.CallbackHygieneCorrespondence.commit_removes_selected_event : ∀
  (s : YulangClosure.CallbackHygieneCorrespondence.State) (x : YulangClosure.CallbackHygieneCorrespondence.Selection)
  (r : YulangClosure.CallbackHygieneCorrespondence.Request),
  Membership.mem.{0, 0} (YulangClosure.CallbackHygieneCorrespondence.commit s x).pending r →
    Ne.{1} r.event x.request.event :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.commit_removes_selected_event' depends on axioms: [propext]
theorem YulangClosure.CallbackHygieneCorrespondence.companion_emit_actual : ∀
  (s : YulangClosure.CallbackHygieneCorrespondence.State) (r : YulangClosure.CallbackHygieneCorrespondence.Request),
  Membership.mem.{0, 0} (YulangClosure.CallbackHygieneCorrespondence.emit s r).emitted
      (YulangClosure.CallbackHygieneCorrespondence.minted s r) ∧
    Membership.mem.{0, 0} (YulangClosure.CallbackHygieneCorrespondence.emit s r).pending
        (YulangClosure.CallbackHygieneCorrespondence.minted s r) ∧
      Eq.{1} (YulangClosure.CallbackHygieneCorrespondence.minted s r).operation r.operation ∧
        Eq.{1} (YulangClosure.CallbackHygieneCorrespondence.minted s r).payload r.payload ∧
          Eq.{1} (YulangClosure.CallbackHygieneCorrespondence.minted s r).lineage r.lineage :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.companion_emit_actual' does not depend on any axioms
theorem YulangClosure.CallbackHygieneCorrespondence.shallow_discard_preserves_contributions : ∀
  (s : YulangClosure.CallbackHygieneCorrespondence.State)
  (cells :
    List.{0} (YulangClosure.CallbackHygieneCorrespondence.Id YulangClosure.CallbackHygieneCorrespondence.Kind.cell)),
  Eq.{1}
      { annotations := s.annotations, permissions := s.permissions, installed := s.installed, active := s.active,
          invocations := s.invocations, entries := s.entries, names := s.names, uses := s.uses,
          executions := s.executions, executing := s.executing, emitted := s.emitted, pending := s.pending,
          selections := s.selections,
          initializing := List.filter.{0} (fun cell => decide ¬Membership.mem.{0, 0} cells cell) s.initializing,
          lifetime :=
            List.cons.{0} (YulangClosure.CallbackHygieneCorrespondence.Lifetime.shallowDiscard cells) s.lifetime,
          nextEvent := s.nextEvent, nextInvocation := s.nextInvocation }.pending
      s.pending ∧
    Eq.{1}
        { annotations := s.annotations, permissions := s.permissions, installed := s.installed, active := s.active,
            invocations := s.invocations, entries := s.entries, names := s.names, uses := s.uses,
            executions := s.executions, executing := s.executing, emitted := s.emitted, pending := s.pending,
            selections := s.selections,
            initializing := List.filter.{0} (fun cell => decide ¬Membership.mem.{0, 0} cells cell) s.initializing,
            lifetime :=
              List.cons.{0} (YulangClosure.CallbackHygieneCorrespondence.Lifetime.shallowDiscard cells) s.lifetime,
            nextEvent := s.nextEvent, nextInvocation := s.nextInvocation }.emitted
        s.emitted ∧
      Eq.{1}
        { annotations := s.annotations, permissions := s.permissions, installed := s.installed, active := s.active,
            invocations := s.invocations, entries := s.entries, names := s.names, uses := s.uses,
            executions := s.executions, executing := s.executing, emitted := s.emitted, pending := s.pending,
            selections := s.selections,
            initializing := List.filter.{0} (fun cell => decide ¬Membership.mem.{0, 0} cells cell) s.initializing,
            lifetime :=
              List.cons.{0} (YulangClosure.CallbackHygieneCorrespondence.Lifetime.shallowDiscard cells) s.lifetime,
            nextEvent := s.nextEvent, nextInvocation := s.nextInvocation }.active
        s.active :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.shallow_discard_preserves_contributions' depends on axioms: [propext]
theorem YulangClosure.CallbackHygieneCorrespondence.normal_return_deactivates : ∀
  (s : YulangClosure.CallbackHygieneCorrespondence.State)
  (owner : YulangClosure.CallbackHygieneCorrespondence.Id YulangClosure.CallbackHygieneCorrespondence.Kind.invocation),
  ¬Membership.mem.{0, 0}
      { annotations := s.annotations, permissions := s.permissions, installed := s.installed,
          active := List.filter.{0} (fun current => decide (Ne.{1} current owner)) s.active,
          invocations := s.invocations, entries := s.entries, names := s.names, uses := s.uses,
          executions := s.executions, executing := s.executing, emitted := s.emitted, pending := s.pending,
          selections := s.selections, initializing := s.initializing,
          lifetime :=
            List.cons.{0} (YulangClosure.CallbackHygieneCorrespondence.Lifetime.normalReturn owner) s.lifetime,
          nextEvent := s.nextEvent, nextInvocation := s.nextInvocation }.active
      owner :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.normal_return_deactivates' depends on axioms: [propext]
theorem YulangClosure.CallbackHygieneCorrespondence.lifetime_branches_distinct : ∀
  (owner : YulangClosure.CallbackHygieneCorrespondence.Id YulangClosure.CallbackHygieneCorrespondence.Kind.invocation)
  (cells :
    List.{0} (YulangClosure.CallbackHygieneCorrespondence.Id YulangClosure.CallbackHygieneCorrespondence.Kind.cell)),
  Ne.{1} (YulangClosure.CallbackHygieneCorrespondence.Lifetime.normalReturn owner)
    (YulangClosure.CallbackHygieneCorrespondence.Lifetime.shallowDiscard cells) :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.lifetime_branches_distinct' does not depend on any axioms
theorem YulangClosure.NativeCallbackGrantBridgeR31.finite_index_round_trip : ∀ {α : Type} [inst : DecidableEq.{1} α]
  (table : List.{0} α) (a : α),
  Membership.mem.{0, 0} table a → Eq.{1} (getElem?.{0, 0, 0} table (List.idxOf.{0} a table)) (some.{0} a) :=
⋯
'YulangClosure.NativeCallbackGrantBridgeR31.finite_index_round_trip' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.NativeCallbackGrantBridgeR31.finite_index_injective : ∀ {α : Type} [inst : DecidableEq.{1} α]
  (table : List.{0} α) {a b : α},
  Membership.mem.{0, 0} table a →
    Membership.mem.{0, 0} table b → Eq.{1} (List.idxOf.{0} a table) (List.idxOf.{0} b table) → Eq.{1} a b :=
⋯
'YulangClosure.NativeCallbackGrantBridgeR31.finite_index_injective' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.NativeCallbackGrantBridgeR31.operation_round_trip : ∀ {Module Parse Green : Type}
  [inst : DecidableEq.{1} Module] [inst_1 : DecidableEq.{1} Parse] [inst_2 : DecidableEq.{1} Green]
  (table : YulangClosure.NativeCallbackGrantBridgeR31.IdentityTable Module Parse Green)
  (operation : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green),
  Membership.mem.{0, 0} table.operations operation →
    Membership.mem.{0, 0} table.families operation.family →
      Eq.{1}
        (YulangClosure.NativeCallbackGrantBridgeR31.decodeOperation table
          (YulangClosure.NativeCallbackGrantBridgeR31.operationKey table operation))
        (some.{0} operation) :=
⋯
'YulangClosure.NativeCallbackGrantBridgeR31.operation_round_trip' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.NativeCallbackGrantBridgeR31.operationKey_injective : ∀ {Module Parse Green : Type}
  [inst : DecidableEq.{1} Module] [inst_1 : DecidableEq.{1} Parse] [inst_2 : DecidableEq.{1} Green]
  (table : YulangClosure.NativeCallbackGrantBridgeR31.IdentityTable Module Parse Green)
  {a b : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green},
  Membership.mem.{0, 0} table.operations a →
    Membership.mem.{0, 0} table.operations b →
      Eq.{1} (YulangClosure.NativeCallbackGrantBridgeR31.operationKey table a)
          (YulangClosure.NativeCallbackGrantBridgeR31.operationKey table b) →
        Eq.{1} a b :=
⋯
'YulangClosure.NativeCallbackGrantBridgeR31.operationKey_injective' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.NativeCallbackGrantBridgeR31.encoded_family_member : ∀ {Module Parse Green : Type}
  [inst : DecidableEq.{1} Module] [inst_1 : DecidableEq.{1} Parse] [inst_2 : DecidableEq.{1} Green]
  (table : YulangClosure.NativeCallbackGrantBridgeR31.IdentityTable Module Parse Green)
  {family : YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green}
  {row : List.{0} (YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green)},
  Membership.mem.{0, 0} row family →
    Membership.mem.{0, 0} (List.map.{0, 0} (fun a => List.idxOf.{0} a table.families) row)
      (List.idxOf.{0} family table.families) :=
⋯
'YulangClosure.NativeCallbackGrantBridgeR31.encoded_family_member' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.NativeCallbackGrantBridgeR31.encoded_family_member_iff : ∀ {Module Parse Green : Type}
  [inst : DecidableEq.{1} Module] [inst_1 : DecidableEq.{1} Parse] [inst_2 : DecidableEq.{1} Green]
  (table : YulangClosure.NativeCallbackGrantBridgeR31.IdentityTable Module Parse Green)
  {family : YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green}
  {row : List.{0} (YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green)},
  (∀ (f : YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green),
      Membership.mem.{0, 0} row f → Membership.mem.{0, 0} table.families f) →
    Membership.mem.{0, 0} table.families family →
      (Membership.mem.{0, 0} (List.map.{0, 0} (fun a => List.idxOf.{0} a table.families) row)
          (List.idxOf.{0} family table.families) ↔
        Membership.mem.{0, 0} row family) :=
⋯
'YulangClosure.NativeCallbackGrantBridgeR31.encoded_family_member_iff' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.NativeCallbackGrantBridgeR31.callback_use_ready : ∀
  (e : YulangClosure.CallbackHygieneCorrespondence.Entry) (n : YulangClosure.CallbackHygieneCorrespondence.NameRead)
  (u : YulangClosure.CallbackHygieneCorrespondence.CallbackUse),
  Eq.{1} e.permission.port YulangClosure.CallbackHygieneCorrespondence.Port.callbackResult →
    Eq.{1} e.formalReceipt.owner e.permission.owner →
      Eq.{1} e.formalReceipt.view e.view →
        Eq.{1} e.formalReceipt.site e.permission.lambdaSite →
          Eq.{1} e.formalReceipt.formal (some.{0} e.permission.formal) →
            Eq.{1} n.entry e.handle →
              Eq.{1} n.formal e.permission.formal →
                Eq.{1} n.receipt.owner e.permission.owner →
                  Eq.{1} n.receipt.view e.view →
                    Eq.{1} n.receipt.site n.site →
                      Eq.{1} n.receipt.formal none.{0} →
                        Eq.{1} u.entry e.handle →
                          Eq.{1} u.owner e.permission.owner →
                            Eq.{1} u.sourceView e.view →
                              Eq.{1} u.formalReceipt e.formalReceipt.handle →
                                Eq.{1} u.nameReceipt n.receipt.handle →
                                  Eq.{1} u.callee n.site →
                                    Eq.{1} u.resultReceipt.owner u.owner →
                                      Eq.{1} u.resultReceipt.view u.resultView →
                                        Eq.{1} u.resultReceipt.site u.applySite →
                                          Eq.{1} u.resultReceipt.formal none.{0} →
                                            YulangClosure.CallbackHygieneCorrespondence.UseReady e n u :=
⋯
'YulangClosure.NativeCallbackGrantBridgeR31.callback_use_ready' does not depend on any axioms
theorem YulangClosure.NativeCallbackGrantBridgeR31.callback_checked_catch : ∀ {Module Parse Green : Type}
  [inst : DecidableEq.{1} Module] [inst_1 : DecidableEq.{1} Parse] [inst_2 : DecidableEq.{1} Green]
  (table : YulangClosure.NativeCallbackGrantBridgeR31.IdentityTable Module Parse Green)
  (r : YulangClosure.NativeCallbackGrantBridgeR31.NativeRequest Module Parse Green)
  (c : YulangClosure.NativeCallbackGrantBridgeR31.NativeConsumer Module Parse Green)
  (a : YulangClosure.NativeCallbackGrantBridgeR31.NativeArm Module Parse Green)
  (e : YulangClosure.CallbackHygieneCorrespondence.Entry) (n : YulangClosure.CallbackHygieneCorrespondence.NameRead)
  (u : YulangClosure.CallbackHygieneCorrespondence.CallbackUse)
  (x : YulangClosure.CallbackHygieneCorrespondence.Execution)
  (active :
    List.{0}
      (YulangClosure.CallbackHygieneCorrespondence.Id YulangClosure.CallbackHygieneCorrespondence.Kind.invocation))
  (installation : YulangClosure.CallbackHygieneCorrespondence.InstalledCatch)
  (families : List.{0} (YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green)),
  YulangClosure.CallbackHygieneCorrespondence.UseReady e n u →
    Eq.{1} x.useHandle u.handle →
      Eq.{1} x.view u.resultView →
        Eq.{1} x.receipt u.resultReceipt.handle →
          Eq.{1} r.coordinates.origin (YulangClosure.CallbackHygieneCorrespondence.Origin.callback x) →
            Eq.{1} e.permission.families (List.map.{0, 0} (fun a => List.idxOf.{0} a table.families) families) →
              Membership.mem.{0, 0} families r.operation.family →
                Membership.mem.{0, 0} active c.coordinates.owner →
                  Eq.{1} c.coordinates.owner e.permission.owner →
                    Eq.{1} c.operation r.operation →
                      Eq.{1} c.coordinates.event r.coordinates.event →
                        Eq.{1} c.coordinates.payload r.coordinates.payload →
                          Eq.{1} c.coordinates.handler installation.handle →
                            Eq.{1} c.coordinates.catchSite installation.site →
                              Eq.{1} c.coordinates.owner installation.owner →
                                Membership.mem.{0, 0} installation.arms
                                    (YulangClosure.NativeCallbackGrantBridgeR31.armKey table a) →
                                  Eq.{1} c.coordinates.arm a.coordinates.handle →
                                    Eq.{1} c.coordinates.armSite a.coordinates.site →
                                      Eq.{1} c.operation a.operation →
                                        Eq.{1}
                                          (YulangClosure.CallbackHygieneCorrespondence.checkedCatch
                                            (YulangClosure.NativeCallbackGrantBridgeR31.callbackSlice e n u x
                                              (YulangClosure.NativeCallbackGrantBridgeR31.requestKey table r)
                                              e.permission active installation)
                                            (YulangClosure.NativeCallbackGrantBridgeR31.requestKey table r)
                                            (YulangClosure.NativeCallbackGrantBridgeR31.consumerKey table c)
                                            e.permission)
                                          (some.{0}
                                            { request := YulangClosure.NativeCallbackGrantBridgeR31.requestKey table r,
                                              consumer :=
                                                YulangClosure.NativeCallbackGrantBridgeR31.consumerKey table c,
                                              permission := e.permission }) :=
⋯
'YulangClosure.NativeCallbackGrantBridgeR31.callback_checked_catch' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.NativeCallbackGrantBridgeR32.referenced_operations_covered : ∀ {Module Parse Green : Type}
  (r c a : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green)
  (families : List.{0} (YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green))
  (op : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green),
  Membership.mem.{0, 0} (List.cons.{0} r (List.cons.{0} c (List.cons.{0} a List.nil.{0}))) op →
    Membership.mem.{0, 0} (YulangClosure.NativeCallbackGrantBridgeR32.coveringTable r c a families).operations op :=
⋯
'YulangClosure.NativeCallbackGrantBridgeR32.referenced_operations_covered' does not depend on any axioms
theorem YulangClosure.NativeCallbackGrantBridgeR32.referenced_families_covered : ∀ {Module Parse Green : Type}
  (r c a : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green)
  (families : List.{0} (YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green))
  (op : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green),
  Membership.mem.{0, 0} (List.cons.{0} r (List.cons.{0} c (List.cons.{0} a List.nil.{0}))) op →
    Membership.mem.{0, 0} (YulangClosure.NativeCallbackGrantBridgeR32.coveringTable r c a families).families
      op.family :=
⋯
'YulangClosure.NativeCallbackGrantBridgeR32.referenced_families_covered' depends on axioms: [propext]
theorem YulangClosure.NativeCallbackGrantBridgeR32.permission_families_covered : ∀ {Module Parse Green : Type}
  (r c a : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green)
  (families : List.{0} (YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green))
  (f : YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green),
  Membership.mem.{0, 0} families f →
    Membership.mem.{0, 0} (YulangClosure.NativeCallbackGrantBridgeR32.coveringTable r c a families).families f :=
⋯
'YulangClosure.NativeCallbackGrantBridgeR32.permission_families_covered' does not depend on any axioms
theorem YulangClosure.NativeCallbackGrantBridgeR32.referenced_operation_round_trip : ∀ {Module Parse Green : Type}
  [inst : DecidableEq.{1} Module] [inst_1 : DecidableEq.{1} Parse] [inst_2 : DecidableEq.{1} Green]
  (r c a : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green)
  (families : List.{0} (YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green))
  {op : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green},
  Membership.mem.{0, 0} (List.cons.{0} r (List.cons.{0} c (List.cons.{0} a List.nil.{0}))) op →
    Eq.{1}
      (YulangClosure.NativeCallbackGrantBridgeR31.decodeOperation
        (YulangClosure.NativeCallbackGrantBridgeR32.coveringTable r c a families)
        (YulangClosure.NativeCallbackGrantBridgeR31.operationKey
          (YulangClosure.NativeCallbackGrantBridgeR32.coveringTable r c a families) op))
      (some.{0} op) :=
⋯
'YulangClosure.NativeCallbackGrantBridgeR32.referenced_operation_round_trip' depends on axioms: [propext,
 Quot.sound.{u}]
theorem YulangClosure.NativeCallbackGrantBridgeR32.covered_operation_keys_distinct : ∀ {Module Parse Green : Type}
  [inst : DecidableEq.{1} Module] [inst_1 : DecidableEq.{1} Parse] [inst_2 : DecidableEq.{1} Green]
  (r c a : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green)
  (families : List.{0} (YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green))
  {left right : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green},
  Membership.mem.{0, 0} (List.cons.{0} r (List.cons.{0} c (List.cons.{0} a List.nil.{0}))) left →
    Membership.mem.{0, 0} (List.cons.{0} r (List.cons.{0} c (List.cons.{0} a List.nil.{0}))) right →
      Ne.{1} left right →
        Ne.{1}
          (YulangClosure.NativeCallbackGrantBridgeR31.operationKey
            (YulangClosure.NativeCallbackGrantBridgeR32.coveringTable r c a families) left)
          (YulangClosure.NativeCallbackGrantBridgeR31.operationKey
            (YulangClosure.NativeCallbackGrantBridgeR32.coveringTable r c a families) right) :=
⋯
'YulangClosure.NativeCallbackGrantBridgeR32.covered_operation_keys_distinct' depends on axioms: [propext,
 Quot.sound.{u}]
theorem YulangClosure.NativeCallbackGrantBridgeR32.covered_family_membership_iff : ∀ {Module Parse Green : Type}
  [inst : DecidableEq.{1} Module] [inst_1 : DecidableEq.{1} Parse] [inst_2 : DecidableEq.{1} Green]
  (r c a : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green)
  (families : List.{0} (YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green))
  {op : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green},
  Membership.mem.{0, 0} (List.cons.{0} r (List.cons.{0} c (List.cons.{0} a List.nil.{0}))) op →
    (Membership.mem.{0, 0}
        (List.map.{0, 0}
          (fun a_1 =>
            List.idxOf.{0} a_1 (YulangClosure.NativeCallbackGrantBridgeR32.coveringTable r c a families).families)
          families)
        (List.idxOf.{0} op.family (YulangClosure.NativeCallbackGrantBridgeR32.coveringTable r c a families).families) ↔
      Membership.mem.{0, 0} families op.family) :=
⋯
'YulangClosure.NativeCallbackGrantBridgeR32.covered_family_membership_iff' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.NativeCallbackGrantBridgeR32.permission_row_round_trip : ∀ {Module Parse Green : Type}
  [inst : DecidableEq.{1} Module] [inst_1 : DecidableEq.{1} Parse] [inst_2 : DecidableEq.{1} Green]
  (r c a : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green)
  (families : List.{0} (YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green))
  {f : YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green},
  Membership.mem.{0, 0} families f →
    have table := YulangClosure.NativeCallbackGrantBridgeR32.coveringTable r c a families;
    Eq.{1} (getElem?.{0, 0, 0} table.families (List.idxOf.{0} f table.families)) (some.{0} f) ∧
      (Membership.mem.{0, 0} (List.map.{0, 0} (fun a => List.idxOf.{0} a table.families) families)
          (List.idxOf.{0} f table.families) ↔
        Membership.mem.{0, 0} families f) :=
⋯
'YulangClosure.NativeCallbackGrantBridgeR32.permission_row_round_trip' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.NativeCallbackGrantBridgeR32.entryWithRow_use_ready : ∀ {Module Parse Green : Type}
  [inst : DecidableEq.{1} Module] [inst_1 : DecidableEq.{1} Parse] [inst_2 : DecidableEq.{1} Green]
  (table : YulangClosure.NativeCallbackGrantBridgeR31.IdentityTable Module Parse Green)
  (families : List.{0} (YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green))
  (e : YulangClosure.CallbackHygieneCorrespondence.Entry) (n : YulangClosure.CallbackHygieneCorrespondence.NameRead)
  (u : YulangClosure.CallbackHygieneCorrespondence.CallbackUse),
  YulangClosure.CallbackHygieneCorrespondence.UseReady e n u →
    YulangClosure.CallbackHygieneCorrespondence.UseReady
      (YulangClosure.NativeCallbackGrantBridgeR32.entryWithRow table families e) n u :=
⋯
'YulangClosure.NativeCallbackGrantBridgeR32.entryWithRow_use_ready' does not depend on any axioms
theorem YulangClosure.NativeCallbackGrantBridgeR32.empty_table_collapse : ∀ {Module Parse Green : Type}
  [inst : DecidableEq.{1} Module] [inst_1 : DecidableEq.{1} Parse] [inst_2 : DecidableEq.{1} Green]
  (left right : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green),
  Eq.{1}
      (YulangClosure.NativeCallbackGrantBridgeR31.operationKey { families := List.nil.{0}, operations := List.nil.{0} }
        left)
      (YulangClosure.NativeCallbackGrantBridgeR31.operationKey { families := List.nil.{0}, operations := List.nil.{0} }
        right) ∧
    Eq.{1}
      (YulangClosure.NativeCallbackGrantBridgeR31.decodeOperation
        { families := List.nil.{0}, operations := List.nil.{0} }
        (YulangClosure.NativeCallbackGrantBridgeR31.operationKey
          { families := List.nil.{0}, operations := List.nil.{0} } left))
      none.{0} :=
⋯
'YulangClosure.NativeCallbackGrantBridgeR32.empty_table_collapse' depends on axioms: [propext]
theorem YulangClosure.NativeCallbackGrantBridgeR32.empty_table_not_covered : ∀ {Module Parse Green : Type}
  (op : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green),
  ¬Membership.mem.{0, 0} { families := List.nil.{0}, operations := List.nil.{0} }.operations op :=
⋯
'YulangClosure.NativeCallbackGrantBridgeR32.empty_table_not_covered' depends on axioms: [propext]
theorem YulangClosure.NativeCallbackGrantBridgeR32.covered_checked_catch : ∀ {Module Parse Green : Type}
  [inst : DecidableEq.{1} Module] [inst_1 : DecidableEq.{1} Parse] [inst_2 : DecidableEq.{1} Green]
  (r : YulangClosure.NativeCallbackGrantBridgeR31.NativeRequest Module Parse Green)
  (c : YulangClosure.NativeCallbackGrantBridgeR31.NativeConsumer Module Parse Green)
  (a : YulangClosure.NativeCallbackGrantBridgeR31.NativeArm Module Parse Green)
  (e : YulangClosure.CallbackHygieneCorrespondence.Entry) (n : YulangClosure.CallbackHygieneCorrespondence.NameRead)
  (u : YulangClosure.CallbackHygieneCorrespondence.CallbackUse)
  (x : YulangClosure.CallbackHygieneCorrespondence.Execution)
  (active :
    List.{0}
      (YulangClosure.CallbackHygieneCorrespondence.Id YulangClosure.CallbackHygieneCorrespondence.Kind.invocation))
  (installation : YulangClosure.CallbackHygieneCorrespondence.InstalledCatch)
  (families : List.{0} (YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green)),
  YulangClosure.CallbackHygieneCorrespondence.UseReady e n u →
    Eq.{1} x.useHandle u.handle →
      Eq.{1} x.view u.resultView →
        Eq.{1} x.receipt u.resultReceipt.handle →
          Eq.{1} r.coordinates.origin (YulangClosure.CallbackHygieneCorrespondence.Origin.callback x) →
            Membership.mem.{0, 0} families r.operation.family →
              Membership.mem.{0, 0} active c.coordinates.owner →
                Eq.{1} c.coordinates.owner e.permission.owner →
                  Eq.{1} c.operation r.operation →
                    Eq.{1} c.coordinates.event r.coordinates.event →
                      Eq.{1} c.coordinates.payload r.coordinates.payload →
                        Eq.{1} c.coordinates.handler installation.handle →
                          Eq.{1} c.coordinates.catchSite installation.site →
                            Eq.{1} c.coordinates.owner installation.owner →
                              Membership.mem.{0, 0} installation.arms
                                  (YulangClosure.NativeCallbackGrantBridgeR31.armKey
                                    (YulangClosure.NativeCallbackGrantBridgeR32.coveringTable r.operation c.operation
                                      a.operation families)
                                    a) →
                                Eq.{1} c.coordinates.arm a.coordinates.handle →
                                  Eq.{1} c.coordinates.armSite a.coordinates.site →
                                    Eq.{1} c.operation a.operation →
                                      have table :=
                                        YulangClosure.NativeCallbackGrantBridgeR32.coveringTable r.operation c.operation
                                          a.operation families;
                                      have projectedEntry :=
                                        YulangClosure.NativeCallbackGrantBridgeR32.entryWithRow table families e;
                                      Eq.{1}
                                          (YulangClosure.NativeCallbackGrantBridgeR31.decodeOperation table
                                            (YulangClosure.NativeCallbackGrantBridgeR31.requestKey table r).operation)
                                          (some.{0} r.operation) ∧
                                        Eq.{1}
                                            (YulangClosure.NativeCallbackGrantBridgeR31.decodeOperation table
                                              (YulangClosure.NativeCallbackGrantBridgeR31.consumerKey table
                                                  c).operation)
                                            (some.{0} c.operation) ∧
                                          Eq.{1}
                                              (YulangClosure.NativeCallbackGrantBridgeR31.decodeOperation table
                                                (YulangClosure.NativeCallbackGrantBridgeR31.armKey table a).operation)
                                              (some.{0} a.operation) ∧
                                            (Membership.mem.{0, 0} projectedEntry.permission.families
                                                  (YulangClosure.NativeCallbackGrantBridgeR31.requestKey table
                                                        r).operation.family ↔
                                                Membership.mem.{0, 0} families r.operation.family) ∧
                                              Eq.{1}
                                                (YulangClosure.CallbackHygieneCorrespondence.checkedCatch
                                                  (YulangClosure.NativeCallbackGrantBridgeR31.callbackSlice
                                                    projectedEntry n u x
                                                    (YulangClosure.NativeCallbackGrantBridgeR31.requestKey table r)
                                                    projectedEntry.permission active installation)
                                                  (YulangClosure.NativeCallbackGrantBridgeR31.requestKey table r)
                                                  (YulangClosure.NativeCallbackGrantBridgeR31.consumerKey table c)
                                                  projectedEntry.permission)
                                                (some.{0}
                                                  {
                                                    request :=
                                                      YulangClosure.NativeCallbackGrantBridgeR31.requestKey table r,
                                                    consumer :=
                                                      YulangClosure.NativeCallbackGrantBridgeR31.consumerKey table c,
                                                    permission := projectedEntry.permission }) :=
⋯
'YulangClosure.NativeCallbackGrantBridgeR32.covered_checked_catch' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.NativeCallbackCoordinatesR33.family_wrong_token : ∀ {Token Module Parse Green : Type}
  [inst : DecidableEq.{1} Token] (s : YulangClosure.NativeCallbackCoordinatesR33.HirSnapshot Token Module Parse Green)
  (q : YulangClosure.NativeCallbackCoordinatesR33.FamilyCoordinate Token),
  Ne.{1} q.snapshotToken s.token →
    Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.decodeFamilyCoordinate s q) none.{0} :=
⋯
'YulangClosure.NativeCallbackCoordinatesR33.family_wrong_token' depends on axioms: [propext]
theorem YulangClosure.NativeCallbackCoordinatesR33.operation_wrong_token : ∀ {Token Module Parse Green : Type}
  [inst : DecidableEq.{1} Token] [inst_1 : DecidableEq.{1} Module] [inst_2 : DecidableEq.{1} Parse]
  [inst_3 : DecidableEq.{1} Green] (s : YulangClosure.NativeCallbackCoordinatesR33.HirSnapshot Token Module Parse Green)
  (q : YulangClosure.NativeCallbackCoordinatesR33.OperationCoordinate Token),
  Ne.{1} q.family.snapshotToken s.token →
    Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.decodeOperationCoordinate s q) none.{0} :=
⋯
'YulangClosure.NativeCallbackCoordinatesR33.operation_wrong_token' depends on axioms: [propext]
theorem YulangClosure.NativeCallbackCoordinatesR33.family_out_of_range : ∀ {Token Module Parse Green : Type}
  [inst : DecidableEq.{1} Token] (s : YulangClosure.NativeCallbackCoordinatesR33.HirSnapshot Token Module Parse Green)
  (q : YulangClosure.NativeCallbackCoordinatesR33.FamilyCoordinate Token),
  LE.le.{0} (List.length.{0} s.effects) q.effectIndex →
    Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.decodeFamilyCoordinate s q) none.{0} :=
⋯
'YulangClosure.NativeCallbackCoordinatesR33.family_out_of_range' depends on axioms: [propext]
theorem YulangClosure.NativeCallbackCoordinatesR33.operation_effect_out_of_range : ∀ {Token Module Parse Green : Type}
  [inst : DecidableEq.{1} Token] [inst_1 : DecidableEq.{1} Module] [inst_2 : DecidableEq.{1} Parse]
  [inst_3 : DecidableEq.{1} Green] (s : YulangClosure.NativeCallbackCoordinatesR33.HirSnapshot Token Module Parse Green)
  (q : YulangClosure.NativeCallbackCoordinatesR33.OperationCoordinate Token),
  LE.le.{0} (List.length.{0} s.effects) q.family.effectIndex →
    Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.decodeOperationCoordinate s q) none.{0} :=
⋯
'YulangClosure.NativeCallbackCoordinatesR33.operation_effect_out_of_range' depends on axioms: [propext]
theorem YulangClosure.NativeCallbackCoordinatesR33.operation_out_of_range : ∀ {Token Module Parse Green : Type}
  [inst : DecidableEq.{1} Token] [inst_1 : DecidableEq.{1} Module] [inst_2 : DecidableEq.{1} Parse]
  [inst_3 : DecidableEq.{1} Green] (s : YulangClosure.NativeCallbackCoordinatesR33.HirSnapshot Token Module Parse Green)
  (q : YulangClosure.NativeCallbackCoordinatesR33.OperationCoordinate Token)
  (effect : YulangClosure.NativeCallbackCoordinatesR33.HirEffect Module Parse Green),
  Eq.{1} (getElem?.{0, 0, 0} s.effects q.family.effectIndex) (some.{0} effect) →
    LE.le.{0} (List.length.{0} effect.operations) q.operationIndex →
      Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.decodeOperationCoordinate s q) none.{0} :=
⋯
'YulangClosure.NativeCallbackCoordinatesR33.operation_out_of_range' depends on axioms: [propext]
theorem YulangClosure.NativeCallbackCoordinatesR33.operation_wrong_family : ∀ {Token Module Parse Green : Type}
  [inst : DecidableEq.{1} Token] [inst_1 : DecidableEq.{1} Module] [inst_2 : DecidableEq.{1} Parse]
  [inst_3 : DecidableEq.{1} Green] (s : YulangClosure.NativeCallbackCoordinatesR33.HirSnapshot Token Module Parse Green)
  (q : YulangClosure.NativeCallbackCoordinatesR33.OperationCoordinate Token)
  (effect : YulangClosure.NativeCallbackCoordinatesR33.HirEffect Module Parse Green)
  (operation : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green),
  Eq.{1} (getElem?.{0, 0, 0} s.effects q.family.effectIndex) (some.{0} effect) →
    Eq.{1} (getElem?.{0, 0, 0} effect.operations q.operationIndex) (some.{0} operation) →
      Ne.{1} operation.family effect.identity →
        Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.decodeOperationCoordinate s q) none.{0} :=
⋯
'YulangClosure.NativeCallbackCoordinatesR33.operation_wrong_family' depends on axioms: [propext]
theorem YulangClosure.NativeCallbackCoordinatesR33.family_decode_exact : ∀ {Token Module Parse Green : Type}
  [inst : DecidableEq.{1} Token] (s : YulangClosure.NativeCallbackCoordinatesR33.HirSnapshot Token Module Parse Green)
  (q : YulangClosure.NativeCallbackCoordinatesR33.FamilyCoordinate Token)
  {family : YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green},
  Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.decodeFamilyCoordinate s q) (some.{0} family) →
    Eq.{1} q.snapshotToken s.token ∧
      Exists.{1} fun effect =>
        Eq.{1} (getElem?.{0, 0, 0} s.effects q.effectIndex) (some.{0} effect) ∧ Eq.{1} family effect.identity :=
⋯
'YulangClosure.NativeCallbackCoordinatesR33.family_decode_exact' depends on axioms: [propext, sorryAx.{u}]
theorem YulangClosure.NativeCallbackCoordinatesR33.family_decode_bounded : ∀ {Token Module Parse Green : Type}
  [inst : DecidableEq.{1} Token] (s : YulangClosure.NativeCallbackCoordinatesR33.HirSnapshot Token Module Parse Green)
  (q : YulangClosure.NativeCallbackCoordinatesR33.FamilyCoordinate Token)
  {family : YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green},
  Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.decodeFamilyCoordinate s q) (some.{0} family) →
    Eq.{1} q.snapshotToken s.token ∧
      Exists.{0} fun bound => Eq.{1} family (getElem.{0, 0, 0} s.effects q.effectIndex bound).identity :=
⋯
'YulangClosure.NativeCallbackCoordinatesR33.family_decode_bounded' depends on axioms: [propext, sorryAx.{u}]
theorem YulangClosure.NativeCallbackCoordinatesR33.operation_decode_exact : ∀ {Token Module Parse Green : Type}
  [inst : DecidableEq.{1} Token] [inst_1 : DecidableEq.{1} Module] [inst_2 : DecidableEq.{1} Parse]
  [inst_3 : DecidableEq.{1} Green] (s : YulangClosure.NativeCallbackCoordinatesR33.HirSnapshot Token Module Parse Green)
  (q : YulangClosure.NativeCallbackCoordinatesR33.OperationCoordinate Token)
  {operation : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green},
  Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.decodeOperationCoordinate s q) (some.{0} operation) →
    Eq.{1} q.family.snapshotToken s.token ∧
      Exists.{1} fun effect =>
        Eq.{1} (getElem?.{0, 0, 0} s.effects q.family.effectIndex) (some.{0} effect) ∧
          Eq.{1} (getElem?.{0, 0, 0} effect.operations q.operationIndex) (some.{0} operation) ∧
            Eq.{1} operation.family effect.identity :=
⋯
'YulangClosure.NativeCallbackCoordinatesR33.operation_decode_exact' depends on axioms: [propext, sorryAx.{u}]
theorem YulangClosure.NativeCallbackCoordinatesR33.operation_decode_bounded : ∀ {Token Module Parse Green : Type}
  [inst : DecidableEq.{1} Token] [inst_1 : DecidableEq.{1} Module] [inst_2 : DecidableEq.{1} Parse]
  [inst_3 : DecidableEq.{1} Green] (s : YulangClosure.NativeCallbackCoordinatesR33.HirSnapshot Token Module Parse Green)
  (q : YulangClosure.NativeCallbackCoordinatesR33.OperationCoordinate Token)
  {operation : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green},
  Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.decodeOperationCoordinate s q) (some.{0} operation) →
    Eq.{1} q.family.snapshotToken s.token ∧
      Exists.{1} fun effect =>
        (Exists.{0} fun bound => Eq.{1} (getElem.{0, 0, 0} s.effects q.family.effectIndex bound) effect) ∧
          (Exists.{0} fun bound => Eq.{1} (getElem.{0, 0, 0} effect.operations q.operationIndex bound) operation) ∧
            Eq.{1} operation.family effect.identity :=
⋯
'YulangClosure.NativeCallbackCoordinatesR33.operation_decode_bounded' depends on axioms: [propext, sorryAx.{u}]
theorem YulangClosure.NativeCallbackCoordinatesR33.operation_family_decode : ∀ {Token Module Parse Green : Type}
  [inst : DecidableEq.{1} Token] [inst_1 : DecidableEq.{1} Module] [inst_2 : DecidableEq.{1} Parse]
  [inst_3 : DecidableEq.{1} Green] (s : YulangClosure.NativeCallbackCoordinatesR33.HirSnapshot Token Module Parse Green)
  (q : YulangClosure.NativeCallbackCoordinatesR33.OperationCoordinate Token)
  {operation : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green},
  Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.decodeOperationCoordinate s q) (some.{0} operation) →
    Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.decodeFamilyCoordinate s q.family) (some.{0} operation.family) :=
⋯
'YulangClosure.NativeCallbackCoordinatesR33.operation_family_decode' depends on axioms: [propext, sorryAx.{u}]
theorem YulangClosure.NativeCallbackCoordinatesR33.row_decode_length : ∀ {Token Module Parse Green : Type}
  [inst : DecidableEq.{1} Token] (s : YulangClosure.NativeCallbackCoordinatesR33.HirSnapshot Token Module Parse Green)
  (coordinates : List.{0} (YulangClosure.NativeCallbackCoordinatesR33.FamilyCoordinate Token))
  {families : List.{0} (YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green)},
  Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.decodeFamilyRow s coordinates) (some.{0} families) →
    Eq.{1} (List.length.{0} families) (List.length.{0} coordinates) :=
⋯
'YulangClosure.NativeCallbackCoordinatesR33.row_decode_length' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.NativeCallbackCoordinatesR33.row_bad_member_rejected : ∀ {Token Module Parse Green : Type}
  [inst : DecidableEq.{1} Token] (s : YulangClosure.NativeCallbackCoordinatesR33.HirSnapshot Token Module Parse Green)
  (coordinates : List.{0} (YulangClosure.NativeCallbackCoordinatesR33.FamilyCoordinate Token))
  {bad : YulangClosure.NativeCallbackCoordinatesR33.FamilyCoordinate Token},
  Membership.mem.{0, 0} coordinates bad →
    Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.decodeFamilyCoordinate s bad) none.{0} →
      Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.decodeFamilyRow s coordinates) none.{0} :=
⋯
'YulangClosure.NativeCallbackCoordinatesR33.row_bad_member_rejected' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.NativeCallbackCoordinatesR33.permission_row_exact : ∀ {Token Module Parse Green : Type}
  [inst : DecidableEq.{1} Token] [inst_1 : DecidableEq.{1} Module] [inst_2 : DecidableEq.{1} Parse]
  [inst_3 : DecidableEq.{1} Green] (s : YulangClosure.NativeCallbackCoordinatesR33.HirSnapshot Token Module Parse Green)
  (coordinates : List.{0} (YulangClosure.NativeCallbackCoordinatesR33.FamilyCoordinate Token))
  {families : List.{0} (YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green)},
  Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.translatePermissionRow s coordinates) (some.{0} families) →
    Eq.{1} families s.permissionRow ∧
      Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.decodeFamilyRow s coordinates) (some.{0} families) ∧
        Eq.{1} (List.length.{0} families) (List.length.{0} coordinates) :=
⋯
'YulangClosure.NativeCallbackCoordinatesR33.permission_row_exact' depends on axioms: [propext,
 sorryAx.{u},
 Quot.sound.{u}]
theorem YulangClosure.NativeCallbackCoordinatesR33.incomplete_row_rejected : ∀ {Token Module Parse Green : Type}
  [inst : DecidableEq.{1} Token] [inst_1 : DecidableEq.{1} Module] [inst_2 : DecidableEq.{1} Parse]
  [inst_3 : DecidableEq.{1} Green] (s : YulangClosure.NativeCallbackCoordinatesR33.HirSnapshot Token Module Parse Green)
  (coordinates : List.{0} (YulangClosure.NativeCallbackCoordinatesR33.FamilyCoordinate Token))
  (families : List.{0} (YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green)),
  Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.decodeFamilyRow s coordinates) (some.{0} families) →
    Ne.{1} families s.permissionRow →
      Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.translatePermissionRow s coordinates) none.{0} :=
⋯
'YulangClosure.NativeCallbackCoordinatesR33.incomplete_row_rejected' depends on axioms: [propext]
theorem YulangClosure.NativeCallbackCoordinatesR33.bad_row_rejected : ∀ {Token Module Parse Green : Type}
  [inst : DecidableEq.{1} Token] [inst_1 : DecidableEq.{1} Module] [inst_2 : DecidableEq.{1} Parse]
  [inst_3 : DecidableEq.{1} Green] (s : YulangClosure.NativeCallbackCoordinatesR33.HirSnapshot Token Module Parse Green)
  (coordinates : List.{0} (YulangClosure.NativeCallbackCoordinatesR33.FamilyCoordinate Token)),
  Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.decodeFamilyRow s coordinates) none.{0} →
    Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.translatePermissionRow s coordinates) none.{0} :=
⋯
'YulangClosure.NativeCallbackCoordinatesR33.bad_row_rejected' depends on axioms: [propext]
theorem YulangClosure.NativeCallbackCoordinatesR33.translation_exact : ∀ {Token Module Parse Green : Type}
  [inst : DecidableEq.{1} Token] [inst_1 : DecidableEq.{1} Module] [inst_2 : DecidableEq.{1} Parse]
  [inst_3 : DecidableEq.{1} Green] (s : YulangClosure.NativeCallbackCoordinatesR33.HirSnapshot Token Module Parse Green)
  (request consumer arm : YulangClosure.NativeCallbackCoordinatesR33.OperationCoordinate Token)
  (row : List.{0} (YulangClosure.NativeCallbackCoordinatesR33.FamilyCoordinate Token))
  {out : YulangClosure.NativeCallbackCoordinatesR33.DecodedCoordinates Module Parse Green},
  Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.translateCoordinates s request consumer arm row) (some.{0} out) →
    Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.decodeOperationCoordinate s request) (some.{0} out.request) ∧
      Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.decodeOperationCoordinate s consumer) (some.{0} out.consumer) ∧
        Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.decodeOperationCoordinate s arm) (some.{0} out.arm) ∧
          Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.translatePermissionRow s row) (some.{0} out.families) :=
⋯
'YulangClosure.NativeCallbackCoordinatesR33.translation_exact' depends on axioms: [propext, sorryAx.{u}]
theorem YulangClosure.NativeCallbackCoordinatesR33.translation_to_r32 : ∀ {Token Module Parse Green : Type}
  [inst : DecidableEq.{1} Token] [inst_1 : DecidableEq.{1} Module] [inst_2 : DecidableEq.{1} Parse]
  [inst_3 : DecidableEq.{1} Green] (s : YulangClosure.NativeCallbackCoordinatesR33.HirSnapshot Token Module Parse Green)
  (request consumer arm : YulangClosure.NativeCallbackCoordinatesR33.OperationCoordinate Token)
  (row : List.{0} (YulangClosure.NativeCallbackCoordinatesR33.FamilyCoordinate Token))
  {out : YulangClosure.NativeCallbackCoordinatesR33.DecodedCoordinates Module Parse Green},
  Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.translateCoordinates s request consumer arm row) (some.{0} out) →
    have table :=
      YulangClosure.NativeCallbackGrantBridgeR32.coveringTable out.request out.consumer out.arm out.families;
    Eq.{1} out.families s.permissionRow ∧
      Eq.{1} (List.length.{0} out.families) (List.length.{0} row) ∧
        Eq.{1} request.family.snapshotToken s.token ∧
          Eq.{1} consumer.family.snapshotToken s.token ∧
            Eq.{1} arm.family.snapshotToken s.token ∧
              (Exists.{1} fun effect =>
                  Membership.mem.{0, 0} s.effects effect ∧
                    Membership.mem.{0, 0} effect.operations out.request ∧ Eq.{1} out.request.family effect.identity) ∧
                (Exists.{1} fun effect =>
                    Membership.mem.{0, 0} s.effects effect ∧
                      Membership.mem.{0, 0} effect.operations out.consumer ∧
                        Eq.{1} out.consumer.family effect.identity) ∧
                  (Exists.{1} fun effect =>
                      Membership.mem.{0, 0} s.effects effect ∧
                        Membership.mem.{0, 0} effect.operations out.arm ∧ Eq.{1} out.arm.family effect.identity) ∧
                    (∀ (op : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green),
                        Membership.mem.{0, 0}
                            (List.cons.{0} out.request
                              (List.cons.{0} out.consumer (List.cons.{0} out.arm List.nil.{0})))
                            op →
                          Membership.mem.{0, 0} table.operations op) ∧
                      (∀ (family : YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green),
                          Membership.mem.{0, 0} s.permissionRow family → Membership.mem.{0, 0} table.families family) ∧
                        Eq.{1}
                            (YulangClosure.NativeCallbackGrantBridgeR31.decodeOperation table
                              (YulangClosure.NativeCallbackGrantBridgeR31.operationKey table out.request))
                            (some.{0} out.request) ∧
                          Eq.{1}
                              (YulangClosure.NativeCallbackGrantBridgeR31.decodeOperation table
                                (YulangClosure.NativeCallbackGrantBridgeR31.operationKey table out.consumer))
                              (some.{0} out.consumer) ∧
                            Eq.{1}
                                (YulangClosure.NativeCallbackGrantBridgeR31.decodeOperation table
                                  (YulangClosure.NativeCallbackGrantBridgeR31.operationKey table out.arm))
                                (some.{0} out.arm) ∧
                              ∀ (family : YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green),
                                Membership.mem.{0, 0} s.permissionRow family →
                                  Eq.{1} (getElem?.{0, 0, 0} table.families (List.idxOf.{0} family table.families))
                                      (some.{0} family) ∧
                                    (Membership.mem.{0, 0}
                                        (List.map.{0, 0} (fun a => List.idxOf.{0} a table.families) out.families)
                                        (List.idxOf.{0} family table.families) ↔
                                      Membership.mem.{0, 0} out.families family) :=
⋯
'YulangClosure.NativeCallbackCoordinatesR33.translation_to_r32' depends on axioms: [propext,
 sorryAx.{u},
 Quot.sound.{u}]

STDERR:
```

## Audit attempt 2

Same pinned read-only bwrap command and all 59 theorem names; revised exact lookup/inversion proofs. Exit 1; measured subprocess seconds 2.9742088059974776.

```text
<stdin>:1097:35: error: Application type mismatch: The argument
  rfl
has type
  ?m.208 = ?m.208
but is expected to have type
  effect.operations[q.operationIndex]? = some stored
in the application
  And.intro rfl
theorem YulangClosure.CallbackHygieneCorrespondence.checked_use_inversion : ∀
  {e : YulangClosure.CallbackHygieneCorrespondence.Entry} {n : YulangClosure.CallbackHygieneCorrespondence.NameRead}
  {u out : YulangClosure.CallbackHygieneCorrespondence.CallbackUse},
  Eq.{1} (YulangClosure.CallbackHygieneCorrespondence.checkedUse e n u) (some.{0} out) →
    Eq.{1} out u ∧ YulangClosure.CallbackHygieneCorrespondence.UseReady e n u :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.checked_use_inversion' does not depend on any axioms
theorem YulangClosure.CallbackHygieneCorrespondence.checked_catch_inversion : ∀
  {s : YulangClosure.CallbackHygieneCorrespondence.State} {r : YulangClosure.CallbackHygieneCorrespondence.Request}
  {c : YulangClosure.CallbackHygieneCorrespondence.Consumer}
  {p : YulangClosure.CallbackHygieneCorrespondence.Permission}
  {x : YulangClosure.CallbackHygieneCorrespondence.Selection},
  Eq.{1} (YulangClosure.CallbackHygieneCorrespondence.checkedCatch s r c p) (some.{0} x) →
    Eq.{1} x { request := r, consumer := c, permission := p } ∧
      YulangClosure.CallbackHygieneCorrespondence.CatchReady s r c p :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.checked_catch_inversion' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.CallbackHygieneCorrespondence.checked_catch_installed_arm : ∀
  {s : YulangClosure.CallbackHygieneCorrespondence.State} {r : YulangClosure.CallbackHygieneCorrespondence.Request}
  {c : YulangClosure.CallbackHygieneCorrespondence.Consumer}
  {p : YulangClosure.CallbackHygieneCorrespondence.Permission}
  {x : YulangClosure.CallbackHygieneCorrespondence.Selection},
  Eq.{1} (YulangClosure.CallbackHygieneCorrespondence.checkedCatch s r c p) (some.{0} x) →
    Exists.{1} fun h =>
      Membership.mem.{0, 0} s.installed h ∧
        Eq.{1} c.handler h.handle ∧
          Eq.{1} c.catchSite h.site ∧
            Eq.{1} c.owner h.owner ∧
              Exists.{1} fun a =>
                Membership.mem.{0, 0} h.arms a ∧
                  Eq.{1} c.arm a.handle ∧ Eq.{1} c.armSite a.site ∧ Eq.{1} c.operation a.operation :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.checked_catch_installed_arm' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.CallbackHygieneCorrespondence.checked_catch_port : ∀
  {s : YulangClosure.CallbackHygieneCorrespondence.State} {r : YulangClosure.CallbackHygieneCorrespondence.Request}
  {c : YulangClosure.CallbackHygieneCorrespondence.Consumer}
  {p : YulangClosure.CallbackHygieneCorrespondence.Permission}
  {x : YulangClosure.CallbackHygieneCorrespondence.Selection},
  Eq.{1} (YulangClosure.CallbackHygieneCorrespondence.checkedCatch s r c p) (some.{0} x) →
    YulangClosure.CallbackHygieneCorrespondence.PortReady s r p :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.checked_catch_port' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.CallbackHygieneCorrespondence.permission_preserves_actual : ∀
  (s : YulangClosure.CallbackHygieneCorrespondence.State) (a : YulangClosure.CallbackHygieneCorrespondence.Annotation),
  Eq.{1}
      { annotations := List.cons.{0} a s.annotations, permissions := s.permissions, installed := s.installed,
          active := s.active, invocations := s.invocations, entries := s.entries, names := s.names, uses := s.uses,
          executions := s.executions, executing := s.executing, emitted := s.emitted, pending := s.pending,
          selections := s.selections, initializing := s.initializing, lifetime := s.lifetime, nextEvent := s.nextEvent,
          nextInvocation := s.nextInvocation }.emitted
      s.emitted ∧
    Eq.{1}
      { annotations := List.cons.{0} a s.annotations, permissions := s.permissions, installed := s.installed,
          active := s.active, invocations := s.invocations, entries := s.entries, names := s.names, uses := s.uses,
          executions := s.executions, executing := s.executing, emitted := s.emitted, pending := s.pending,
          selections := s.selections, initializing := s.initializing, lifetime := s.lifetime, nextEvent := s.nextEvent,
          nextInvocation := s.nextInvocation }.pending
      s.pending :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.permission_preserves_actual' does not depend on any axioms
theorem YulangClosure.CallbackHygieneCorrespondence.emit_conserved : ∀
  {s : YulangClosure.CallbackHygieneCorrespondence.State},
  YulangClosure.CallbackHygieneCorrespondence.Conserved s →
    ∀ (r : YulangClosure.CallbackHygieneCorrespondence.Request),
      YulangClosure.CallbackHygieneCorrespondence.Conserved (YulangClosure.CallbackHygieneCorrespondence.emit s r) :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.emit_conserved' depends on axioms: [propext]
theorem YulangClosure.CallbackHygieneCorrespondence.commit_conserved : ∀
  {s : YulangClosure.CallbackHygieneCorrespondence.State},
  YulangClosure.CallbackHygieneCorrespondence.Conserved s →
    ∀ {r : YulangClosure.CallbackHygieneCorrespondence.Request}
      {c : YulangClosure.CallbackHygieneCorrespondence.Consumer}
      {p : YulangClosure.CallbackHygieneCorrespondence.Permission}
      {x : YulangClosure.CallbackHygieneCorrespondence.Selection},
      Eq.{1} (YulangClosure.CallbackHygieneCorrespondence.checkedCatch s r c p) (some.{0} x) →
        YulangClosure.CallbackHygieneCorrespondence.Conserved
          (YulangClosure.CallbackHygieneCorrespondence.commit s x) :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.commit_conserved' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.CallbackHygieneCorrespondence.step_conserved : ∀
  {before after : YulangClosure.CallbackHygieneCorrespondence.State},
  YulangClosure.CallbackHygieneCorrespondence.Step before after →
    YulangClosure.CallbackHygieneCorrespondence.Conserved before →
      YulangClosure.CallbackHygieneCorrespondence.Conserved after :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.step_conserved' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.CallbackHygieneCorrespondence.history_conserved : ∀
  {initial final : YulangClosure.CallbackHygieneCorrespondence.State},
  YulangClosure.CallbackHygieneCorrespondence.History initial final →
    YulangClosure.CallbackHygieneCorrespondence.Conserved initial →
      YulangClosure.CallbackHygieneCorrespondence.Conserved final :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.history_conserved' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.CallbackHygieneCorrespondence.empty_conserved : YulangClosure.CallbackHygieneCorrespondence.Conserved
  { } :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.empty_conserved' does not depend on any axioms
theorem YulangClosure.CallbackHygieneCorrespondence.emit_events_before : ∀
  {s : YulangClosure.CallbackHygieneCorrespondence.State},
  YulangClosure.CallbackHygieneCorrespondence.EventsBefore s →
    ∀ (r : YulangClosure.CallbackHygieneCorrespondence.Request),
      YulangClosure.CallbackHygieneCorrespondence.EventsBefore (YulangClosure.CallbackHygieneCorrespondence.emit s r) :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.emit_events_before' depends on axioms: [propext]
theorem YulangClosure.CallbackHygieneCorrespondence.step_events_before : ∀
  {before after : YulangClosure.CallbackHygieneCorrespondence.State},
  YulangClosure.CallbackHygieneCorrespondence.Step before after →
    YulangClosure.CallbackHygieneCorrespondence.EventsBefore before →
      YulangClosure.CallbackHygieneCorrespondence.EventsBefore after :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.step_events_before' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.CallbackHygieneCorrespondence.generated_events_before : ∀
  {final : YulangClosure.CallbackHygieneCorrespondence.State},
  YulangClosure.CallbackHygieneCorrespondence.History { } final →
    YulangClosure.CallbackHygieneCorrespondence.EventsBefore final :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.generated_events_before' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.CallbackHygieneCorrespondence.generated_selection_actual : ∀
  {final : YulangClosure.CallbackHygieneCorrespondence.State},
  YulangClosure.CallbackHygieneCorrespondence.History { } final →
    ∀ {x : YulangClosure.CallbackHygieneCorrespondence.Selection},
      Membership.mem.{0, 0} final.selections x →
        Membership.mem.{0, 0} final.emitted x.request ∧
          Eq.{1} x.consumer.operation x.request.operation ∧
            Eq.{1} x.consumer.event x.request.event ∧
              Eq.{1} x.consumer.payload x.request.payload ∧
                Eq.{1} x.consumer.owner x.permission.owner ∧
                  Membership.mem.{0, 0} x.permission.families x.request.operation.family :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.generated_selection_actual' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.CallbackHygieneCorrespondence.empty_inflow_rejected : ∀
  (s : YulangClosure.CallbackHygieneCorrespondence.State) (r : YulangClosure.CallbackHygieneCorrespondence.Request)
  (c : YulangClosure.CallbackHygieneCorrespondence.Consumer)
  (p : YulangClosure.CallbackHygieneCorrespondence.Permission),
  Eq.{1} s.pending List.nil.{0} → Eq.{1} (YulangClosure.CallbackHygieneCorrespondence.checkedCatch s r c p) none.{0} :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.empty_inflow_rejected' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.CallbackHygieneCorrespondence.companion_event_fresh : ∀
  {s : YulangClosure.CallbackHygieneCorrespondence.State},
  YulangClosure.CallbackHygieneCorrespondence.History { } s →
    ∀ {inner : YulangClosure.CallbackHygieneCorrespondence.Selection},
      Membership.mem.{0, 0} s.selections inner →
        ∀ (r : YulangClosure.CallbackHygieneCorrespondence.Request),
          Ne.{1} (YulangClosure.CallbackHygieneCorrespondence.minted s r).event inner.request.event :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.companion_event_fresh' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.CallbackHygieneCorrespondence.commit_preserves_other_event : ∀
  (s : YulangClosure.CallbackHygieneCorrespondence.State) (x : YulangClosure.CallbackHygieneCorrespondence.Selection)
  (write : YulangClosure.CallbackHygieneCorrespondence.Request),
  Membership.mem.{0, 0} s.pending write →
    Ne.{1} write.event x.request.event →
      Membership.mem.{0, 0} (YulangClosure.CallbackHygieneCorrespondence.commit s x).pending write :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.commit_preserves_other_event' depends on axioms: [propext]
theorem YulangClosure.CallbackHygieneCorrespondence.commit_removes_selected_event : ∀
  (s : YulangClosure.CallbackHygieneCorrespondence.State) (x : YulangClosure.CallbackHygieneCorrespondence.Selection)
  (r : YulangClosure.CallbackHygieneCorrespondence.Request),
  Membership.mem.{0, 0} (YulangClosure.CallbackHygieneCorrespondence.commit s x).pending r →
    Ne.{1} r.event x.request.event :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.commit_removes_selected_event' depends on axioms: [propext]
theorem YulangClosure.CallbackHygieneCorrespondence.companion_emit_actual : ∀
  (s : YulangClosure.CallbackHygieneCorrespondence.State) (r : YulangClosure.CallbackHygieneCorrespondence.Request),
  Membership.mem.{0, 0} (YulangClosure.CallbackHygieneCorrespondence.emit s r).emitted
      (YulangClosure.CallbackHygieneCorrespondence.minted s r) ∧
    Membership.mem.{0, 0} (YulangClosure.CallbackHygieneCorrespondence.emit s r).pending
        (YulangClosure.CallbackHygieneCorrespondence.minted s r) ∧
      Eq.{1} (YulangClosure.CallbackHygieneCorrespondence.minted s r).operation r.operation ∧
        Eq.{1} (YulangClosure.CallbackHygieneCorrespondence.minted s r).payload r.payload ∧
          Eq.{1} (YulangClosure.CallbackHygieneCorrespondence.minted s r).lineage r.lineage :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.companion_emit_actual' does not depend on any axioms
theorem YulangClosure.CallbackHygieneCorrespondence.shallow_discard_preserves_contributions : ∀
  (s : YulangClosure.CallbackHygieneCorrespondence.State)
  (cells :
    List.{0} (YulangClosure.CallbackHygieneCorrespondence.Id YulangClosure.CallbackHygieneCorrespondence.Kind.cell)),
  Eq.{1}
      { annotations := s.annotations, permissions := s.permissions, installed := s.installed, active := s.active,
          invocations := s.invocations, entries := s.entries, names := s.names, uses := s.uses,
          executions := s.executions, executing := s.executing, emitted := s.emitted, pending := s.pending,
          selections := s.selections,
          initializing := List.filter.{0} (fun cell => decide ¬Membership.mem.{0, 0} cells cell) s.initializing,
          lifetime :=
            List.cons.{0} (YulangClosure.CallbackHygieneCorrespondence.Lifetime.shallowDiscard cells) s.lifetime,
          nextEvent := s.nextEvent, nextInvocation := s.nextInvocation }.pending
      s.pending ∧
    Eq.{1}
        { annotations := s.annotations, permissions := s.permissions, installed := s.installed, active := s.active,
            invocations := s.invocations, entries := s.entries, names := s.names, uses := s.uses,
            executions := s.executions, executing := s.executing, emitted := s.emitted, pending := s.pending,
            selections := s.selections,
            initializing := List.filter.{0} (fun cell => decide ¬Membership.mem.{0, 0} cells cell) s.initializing,
            lifetime :=
              List.cons.{0} (YulangClosure.CallbackHygieneCorrespondence.Lifetime.shallowDiscard cells) s.lifetime,
            nextEvent := s.nextEvent, nextInvocation := s.nextInvocation }.emitted
        s.emitted ∧
      Eq.{1}
        { annotations := s.annotations, permissions := s.permissions, installed := s.installed, active := s.active,
            invocations := s.invocations, entries := s.entries, names := s.names, uses := s.uses,
            executions := s.executions, executing := s.executing, emitted := s.emitted, pending := s.pending,
            selections := s.selections,
            initializing := List.filter.{0} (fun cell => decide ¬Membership.mem.{0, 0} cells cell) s.initializing,
            lifetime :=
              List.cons.{0} (YulangClosure.CallbackHygieneCorrespondence.Lifetime.shallowDiscard cells) s.lifetime,
            nextEvent := s.nextEvent, nextInvocation := s.nextInvocation }.active
        s.active :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.shallow_discard_preserves_contributions' depends on axioms: [propext]
theorem YulangClosure.CallbackHygieneCorrespondence.normal_return_deactivates : ∀
  (s : YulangClosure.CallbackHygieneCorrespondence.State)
  (owner : YulangClosure.CallbackHygieneCorrespondence.Id YulangClosure.CallbackHygieneCorrespondence.Kind.invocation),
  ¬Membership.mem.{0, 0}
      { annotations := s.annotations, permissions := s.permissions, installed := s.installed,
          active := List.filter.{0} (fun current => decide (Ne.{1} current owner)) s.active,
          invocations := s.invocations, entries := s.entries, names := s.names, uses := s.uses,
          executions := s.executions, executing := s.executing, emitted := s.emitted, pending := s.pending,
          selections := s.selections, initializing := s.initializing,
          lifetime :=
            List.cons.{0} (YulangClosure.CallbackHygieneCorrespondence.Lifetime.normalReturn owner) s.lifetime,
          nextEvent := s.nextEvent, nextInvocation := s.nextInvocation }.active
      owner :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.normal_return_deactivates' depends on axioms: [propext]
theorem YulangClosure.CallbackHygieneCorrespondence.lifetime_branches_distinct : ∀
  (owner : YulangClosure.CallbackHygieneCorrespondence.Id YulangClosure.CallbackHygieneCorrespondence.Kind.invocation)
  (cells :
    List.{0} (YulangClosure.CallbackHygieneCorrespondence.Id YulangClosure.CallbackHygieneCorrespondence.Kind.cell)),
  Ne.{1} (YulangClosure.CallbackHygieneCorrespondence.Lifetime.normalReturn owner)
    (YulangClosure.CallbackHygieneCorrespondence.Lifetime.shallowDiscard cells) :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.lifetime_branches_distinct' does not depend on any axioms
theorem YulangClosure.NativeCallbackGrantBridgeR31.finite_index_round_trip : ∀ {α : Type} [inst : DecidableEq.{1} α]
  (table : List.{0} α) (a : α),
  Membership.mem.{0, 0} table a → Eq.{1} (getElem?.{0, 0, 0} table (List.idxOf.{0} a table)) (some.{0} a) :=
⋯
'YulangClosure.NativeCallbackGrantBridgeR31.finite_index_round_trip' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.NativeCallbackGrantBridgeR31.finite_index_injective : ∀ {α : Type} [inst : DecidableEq.{1} α]
  (table : List.{0} α) {a b : α},
  Membership.mem.{0, 0} table a →
    Membership.mem.{0, 0} table b → Eq.{1} (List.idxOf.{0} a table) (List.idxOf.{0} b table) → Eq.{1} a b :=
⋯
'YulangClosure.NativeCallbackGrantBridgeR31.finite_index_injective' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.NativeCallbackGrantBridgeR31.operation_round_trip : ∀ {Module Parse Green : Type}
  [inst : DecidableEq.{1} Module] [inst_1 : DecidableEq.{1} Parse] [inst_2 : DecidableEq.{1} Green]
  (table : YulangClosure.NativeCallbackGrantBridgeR31.IdentityTable Module Parse Green)
  (operation : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green),
  Membership.mem.{0, 0} table.operations operation →
    Membership.mem.{0, 0} table.families operation.family →
      Eq.{1}
        (YulangClosure.NativeCallbackGrantBridgeR31.decodeOperation table
          (YulangClosure.NativeCallbackGrantBridgeR31.operationKey table operation))
        (some.{0} operation) :=
⋯
'YulangClosure.NativeCallbackGrantBridgeR31.operation_round_trip' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.NativeCallbackGrantBridgeR31.operationKey_injective : ∀ {Module Parse Green : Type}
  [inst : DecidableEq.{1} Module] [inst_1 : DecidableEq.{1} Parse] [inst_2 : DecidableEq.{1} Green]
  (table : YulangClosure.NativeCallbackGrantBridgeR31.IdentityTable Module Parse Green)
  {a b : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green},
  Membership.mem.{0, 0} table.operations a →
    Membership.mem.{0, 0} table.operations b →
      Eq.{1} (YulangClosure.NativeCallbackGrantBridgeR31.operationKey table a)
          (YulangClosure.NativeCallbackGrantBridgeR31.operationKey table b) →
        Eq.{1} a b :=
⋯
'YulangClosure.NativeCallbackGrantBridgeR31.operationKey_injective' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.NativeCallbackGrantBridgeR31.encoded_family_member : ∀ {Module Parse Green : Type}
  [inst : DecidableEq.{1} Module] [inst_1 : DecidableEq.{1} Parse] [inst_2 : DecidableEq.{1} Green]
  (table : YulangClosure.NativeCallbackGrantBridgeR31.IdentityTable Module Parse Green)
  {family : YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green}
  {row : List.{0} (YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green)},
  Membership.mem.{0, 0} row family →
    Membership.mem.{0, 0} (List.map.{0, 0} (fun a => List.idxOf.{0} a table.families) row)
      (List.idxOf.{0} family table.families) :=
⋯
'YulangClosure.NativeCallbackGrantBridgeR31.encoded_family_member' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.NativeCallbackGrantBridgeR31.encoded_family_member_iff : ∀ {Module Parse Green : Type}
  [inst : DecidableEq.{1} Module] [inst_1 : DecidableEq.{1} Parse] [inst_2 : DecidableEq.{1} Green]
  (table : YulangClosure.NativeCallbackGrantBridgeR31.IdentityTable Module Parse Green)
  {family : YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green}
  {row : List.{0} (YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green)},
  (∀ (f : YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green),
      Membership.mem.{0, 0} row f → Membership.mem.{0, 0} table.families f) →
    Membership.mem.{0, 0} table.families family →
      (Membership.mem.{0, 0} (List.map.{0, 0} (fun a => List.idxOf.{0} a table.families) row)
          (List.idxOf.{0} family table.families) ↔
        Membership.mem.{0, 0} row family) :=
⋯
'YulangClosure.NativeCallbackGrantBridgeR31.encoded_family_member_iff' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.NativeCallbackGrantBridgeR31.callback_use_ready : ∀
  (e : YulangClosure.CallbackHygieneCorrespondence.Entry) (n : YulangClosure.CallbackHygieneCorrespondence.NameRead)
  (u : YulangClosure.CallbackHygieneCorrespondence.CallbackUse),
  Eq.{1} e.permission.port YulangClosure.CallbackHygieneCorrespondence.Port.callbackResult →
    Eq.{1} e.formalReceipt.owner e.permission.owner →
      Eq.{1} e.formalReceipt.view e.view →
        Eq.{1} e.formalReceipt.site e.permission.lambdaSite →
          Eq.{1} e.formalReceipt.formal (some.{0} e.permission.formal) →
            Eq.{1} n.entry e.handle →
              Eq.{1} n.formal e.permission.formal →
                Eq.{1} n.receipt.owner e.permission.owner →
                  Eq.{1} n.receipt.view e.view →
                    Eq.{1} n.receipt.site n.site →
                      Eq.{1} n.receipt.formal none.{0} →
                        Eq.{1} u.entry e.handle →
                          Eq.{1} u.owner e.permission.owner →
                            Eq.{1} u.sourceView e.view →
                              Eq.{1} u.formalReceipt e.formalReceipt.handle →
                                Eq.{1} u.nameReceipt n.receipt.handle →
                                  Eq.{1} u.callee n.site →
                                    Eq.{1} u.resultReceipt.owner u.owner →
                                      Eq.{1} u.resultReceipt.view u.resultView →
                                        Eq.{1} u.resultReceipt.site u.applySite →
                                          Eq.{1} u.resultReceipt.formal none.{0} →
                                            YulangClosure.CallbackHygieneCorrespondence.UseReady e n u :=
⋯
'YulangClosure.NativeCallbackGrantBridgeR31.callback_use_ready' does not depend on any axioms
theorem YulangClosure.NativeCallbackGrantBridgeR31.callback_checked_catch : ∀ {Module Parse Green : Type}
  [inst : DecidableEq.{1} Module] [inst_1 : DecidableEq.{1} Parse] [inst_2 : DecidableEq.{1} Green]
  (table : YulangClosure.NativeCallbackGrantBridgeR31.IdentityTable Module Parse Green)
  (r : YulangClosure.NativeCallbackGrantBridgeR31.NativeRequest Module Parse Green)
  (c : YulangClosure.NativeCallbackGrantBridgeR31.NativeConsumer Module Parse Green)
  (a : YulangClosure.NativeCallbackGrantBridgeR31.NativeArm Module Parse Green)
  (e : YulangClosure.CallbackHygieneCorrespondence.Entry) (n : YulangClosure.CallbackHygieneCorrespondence.NameRead)
  (u : YulangClosure.CallbackHygieneCorrespondence.CallbackUse)
  (x : YulangClosure.CallbackHygieneCorrespondence.Execution)
  (active :
    List.{0}
      (YulangClosure.CallbackHygieneCorrespondence.Id YulangClosure.CallbackHygieneCorrespondence.Kind.invocation))
  (installation : YulangClosure.CallbackHygieneCorrespondence.InstalledCatch)
  (families : List.{0} (YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green)),
  YulangClosure.CallbackHygieneCorrespondence.UseReady e n u →
    Eq.{1} x.useHandle u.handle →
      Eq.{1} x.view u.resultView →
        Eq.{1} x.receipt u.resultReceipt.handle →
          Eq.{1} r.coordinates.origin (YulangClosure.CallbackHygieneCorrespondence.Origin.callback x) →
            Eq.{1} e.permission.families (List.map.{0, 0} (fun a => List.idxOf.{0} a table.families) families) →
              Membership.mem.{0, 0} families r.operation.family →
                Membership.mem.{0, 0} active c.coordinates.owner →
                  Eq.{1} c.coordinates.owner e.permission.owner →
                    Eq.{1} c.operation r.operation →
                      Eq.{1} c.coordinates.event r.coordinates.event →
                        Eq.{1} c.coordinates.payload r.coordinates.payload →
                          Eq.{1} c.coordinates.handler installation.handle →
                            Eq.{1} c.coordinates.catchSite installation.site →
                              Eq.{1} c.coordinates.owner installation.owner →
                                Membership.mem.{0, 0} installation.arms
                                    (YulangClosure.NativeCallbackGrantBridgeR31.armKey table a) →
                                  Eq.{1} c.coordinates.arm a.coordinates.handle →
                                    Eq.{1} c.coordinates.armSite a.coordinates.site →
                                      Eq.{1} c.operation a.operation →
                                        Eq.{1}
                                          (YulangClosure.CallbackHygieneCorrespondence.checkedCatch
                                            (YulangClosure.NativeCallbackGrantBridgeR31.callbackSlice e n u x
                                              (YulangClosure.NativeCallbackGrantBridgeR31.requestKey table r)
                                              e.permission active installation)
                                            (YulangClosure.NativeCallbackGrantBridgeR31.requestKey table r)
                                            (YulangClosure.NativeCallbackGrantBridgeR31.consumerKey table c)
                                            e.permission)
                                          (some.{0}
                                            { request := YulangClosure.NativeCallbackGrantBridgeR31.requestKey table r,
                                              consumer :=
                                                YulangClosure.NativeCallbackGrantBridgeR31.consumerKey table c,
                                              permission := e.permission }) :=
⋯
'YulangClosure.NativeCallbackGrantBridgeR31.callback_checked_catch' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.NativeCallbackGrantBridgeR32.referenced_operations_covered : ∀ {Module Parse Green : Type}
  (r c a : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green)
  (families : List.{0} (YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green))
  (op : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green),
  Membership.mem.{0, 0} (List.cons.{0} r (List.cons.{0} c (List.cons.{0} a List.nil.{0}))) op →
    Membership.mem.{0, 0} (YulangClosure.NativeCallbackGrantBridgeR32.coveringTable r c a families).operations op :=
⋯
'YulangClosure.NativeCallbackGrantBridgeR32.referenced_operations_covered' does not depend on any axioms
theorem YulangClosure.NativeCallbackGrantBridgeR32.referenced_families_covered : ∀ {Module Parse Green : Type}
  (r c a : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green)
  (families : List.{0} (YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green))
  (op : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green),
  Membership.mem.{0, 0} (List.cons.{0} r (List.cons.{0} c (List.cons.{0} a List.nil.{0}))) op →
    Membership.mem.{0, 0} (YulangClosure.NativeCallbackGrantBridgeR32.coveringTable r c a families).families
      op.family :=
⋯
'YulangClosure.NativeCallbackGrantBridgeR32.referenced_families_covered' depends on axioms: [propext]
theorem YulangClosure.NativeCallbackGrantBridgeR32.permission_families_covered : ∀ {Module Parse Green : Type}
  (r c a : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green)
  (families : List.{0} (YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green))
  (f : YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green),
  Membership.mem.{0, 0} families f →
    Membership.mem.{0, 0} (YulangClosure.NativeCallbackGrantBridgeR32.coveringTable r c a families).families f :=
⋯
'YulangClosure.NativeCallbackGrantBridgeR32.permission_families_covered' does not depend on any axioms
theorem YulangClosure.NativeCallbackGrantBridgeR32.referenced_operation_round_trip : ∀ {Module Parse Green : Type}
  [inst : DecidableEq.{1} Module] [inst_1 : DecidableEq.{1} Parse] [inst_2 : DecidableEq.{1} Green]
  (r c a : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green)
  (families : List.{0} (YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green))
  {op : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green},
  Membership.mem.{0, 0} (List.cons.{0} r (List.cons.{0} c (List.cons.{0} a List.nil.{0}))) op →
    Eq.{1}
      (YulangClosure.NativeCallbackGrantBridgeR31.decodeOperation
        (YulangClosure.NativeCallbackGrantBridgeR32.coveringTable r c a families)
        (YulangClosure.NativeCallbackGrantBridgeR31.operationKey
          (YulangClosure.NativeCallbackGrantBridgeR32.coveringTable r c a families) op))
      (some.{0} op) :=
⋯
'YulangClosure.NativeCallbackGrantBridgeR32.referenced_operation_round_trip' depends on axioms: [propext,
 Quot.sound.{u}]
theorem YulangClosure.NativeCallbackGrantBridgeR32.covered_operation_keys_distinct : ∀ {Module Parse Green : Type}
  [inst : DecidableEq.{1} Module] [inst_1 : DecidableEq.{1} Parse] [inst_2 : DecidableEq.{1} Green]
  (r c a : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green)
  (families : List.{0} (YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green))
  {left right : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green},
  Membership.mem.{0, 0} (List.cons.{0} r (List.cons.{0} c (List.cons.{0} a List.nil.{0}))) left →
    Membership.mem.{0, 0} (List.cons.{0} r (List.cons.{0} c (List.cons.{0} a List.nil.{0}))) right →
      Ne.{1} left right →
        Ne.{1}
          (YulangClosure.NativeCallbackGrantBridgeR31.operationKey
            (YulangClosure.NativeCallbackGrantBridgeR32.coveringTable r c a families) left)
          (YulangClosure.NativeCallbackGrantBridgeR31.operationKey
            (YulangClosure.NativeCallbackGrantBridgeR32.coveringTable r c a families) right) :=
⋯
'YulangClosure.NativeCallbackGrantBridgeR32.covered_operation_keys_distinct' depends on axioms: [propext,
 Quot.sound.{u}]
theorem YulangClosure.NativeCallbackGrantBridgeR32.covered_family_membership_iff : ∀ {Module Parse Green : Type}
  [inst : DecidableEq.{1} Module] [inst_1 : DecidableEq.{1} Parse] [inst_2 : DecidableEq.{1} Green]
  (r c a : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green)
  (families : List.{0} (YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green))
  {op : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green},
  Membership.mem.{0, 0} (List.cons.{0} r (List.cons.{0} c (List.cons.{0} a List.nil.{0}))) op →
    (Membership.mem.{0, 0}
        (List.map.{0, 0}
          (fun a_1 =>
            List.idxOf.{0} a_1 (YulangClosure.NativeCallbackGrantBridgeR32.coveringTable r c a families).families)
          families)
        (List.idxOf.{0} op.family (YulangClosure.NativeCallbackGrantBridgeR32.coveringTable r c a families).families) ↔
      Membership.mem.{0, 0} families op.family) :=
⋯
'YulangClosure.NativeCallbackGrantBridgeR32.covered_family_membership_iff' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.NativeCallbackGrantBridgeR32.permission_row_round_trip : ∀ {Module Parse Green : Type}
  [inst : DecidableEq.{1} Module] [inst_1 : DecidableEq.{1} Parse] [inst_2 : DecidableEq.{1} Green]
  (r c a : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green)
  (families : List.{0} (YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green))
  {f : YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green},
  Membership.mem.{0, 0} families f →
    have table := YulangClosure.NativeCallbackGrantBridgeR32.coveringTable r c a families;
    Eq.{1} (getElem?.{0, 0, 0} table.families (List.idxOf.{0} f table.families)) (some.{0} f) ∧
      (Membership.mem.{0, 0} (List.map.{0, 0} (fun a => List.idxOf.{0} a table.families) families)
          (List.idxOf.{0} f table.families) ↔
        Membership.mem.{0, 0} families f) :=
⋯
'YulangClosure.NativeCallbackGrantBridgeR32.permission_row_round_trip' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.NativeCallbackGrantBridgeR32.entryWithRow_use_ready : ∀ {Module Parse Green : Type}
  [inst : DecidableEq.{1} Module] [inst_1 : DecidableEq.{1} Parse] [inst_2 : DecidableEq.{1} Green]
  (table : YulangClosure.NativeCallbackGrantBridgeR31.IdentityTable Module Parse Green)
  (families : List.{0} (YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green))
  (e : YulangClosure.CallbackHygieneCorrespondence.Entry) (n : YulangClosure.CallbackHygieneCorrespondence.NameRead)
  (u : YulangClosure.CallbackHygieneCorrespondence.CallbackUse),
  YulangClosure.CallbackHygieneCorrespondence.UseReady e n u →
    YulangClosure.CallbackHygieneCorrespondence.UseReady
      (YulangClosure.NativeCallbackGrantBridgeR32.entryWithRow table families e) n u :=
⋯
'YulangClosure.NativeCallbackGrantBridgeR32.entryWithRow_use_ready' does not depend on any axioms
theorem YulangClosure.NativeCallbackGrantBridgeR32.empty_table_collapse : ∀ {Module Parse Green : Type}
  [inst : DecidableEq.{1} Module] [inst_1 : DecidableEq.{1} Parse] [inst_2 : DecidableEq.{1} Green]
  (left right : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green),
  Eq.{1}
      (YulangClosure.NativeCallbackGrantBridgeR31.operationKey { families := List.nil.{0}, operations := List.nil.{0} }
        left)
      (YulangClosure.NativeCallbackGrantBridgeR31.operationKey { families := List.nil.{0}, operations := List.nil.{0} }
        right) ∧
    Eq.{1}
      (YulangClosure.NativeCallbackGrantBridgeR31.decodeOperation
        { families := List.nil.{0}, operations := List.nil.{0} }
        (YulangClosure.NativeCallbackGrantBridgeR31.operationKey
          { families := List.nil.{0}, operations := List.nil.{0} } left))
      none.{0} :=
⋯
'YulangClosure.NativeCallbackGrantBridgeR32.empty_table_collapse' depends on axioms: [propext]
theorem YulangClosure.NativeCallbackGrantBridgeR32.empty_table_not_covered : ∀ {Module Parse Green : Type}
  (op : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green),
  ¬Membership.mem.{0, 0} { families := List.nil.{0}, operations := List.nil.{0} }.operations op :=
⋯
'YulangClosure.NativeCallbackGrantBridgeR32.empty_table_not_covered' depends on axioms: [propext]
theorem YulangClosure.NativeCallbackGrantBridgeR32.covered_checked_catch : ∀ {Module Parse Green : Type}
  [inst : DecidableEq.{1} Module] [inst_1 : DecidableEq.{1} Parse] [inst_2 : DecidableEq.{1} Green]
  (r : YulangClosure.NativeCallbackGrantBridgeR31.NativeRequest Module Parse Green)
  (c : YulangClosure.NativeCallbackGrantBridgeR31.NativeConsumer Module Parse Green)
  (a : YulangClosure.NativeCallbackGrantBridgeR31.NativeArm Module Parse Green)
  (e : YulangClosure.CallbackHygieneCorrespondence.Entry) (n : YulangClosure.CallbackHygieneCorrespondence.NameRead)
  (u : YulangClosure.CallbackHygieneCorrespondence.CallbackUse)
  (x : YulangClosure.CallbackHygieneCorrespondence.Execution)
  (active :
    List.{0}
      (YulangClosure.CallbackHygieneCorrespondence.Id YulangClosure.CallbackHygieneCorrespondence.Kind.invocation))
  (installation : YulangClosure.CallbackHygieneCorrespondence.InstalledCatch)
  (families : List.{0} (YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green)),
  YulangClosure.CallbackHygieneCorrespondence.UseReady e n u →
    Eq.{1} x.useHandle u.handle →
      Eq.{1} x.view u.resultView →
        Eq.{1} x.receipt u.resultReceipt.handle →
          Eq.{1} r.coordinates.origin (YulangClosure.CallbackHygieneCorrespondence.Origin.callback x) →
            Membership.mem.{0, 0} families r.operation.family →
              Membership.mem.{0, 0} active c.coordinates.owner →
                Eq.{1} c.coordinates.owner e.permission.owner →
                  Eq.{1} c.operation r.operation →
                    Eq.{1} c.coordinates.event r.coordinates.event →
                      Eq.{1} c.coordinates.payload r.coordinates.payload →
                        Eq.{1} c.coordinates.handler installation.handle →
                          Eq.{1} c.coordinates.catchSite installation.site →
                            Eq.{1} c.coordinates.owner installation.owner →
                              Membership.mem.{0, 0} installation.arms
                                  (YulangClosure.NativeCallbackGrantBridgeR31.armKey
                                    (YulangClosure.NativeCallbackGrantBridgeR32.coveringTable r.operation c.operation
                                      a.operation families)
                                    a) →
                                Eq.{1} c.coordinates.arm a.coordinates.handle →
                                  Eq.{1} c.coordinates.armSite a.coordinates.site →
                                    Eq.{1} c.operation a.operation →
                                      have table :=
                                        YulangClosure.NativeCallbackGrantBridgeR32.coveringTable r.operation c.operation
                                          a.operation families;
                                      have projectedEntry :=
                                        YulangClosure.NativeCallbackGrantBridgeR32.entryWithRow table families e;
                                      Eq.{1}
                                          (YulangClosure.NativeCallbackGrantBridgeR31.decodeOperation table
                                            (YulangClosure.NativeCallbackGrantBridgeR31.requestKey table r).operation)
                                          (some.{0} r.operation) ∧
                                        Eq.{1}
                                            (YulangClosure.NativeCallbackGrantBridgeR31.decodeOperation table
                                              (YulangClosure.NativeCallbackGrantBridgeR31.consumerKey table
                                                  c).operation)
                                            (some.{0} c.operation) ∧
                                          Eq.{1}
                                              (YulangClosure.NativeCallbackGrantBridgeR31.decodeOperation table
                                                (YulangClosure.NativeCallbackGrantBridgeR31.armKey table a).operation)
                                              (some.{0} a.operation) ∧
                                            (Membership.mem.{0, 0} projectedEntry.permission.families
                                                  (YulangClosure.NativeCallbackGrantBridgeR31.requestKey table
                                                        r).operation.family ↔
                                                Membership.mem.{0, 0} families r.operation.family) ∧
                                              Eq.{1}
                                                (YulangClosure.CallbackHygieneCorrespondence.checkedCatch
                                                  (YulangClosure.NativeCallbackGrantBridgeR31.callbackSlice
                                                    projectedEntry n u x
                                                    (YulangClosure.NativeCallbackGrantBridgeR31.requestKey table r)
                                                    projectedEntry.permission active installation)
                                                  (YulangClosure.NativeCallbackGrantBridgeR31.requestKey table r)
                                                  (YulangClosure.NativeCallbackGrantBridgeR31.consumerKey table c)
                                                  projectedEntry.permission)
                                                (some.{0}
                                                  {
                                                    request :=
                                                      YulangClosure.NativeCallbackGrantBridgeR31.requestKey table r,
                                                    consumer :=
                                                      YulangClosure.NativeCallbackGrantBridgeR31.consumerKey table c,
                                                    permission := projectedEntry.permission }) :=
⋯
'YulangClosure.NativeCallbackGrantBridgeR32.covered_checked_catch' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.NativeCallbackCoordinatesR33.family_wrong_token : ∀ {Token Module Parse Green : Type}
  [inst : DecidableEq.{1} Token] (s : YulangClosure.NativeCallbackCoordinatesR33.HirSnapshot Token Module Parse Green)
  (q : YulangClosure.NativeCallbackCoordinatesR33.FamilyCoordinate Token),
  Ne.{1} q.snapshotToken s.token →
    Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.decodeFamilyCoordinate s q) none.{0} :=
⋯
'YulangClosure.NativeCallbackCoordinatesR33.family_wrong_token' depends on axioms: [propext]
theorem YulangClosure.NativeCallbackCoordinatesR33.operation_wrong_token : ∀ {Token Module Parse Green : Type}
  [inst : DecidableEq.{1} Token] [inst_1 : DecidableEq.{1} Module] [inst_2 : DecidableEq.{1} Parse]
  [inst_3 : DecidableEq.{1} Green] (s : YulangClosure.NativeCallbackCoordinatesR33.HirSnapshot Token Module Parse Green)
  (q : YulangClosure.NativeCallbackCoordinatesR33.OperationCoordinate Token),
  Ne.{1} q.family.snapshotToken s.token →
    Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.decodeOperationCoordinate s q) none.{0} :=
⋯
'YulangClosure.NativeCallbackCoordinatesR33.operation_wrong_token' depends on axioms: [propext]
theorem YulangClosure.NativeCallbackCoordinatesR33.family_out_of_range : ∀ {Token Module Parse Green : Type}
  [inst : DecidableEq.{1} Token] (s : YulangClosure.NativeCallbackCoordinatesR33.HirSnapshot Token Module Parse Green)
  (q : YulangClosure.NativeCallbackCoordinatesR33.FamilyCoordinate Token),
  LE.le.{0} (List.length.{0} s.effects) q.effectIndex →
    Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.decodeFamilyCoordinate s q) none.{0} :=
⋯
'YulangClosure.NativeCallbackCoordinatesR33.family_out_of_range' depends on axioms: [propext]
theorem YulangClosure.NativeCallbackCoordinatesR33.operation_effect_out_of_range : ∀ {Token Module Parse Green : Type}
  [inst : DecidableEq.{1} Token] [inst_1 : DecidableEq.{1} Module] [inst_2 : DecidableEq.{1} Parse]
  [inst_3 : DecidableEq.{1} Green] (s : YulangClosure.NativeCallbackCoordinatesR33.HirSnapshot Token Module Parse Green)
  (q : YulangClosure.NativeCallbackCoordinatesR33.OperationCoordinate Token),
  LE.le.{0} (List.length.{0} s.effects) q.family.effectIndex →
    Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.decodeOperationCoordinate s q) none.{0} :=
⋯
'YulangClosure.NativeCallbackCoordinatesR33.operation_effect_out_of_range' depends on axioms: [propext]
theorem YulangClosure.NativeCallbackCoordinatesR33.operation_out_of_range : ∀ {Token Module Parse Green : Type}
  [inst : DecidableEq.{1} Token] [inst_1 : DecidableEq.{1} Module] [inst_2 : DecidableEq.{1} Parse]
  [inst_3 : DecidableEq.{1} Green] (s : YulangClosure.NativeCallbackCoordinatesR33.HirSnapshot Token Module Parse Green)
  (q : YulangClosure.NativeCallbackCoordinatesR33.OperationCoordinate Token)
  (effect : YulangClosure.NativeCallbackCoordinatesR33.HirEffect Module Parse Green),
  Eq.{1} (getElem?.{0, 0, 0} s.effects q.family.effectIndex) (some.{0} effect) →
    LE.le.{0} (List.length.{0} effect.operations) q.operationIndex →
      Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.decodeOperationCoordinate s q) none.{0} :=
⋯
'YulangClosure.NativeCallbackCoordinatesR33.operation_out_of_range' depends on axioms: [propext]
theorem YulangClosure.NativeCallbackCoordinatesR33.operation_wrong_family : ∀ {Token Module Parse Green : Type}
  [inst : DecidableEq.{1} Token] [inst_1 : DecidableEq.{1} Module] [inst_2 : DecidableEq.{1} Parse]
  [inst_3 : DecidableEq.{1} Green] (s : YulangClosure.NativeCallbackCoordinatesR33.HirSnapshot Token Module Parse Green)
  (q : YulangClosure.NativeCallbackCoordinatesR33.OperationCoordinate Token)
  (effect : YulangClosure.NativeCallbackCoordinatesR33.HirEffect Module Parse Green)
  (operation : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green),
  Eq.{1} (getElem?.{0, 0, 0} s.effects q.family.effectIndex) (some.{0} effect) →
    Eq.{1} (getElem?.{0, 0, 0} effect.operations q.operationIndex) (some.{0} operation) →
      Ne.{1} operation.family effect.identity →
        Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.decodeOperationCoordinate s q) none.{0} :=
⋯
'YulangClosure.NativeCallbackCoordinatesR33.operation_wrong_family' depends on axioms: [propext]
theorem YulangClosure.NativeCallbackCoordinatesR33.family_decode_exact : ∀ {Token Module Parse Green : Type}
  [inst : DecidableEq.{1} Token] (s : YulangClosure.NativeCallbackCoordinatesR33.HirSnapshot Token Module Parse Green)
  (q : YulangClosure.NativeCallbackCoordinatesR33.FamilyCoordinate Token)
  {family : YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green},
  Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.decodeFamilyCoordinate s q) (some.{0} family) →
    Eq.{1} q.snapshotToken s.token ∧
      Exists.{1} fun effect =>
        Eq.{1} (getElem?.{0, 0, 0} s.effects q.effectIndex) (some.{0} effect) ∧ Eq.{1} family effect.identity :=
⋯
'YulangClosure.NativeCallbackCoordinatesR33.family_decode_exact' depends on axioms: [propext]
theorem YulangClosure.NativeCallbackCoordinatesR33.family_decode_bounded : ∀ {Token Module Parse Green : Type}
  [inst : DecidableEq.{1} Token] (s : YulangClosure.NativeCallbackCoordinatesR33.HirSnapshot Token Module Parse Green)
  (q : YulangClosure.NativeCallbackCoordinatesR33.FamilyCoordinate Token)
  {family : YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green},
  Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.decodeFamilyCoordinate s q) (some.{0} family) →
    Eq.{1} q.snapshotToken s.token ∧
      Exists.{0} fun bound => Eq.{1} family (getElem.{0, 0, 0} s.effects q.effectIndex bound).identity :=
⋯
'YulangClosure.NativeCallbackCoordinatesR33.family_decode_bounded' depends on axioms: [propext]
theorem YulangClosure.NativeCallbackCoordinatesR33.operation_decode_exact : ∀ {Token Module Parse Green : Type}
  [inst : DecidableEq.{1} Token] [inst_1 : DecidableEq.{1} Module] [inst_2 : DecidableEq.{1} Parse]
  [inst_3 : DecidableEq.{1} Green] (s : YulangClosure.NativeCallbackCoordinatesR33.HirSnapshot Token Module Parse Green)
  (q : YulangClosure.NativeCallbackCoordinatesR33.OperationCoordinate Token)
  {operation : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green},
  Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.decodeOperationCoordinate s q) (some.{0} operation) →
    Eq.{1} q.family.snapshotToken s.token ∧
      Exists.{1} fun effect =>
        Eq.{1} (getElem?.{0, 0, 0} s.effects q.family.effectIndex) (some.{0} effect) ∧
          Eq.{1} (getElem?.{0, 0, 0} effect.operations q.operationIndex) (some.{0} operation) ∧
            Eq.{1} operation.family effect.identity :=
⋯
'YulangClosure.NativeCallbackCoordinatesR33.operation_decode_exact' depends on axioms: [propext, sorryAx.{u}]
theorem YulangClosure.NativeCallbackCoordinatesR33.operation_decode_bounded : ∀ {Token Module Parse Green : Type}
  [inst : DecidableEq.{1} Token] [inst_1 : DecidableEq.{1} Module] [inst_2 : DecidableEq.{1} Parse]
  [inst_3 : DecidableEq.{1} Green] (s : YulangClosure.NativeCallbackCoordinatesR33.HirSnapshot Token Module Parse Green)
  (q : YulangClosure.NativeCallbackCoordinatesR33.OperationCoordinate Token)
  {operation : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green},
  Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.decodeOperationCoordinate s q) (some.{0} operation) →
    Eq.{1} q.family.snapshotToken s.token ∧
      Exists.{1} fun effect =>
        (Exists.{0} fun bound => Eq.{1} (getElem.{0, 0, 0} s.effects q.family.effectIndex bound) effect) ∧
          (Exists.{0} fun bound => Eq.{1} (getElem.{0, 0, 0} effect.operations q.operationIndex bound) operation) ∧
            Eq.{1} operation.family effect.identity :=
⋯
'YulangClosure.NativeCallbackCoordinatesR33.operation_decode_bounded' depends on axioms: [propext, sorryAx.{u}]
theorem YulangClosure.NativeCallbackCoordinatesR33.operation_family_decode : ∀ {Token Module Parse Green : Type}
  [inst : DecidableEq.{1} Token] [inst_1 : DecidableEq.{1} Module] [inst_2 : DecidableEq.{1} Parse]
  [inst_3 : DecidableEq.{1} Green] (s : YulangClosure.NativeCallbackCoordinatesR33.HirSnapshot Token Module Parse Green)
  (q : YulangClosure.NativeCallbackCoordinatesR33.OperationCoordinate Token)
  {operation : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green},
  Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.decodeOperationCoordinate s q) (some.{0} operation) →
    Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.decodeFamilyCoordinate s q.family) (some.{0} operation.family) :=
⋯
'YulangClosure.NativeCallbackCoordinatesR33.operation_family_decode' depends on axioms: [propext, sorryAx.{u}]
theorem YulangClosure.NativeCallbackCoordinatesR33.row_decode_length : ∀ {Token Module Parse Green : Type}
  [inst : DecidableEq.{1} Token] (s : YulangClosure.NativeCallbackCoordinatesR33.HirSnapshot Token Module Parse Green)
  (coordinates : List.{0} (YulangClosure.NativeCallbackCoordinatesR33.FamilyCoordinate Token))
  {families : List.{0} (YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green)},
  Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.decodeFamilyRow s coordinates) (some.{0} families) →
    Eq.{1} (List.length.{0} families) (List.length.{0} coordinates) :=
⋯
'YulangClosure.NativeCallbackCoordinatesR33.row_decode_length' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.NativeCallbackCoordinatesR33.row_bad_member_rejected : ∀ {Token Module Parse Green : Type}
  [inst : DecidableEq.{1} Token] (s : YulangClosure.NativeCallbackCoordinatesR33.HirSnapshot Token Module Parse Green)
  (coordinates : List.{0} (YulangClosure.NativeCallbackCoordinatesR33.FamilyCoordinate Token))
  {bad : YulangClosure.NativeCallbackCoordinatesR33.FamilyCoordinate Token},
  Membership.mem.{0, 0} coordinates bad →
    Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.decodeFamilyCoordinate s bad) none.{0} →
      Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.decodeFamilyRow s coordinates) none.{0} :=
⋯
'YulangClosure.NativeCallbackCoordinatesR33.row_bad_member_rejected' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.NativeCallbackCoordinatesR33.permission_row_exact : ∀ {Token Module Parse Green : Type}
  [inst : DecidableEq.{1} Token] [inst_1 : DecidableEq.{1} Module] [inst_2 : DecidableEq.{1} Parse]
  [inst_3 : DecidableEq.{1} Green] (s : YulangClosure.NativeCallbackCoordinatesR33.HirSnapshot Token Module Parse Green)
  (coordinates : List.{0} (YulangClosure.NativeCallbackCoordinatesR33.FamilyCoordinate Token))
  {families : List.{0} (YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green)},
  Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.translatePermissionRow s coordinates) (some.{0} families) →
    Eq.{1} families s.permissionRow ∧
      Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.decodeFamilyRow s coordinates) (some.{0} families) ∧
        Eq.{1} (List.length.{0} families) (List.length.{0} coordinates) :=
⋯
'YulangClosure.NativeCallbackCoordinatesR33.permission_row_exact' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.NativeCallbackCoordinatesR33.incomplete_row_rejected : ∀ {Token Module Parse Green : Type}
  [inst : DecidableEq.{1} Token] [inst_1 : DecidableEq.{1} Module] [inst_2 : DecidableEq.{1} Parse]
  [inst_3 : DecidableEq.{1} Green] (s : YulangClosure.NativeCallbackCoordinatesR33.HirSnapshot Token Module Parse Green)
  (coordinates : List.{0} (YulangClosure.NativeCallbackCoordinatesR33.FamilyCoordinate Token))
  (families : List.{0} (YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green)),
  Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.decodeFamilyRow s coordinates) (some.{0} families) →
    Ne.{1} families s.permissionRow →
      Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.translatePermissionRow s coordinates) none.{0} :=
⋯
'YulangClosure.NativeCallbackCoordinatesR33.incomplete_row_rejected' depends on axioms: [propext]
theorem YulangClosure.NativeCallbackCoordinatesR33.bad_row_rejected : ∀ {Token Module Parse Green : Type}
  [inst : DecidableEq.{1} Token] [inst_1 : DecidableEq.{1} Module] [inst_2 : DecidableEq.{1} Parse]
  [inst_3 : DecidableEq.{1} Green] (s : YulangClosure.NativeCallbackCoordinatesR33.HirSnapshot Token Module Parse Green)
  (coordinates : List.{0} (YulangClosure.NativeCallbackCoordinatesR33.FamilyCoordinate Token)),
  Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.decodeFamilyRow s coordinates) none.{0} →
    Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.translatePermissionRow s coordinates) none.{0} :=
⋯
'YulangClosure.NativeCallbackCoordinatesR33.bad_row_rejected' depends on axioms: [propext]
theorem YulangClosure.NativeCallbackCoordinatesR33.translation_exact : ∀ {Token Module Parse Green : Type}
  [inst : DecidableEq.{1} Token] [inst_1 : DecidableEq.{1} Module] [inst_2 : DecidableEq.{1} Parse]
  [inst_3 : DecidableEq.{1} Green] (s : YulangClosure.NativeCallbackCoordinatesR33.HirSnapshot Token Module Parse Green)
  (request consumer arm : YulangClosure.NativeCallbackCoordinatesR33.OperationCoordinate Token)
  (row : List.{0} (YulangClosure.NativeCallbackCoordinatesR33.FamilyCoordinate Token))
  {out : YulangClosure.NativeCallbackCoordinatesR33.DecodedCoordinates Module Parse Green},
  Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.translateCoordinates s request consumer arm row) (some.{0} out) →
    Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.decodeOperationCoordinate s request) (some.{0} out.request) ∧
      Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.decodeOperationCoordinate s consumer) (some.{0} out.consumer) ∧
        Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.decodeOperationCoordinate s arm) (some.{0} out.arm) ∧
          Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.translatePermissionRow s row) (some.{0} out.families) :=
⋯
'YulangClosure.NativeCallbackCoordinatesR33.translation_exact' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.NativeCallbackCoordinatesR33.translation_to_r32 : ∀ {Token Module Parse Green : Type}
  [inst : DecidableEq.{1} Token] [inst_1 : DecidableEq.{1} Module] [inst_2 : DecidableEq.{1} Parse]
  [inst_3 : DecidableEq.{1} Green] (s : YulangClosure.NativeCallbackCoordinatesR33.HirSnapshot Token Module Parse Green)
  (request consumer arm : YulangClosure.NativeCallbackCoordinatesR33.OperationCoordinate Token)
  (row : List.{0} (YulangClosure.NativeCallbackCoordinatesR33.FamilyCoordinate Token))
  {out : YulangClosure.NativeCallbackCoordinatesR33.DecodedCoordinates Module Parse Green},
  Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.translateCoordinates s request consumer arm row) (some.{0} out) →
    have table :=
      YulangClosure.NativeCallbackGrantBridgeR32.coveringTable out.request out.consumer out.arm out.families;
    Eq.{1} out.families s.permissionRow ∧
      Eq.{1} (List.length.{0} out.families) (List.length.{0} row) ∧
        Eq.{1} request.family.snapshotToken s.token ∧
          Eq.{1} consumer.family.snapshotToken s.token ∧
            Eq.{1} arm.family.snapshotToken s.token ∧
              (Exists.{1} fun effect =>
                  Membership.mem.{0, 0} s.effects effect ∧
                    Membership.mem.{0, 0} effect.operations out.request ∧ Eq.{1} out.request.family effect.identity) ∧
                (Exists.{1} fun effect =>
                    Membership.mem.{0, 0} s.effects effect ∧
                      Membership.mem.{0, 0} effect.operations out.consumer ∧
                        Eq.{1} out.consumer.family effect.identity) ∧
                  (Exists.{1} fun effect =>
                      Membership.mem.{0, 0} s.effects effect ∧
                        Membership.mem.{0, 0} effect.operations out.arm ∧ Eq.{1} out.arm.family effect.identity) ∧
                    (∀ (op : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green),
                        Membership.mem.{0, 0}
                            (List.cons.{0} out.request
                              (List.cons.{0} out.consumer (List.cons.{0} out.arm List.nil.{0})))
                            op →
                          Membership.mem.{0, 0} table.operations op) ∧
                      (∀ (family : YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green),
                          Membership.mem.{0, 0} s.permissionRow family → Membership.mem.{0, 0} table.families family) ∧
                        Eq.{1}
                            (YulangClosure.NativeCallbackGrantBridgeR31.decodeOperation table
                              (YulangClosure.NativeCallbackGrantBridgeR31.operationKey table out.request))
                            (some.{0} out.request) ∧
                          Eq.{1}
                              (YulangClosure.NativeCallbackGrantBridgeR31.decodeOperation table
                                (YulangClosure.NativeCallbackGrantBridgeR31.operationKey table out.consumer))
                              (some.{0} out.consumer) ∧
                            Eq.{1}
                                (YulangClosure.NativeCallbackGrantBridgeR31.decodeOperation table
                                  (YulangClosure.NativeCallbackGrantBridgeR31.operationKey table out.arm))
                                (some.{0} out.arm) ∧
                              ∀ (family : YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green),
                                Membership.mem.{0, 0} s.permissionRow family →
                                  Eq.{1} (getElem?.{0, 0, 0} table.families (List.idxOf.{0} family table.families))
                                      (some.{0} family) ∧
                                    (Membership.mem.{0, 0}
                                        (List.map.{0, 0} (fun a => List.idxOf.{0} a table.families) out.families)
                                        (List.idxOf.{0} family table.families) ↔
                                      Membership.mem.{0, 0} out.families family) :=
⋯
'YulangClosure.NativeCallbackCoordinatesR33.translation_to_r32' depends on axioms: [propext,
 sorryAx.{u},
 Quot.sound.{u}]

STDERR:
```

## Audit attempt 3

Same pinned read-only bwrap command and all 59 theorem names; exact nested-operation lookup proof repaired. Exit 0; measured subprocess seconds 3.0580294230021536.

```text
theorem YulangClosure.CallbackHygieneCorrespondence.checked_use_inversion : ∀
  {e : YulangClosure.CallbackHygieneCorrespondence.Entry} {n : YulangClosure.CallbackHygieneCorrespondence.NameRead}
  {u out : YulangClosure.CallbackHygieneCorrespondence.CallbackUse},
  Eq.{1} (YulangClosure.CallbackHygieneCorrespondence.checkedUse e n u) (some.{0} out) →
    Eq.{1} out u ∧ YulangClosure.CallbackHygieneCorrespondence.UseReady e n u :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.checked_use_inversion' does not depend on any axioms
theorem YulangClosure.CallbackHygieneCorrespondence.checked_catch_inversion : ∀
  {s : YulangClosure.CallbackHygieneCorrespondence.State} {r : YulangClosure.CallbackHygieneCorrespondence.Request}
  {c : YulangClosure.CallbackHygieneCorrespondence.Consumer}
  {p : YulangClosure.CallbackHygieneCorrespondence.Permission}
  {x : YulangClosure.CallbackHygieneCorrespondence.Selection},
  Eq.{1} (YulangClosure.CallbackHygieneCorrespondence.checkedCatch s r c p) (some.{0} x) →
    Eq.{1} x { request := r, consumer := c, permission := p } ∧
      YulangClosure.CallbackHygieneCorrespondence.CatchReady s r c p :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.checked_catch_inversion' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.CallbackHygieneCorrespondence.checked_catch_installed_arm : ∀
  {s : YulangClosure.CallbackHygieneCorrespondence.State} {r : YulangClosure.CallbackHygieneCorrespondence.Request}
  {c : YulangClosure.CallbackHygieneCorrespondence.Consumer}
  {p : YulangClosure.CallbackHygieneCorrespondence.Permission}
  {x : YulangClosure.CallbackHygieneCorrespondence.Selection},
  Eq.{1} (YulangClosure.CallbackHygieneCorrespondence.checkedCatch s r c p) (some.{0} x) →
    Exists.{1} fun h =>
      Membership.mem.{0, 0} s.installed h ∧
        Eq.{1} c.handler h.handle ∧
          Eq.{1} c.catchSite h.site ∧
            Eq.{1} c.owner h.owner ∧
              Exists.{1} fun a =>
                Membership.mem.{0, 0} h.arms a ∧
                  Eq.{1} c.arm a.handle ∧ Eq.{1} c.armSite a.site ∧ Eq.{1} c.operation a.operation :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.checked_catch_installed_arm' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.CallbackHygieneCorrespondence.checked_catch_port : ∀
  {s : YulangClosure.CallbackHygieneCorrespondence.State} {r : YulangClosure.CallbackHygieneCorrespondence.Request}
  {c : YulangClosure.CallbackHygieneCorrespondence.Consumer}
  {p : YulangClosure.CallbackHygieneCorrespondence.Permission}
  {x : YulangClosure.CallbackHygieneCorrespondence.Selection},
  Eq.{1} (YulangClosure.CallbackHygieneCorrespondence.checkedCatch s r c p) (some.{0} x) →
    YulangClosure.CallbackHygieneCorrespondence.PortReady s r p :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.checked_catch_port' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.CallbackHygieneCorrespondence.permission_preserves_actual : ∀
  (s : YulangClosure.CallbackHygieneCorrespondence.State) (a : YulangClosure.CallbackHygieneCorrespondence.Annotation),
  Eq.{1}
      { annotations := List.cons.{0} a s.annotations, permissions := s.permissions, installed := s.installed,
          active := s.active, invocations := s.invocations, entries := s.entries, names := s.names, uses := s.uses,
          executions := s.executions, executing := s.executing, emitted := s.emitted, pending := s.pending,
          selections := s.selections, initializing := s.initializing, lifetime := s.lifetime, nextEvent := s.nextEvent,
          nextInvocation := s.nextInvocation }.emitted
      s.emitted ∧
    Eq.{1}
      { annotations := List.cons.{0} a s.annotations, permissions := s.permissions, installed := s.installed,
          active := s.active, invocations := s.invocations, entries := s.entries, names := s.names, uses := s.uses,
          executions := s.executions, executing := s.executing, emitted := s.emitted, pending := s.pending,
          selections := s.selections, initializing := s.initializing, lifetime := s.lifetime, nextEvent := s.nextEvent,
          nextInvocation := s.nextInvocation }.pending
      s.pending :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.permission_preserves_actual' does not depend on any axioms
theorem YulangClosure.CallbackHygieneCorrespondence.emit_conserved : ∀
  {s : YulangClosure.CallbackHygieneCorrespondence.State},
  YulangClosure.CallbackHygieneCorrespondence.Conserved s →
    ∀ (r : YulangClosure.CallbackHygieneCorrespondence.Request),
      YulangClosure.CallbackHygieneCorrespondence.Conserved (YulangClosure.CallbackHygieneCorrespondence.emit s r) :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.emit_conserved' depends on axioms: [propext]
theorem YulangClosure.CallbackHygieneCorrespondence.commit_conserved : ∀
  {s : YulangClosure.CallbackHygieneCorrespondence.State},
  YulangClosure.CallbackHygieneCorrespondence.Conserved s →
    ∀ {r : YulangClosure.CallbackHygieneCorrespondence.Request}
      {c : YulangClosure.CallbackHygieneCorrespondence.Consumer}
      {p : YulangClosure.CallbackHygieneCorrespondence.Permission}
      {x : YulangClosure.CallbackHygieneCorrespondence.Selection},
      Eq.{1} (YulangClosure.CallbackHygieneCorrespondence.checkedCatch s r c p) (some.{0} x) →
        YulangClosure.CallbackHygieneCorrespondence.Conserved
          (YulangClosure.CallbackHygieneCorrespondence.commit s x) :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.commit_conserved' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.CallbackHygieneCorrespondence.step_conserved : ∀
  {before after : YulangClosure.CallbackHygieneCorrespondence.State},
  YulangClosure.CallbackHygieneCorrespondence.Step before after →
    YulangClosure.CallbackHygieneCorrespondence.Conserved before →
      YulangClosure.CallbackHygieneCorrespondence.Conserved after :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.step_conserved' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.CallbackHygieneCorrespondence.history_conserved : ∀
  {initial final : YulangClosure.CallbackHygieneCorrespondence.State},
  YulangClosure.CallbackHygieneCorrespondence.History initial final →
    YulangClosure.CallbackHygieneCorrespondence.Conserved initial →
      YulangClosure.CallbackHygieneCorrespondence.Conserved final :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.history_conserved' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.CallbackHygieneCorrespondence.empty_conserved : YulangClosure.CallbackHygieneCorrespondence.Conserved
  { } :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.empty_conserved' does not depend on any axioms
theorem YulangClosure.CallbackHygieneCorrespondence.emit_events_before : ∀
  {s : YulangClosure.CallbackHygieneCorrespondence.State},
  YulangClosure.CallbackHygieneCorrespondence.EventsBefore s →
    ∀ (r : YulangClosure.CallbackHygieneCorrespondence.Request),
      YulangClosure.CallbackHygieneCorrespondence.EventsBefore (YulangClosure.CallbackHygieneCorrespondence.emit s r) :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.emit_events_before' depends on axioms: [propext]
theorem YulangClosure.CallbackHygieneCorrespondence.step_events_before : ∀
  {before after : YulangClosure.CallbackHygieneCorrespondence.State},
  YulangClosure.CallbackHygieneCorrespondence.Step before after →
    YulangClosure.CallbackHygieneCorrespondence.EventsBefore before →
      YulangClosure.CallbackHygieneCorrespondence.EventsBefore after :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.step_events_before' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.CallbackHygieneCorrespondence.generated_events_before : ∀
  {final : YulangClosure.CallbackHygieneCorrespondence.State},
  YulangClosure.CallbackHygieneCorrespondence.History { } final →
    YulangClosure.CallbackHygieneCorrespondence.EventsBefore final :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.generated_events_before' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.CallbackHygieneCorrespondence.generated_selection_actual : ∀
  {final : YulangClosure.CallbackHygieneCorrespondence.State},
  YulangClosure.CallbackHygieneCorrespondence.History { } final →
    ∀ {x : YulangClosure.CallbackHygieneCorrespondence.Selection},
      Membership.mem.{0, 0} final.selections x →
        Membership.mem.{0, 0} final.emitted x.request ∧
          Eq.{1} x.consumer.operation x.request.operation ∧
            Eq.{1} x.consumer.event x.request.event ∧
              Eq.{1} x.consumer.payload x.request.payload ∧
                Eq.{1} x.consumer.owner x.permission.owner ∧
                  Membership.mem.{0, 0} x.permission.families x.request.operation.family :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.generated_selection_actual' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.CallbackHygieneCorrespondence.empty_inflow_rejected : ∀
  (s : YulangClosure.CallbackHygieneCorrespondence.State) (r : YulangClosure.CallbackHygieneCorrespondence.Request)
  (c : YulangClosure.CallbackHygieneCorrespondence.Consumer)
  (p : YulangClosure.CallbackHygieneCorrespondence.Permission),
  Eq.{1} s.pending List.nil.{0} → Eq.{1} (YulangClosure.CallbackHygieneCorrespondence.checkedCatch s r c p) none.{0} :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.empty_inflow_rejected' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.CallbackHygieneCorrespondence.companion_event_fresh : ∀
  {s : YulangClosure.CallbackHygieneCorrespondence.State},
  YulangClosure.CallbackHygieneCorrespondence.History { } s →
    ∀ {inner : YulangClosure.CallbackHygieneCorrespondence.Selection},
      Membership.mem.{0, 0} s.selections inner →
        ∀ (r : YulangClosure.CallbackHygieneCorrespondence.Request),
          Ne.{1} (YulangClosure.CallbackHygieneCorrespondence.minted s r).event inner.request.event :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.companion_event_fresh' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.CallbackHygieneCorrespondence.commit_preserves_other_event : ∀
  (s : YulangClosure.CallbackHygieneCorrespondence.State) (x : YulangClosure.CallbackHygieneCorrespondence.Selection)
  (write : YulangClosure.CallbackHygieneCorrespondence.Request),
  Membership.mem.{0, 0} s.pending write →
    Ne.{1} write.event x.request.event →
      Membership.mem.{0, 0} (YulangClosure.CallbackHygieneCorrespondence.commit s x).pending write :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.commit_preserves_other_event' depends on axioms: [propext]
theorem YulangClosure.CallbackHygieneCorrespondence.commit_removes_selected_event : ∀
  (s : YulangClosure.CallbackHygieneCorrespondence.State) (x : YulangClosure.CallbackHygieneCorrespondence.Selection)
  (r : YulangClosure.CallbackHygieneCorrespondence.Request),
  Membership.mem.{0, 0} (YulangClosure.CallbackHygieneCorrespondence.commit s x).pending r →
    Ne.{1} r.event x.request.event :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.commit_removes_selected_event' depends on axioms: [propext]
theorem YulangClosure.CallbackHygieneCorrespondence.companion_emit_actual : ∀
  (s : YulangClosure.CallbackHygieneCorrespondence.State) (r : YulangClosure.CallbackHygieneCorrespondence.Request),
  Membership.mem.{0, 0} (YulangClosure.CallbackHygieneCorrespondence.emit s r).emitted
      (YulangClosure.CallbackHygieneCorrespondence.minted s r) ∧
    Membership.mem.{0, 0} (YulangClosure.CallbackHygieneCorrespondence.emit s r).pending
        (YulangClosure.CallbackHygieneCorrespondence.minted s r) ∧
      Eq.{1} (YulangClosure.CallbackHygieneCorrespondence.minted s r).operation r.operation ∧
        Eq.{1} (YulangClosure.CallbackHygieneCorrespondence.minted s r).payload r.payload ∧
          Eq.{1} (YulangClosure.CallbackHygieneCorrespondence.minted s r).lineage r.lineage :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.companion_emit_actual' does not depend on any axioms
theorem YulangClosure.CallbackHygieneCorrespondence.shallow_discard_preserves_contributions : ∀
  (s : YulangClosure.CallbackHygieneCorrespondence.State)
  (cells :
    List.{0} (YulangClosure.CallbackHygieneCorrespondence.Id YulangClosure.CallbackHygieneCorrespondence.Kind.cell)),
  Eq.{1}
      { annotations := s.annotations, permissions := s.permissions, installed := s.installed, active := s.active,
          invocations := s.invocations, entries := s.entries, names := s.names, uses := s.uses,
          executions := s.executions, executing := s.executing, emitted := s.emitted, pending := s.pending,
          selections := s.selections,
          initializing := List.filter.{0} (fun cell => decide ¬Membership.mem.{0, 0} cells cell) s.initializing,
          lifetime :=
            List.cons.{0} (YulangClosure.CallbackHygieneCorrespondence.Lifetime.shallowDiscard cells) s.lifetime,
          nextEvent := s.nextEvent, nextInvocation := s.nextInvocation }.pending
      s.pending ∧
    Eq.{1}
        { annotations := s.annotations, permissions := s.permissions, installed := s.installed, active := s.active,
            invocations := s.invocations, entries := s.entries, names := s.names, uses := s.uses,
            executions := s.executions, executing := s.executing, emitted := s.emitted, pending := s.pending,
            selections := s.selections,
            initializing := List.filter.{0} (fun cell => decide ¬Membership.mem.{0, 0} cells cell) s.initializing,
            lifetime :=
              List.cons.{0} (YulangClosure.CallbackHygieneCorrespondence.Lifetime.shallowDiscard cells) s.lifetime,
            nextEvent := s.nextEvent, nextInvocation := s.nextInvocation }.emitted
        s.emitted ∧
      Eq.{1}
        { annotations := s.annotations, permissions := s.permissions, installed := s.installed, active := s.active,
            invocations := s.invocations, entries := s.entries, names := s.names, uses := s.uses,
            executions := s.executions, executing := s.executing, emitted := s.emitted, pending := s.pending,
            selections := s.selections,
            initializing := List.filter.{0} (fun cell => decide ¬Membership.mem.{0, 0} cells cell) s.initializing,
            lifetime :=
              List.cons.{0} (YulangClosure.CallbackHygieneCorrespondence.Lifetime.shallowDiscard cells) s.lifetime,
            nextEvent := s.nextEvent, nextInvocation := s.nextInvocation }.active
        s.active :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.shallow_discard_preserves_contributions' depends on axioms: [propext]
theorem YulangClosure.CallbackHygieneCorrespondence.normal_return_deactivates : ∀
  (s : YulangClosure.CallbackHygieneCorrespondence.State)
  (owner : YulangClosure.CallbackHygieneCorrespondence.Id YulangClosure.CallbackHygieneCorrespondence.Kind.invocation),
  ¬Membership.mem.{0, 0}
      { annotations := s.annotations, permissions := s.permissions, installed := s.installed,
          active := List.filter.{0} (fun current => decide (Ne.{1} current owner)) s.active,
          invocations := s.invocations, entries := s.entries, names := s.names, uses := s.uses,
          executions := s.executions, executing := s.executing, emitted := s.emitted, pending := s.pending,
          selections := s.selections, initializing := s.initializing,
          lifetime :=
            List.cons.{0} (YulangClosure.CallbackHygieneCorrespondence.Lifetime.normalReturn owner) s.lifetime,
          nextEvent := s.nextEvent, nextInvocation := s.nextInvocation }.active
      owner :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.normal_return_deactivates' depends on axioms: [propext]
theorem YulangClosure.CallbackHygieneCorrespondence.lifetime_branches_distinct : ∀
  (owner : YulangClosure.CallbackHygieneCorrespondence.Id YulangClosure.CallbackHygieneCorrespondence.Kind.invocation)
  (cells :
    List.{0} (YulangClosure.CallbackHygieneCorrespondence.Id YulangClosure.CallbackHygieneCorrespondence.Kind.cell)),
  Ne.{1} (YulangClosure.CallbackHygieneCorrespondence.Lifetime.normalReturn owner)
    (YulangClosure.CallbackHygieneCorrespondence.Lifetime.shallowDiscard cells) :=
⋯
'YulangClosure.CallbackHygieneCorrespondence.lifetime_branches_distinct' does not depend on any axioms
theorem YulangClosure.NativeCallbackGrantBridgeR31.finite_index_round_trip : ∀ {α : Type} [inst : DecidableEq.{1} α]
  (table : List.{0} α) (a : α),
  Membership.mem.{0, 0} table a → Eq.{1} (getElem?.{0, 0, 0} table (List.idxOf.{0} a table)) (some.{0} a) :=
⋯
'YulangClosure.NativeCallbackGrantBridgeR31.finite_index_round_trip' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.NativeCallbackGrantBridgeR31.finite_index_injective : ∀ {α : Type} [inst : DecidableEq.{1} α]
  (table : List.{0} α) {a b : α},
  Membership.mem.{0, 0} table a →
    Membership.mem.{0, 0} table b → Eq.{1} (List.idxOf.{0} a table) (List.idxOf.{0} b table) → Eq.{1} a b :=
⋯
'YulangClosure.NativeCallbackGrantBridgeR31.finite_index_injective' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.NativeCallbackGrantBridgeR31.operation_round_trip : ∀ {Module Parse Green : Type}
  [inst : DecidableEq.{1} Module] [inst_1 : DecidableEq.{1} Parse] [inst_2 : DecidableEq.{1} Green]
  (table : YulangClosure.NativeCallbackGrantBridgeR31.IdentityTable Module Parse Green)
  (operation : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green),
  Membership.mem.{0, 0} table.operations operation →
    Membership.mem.{0, 0} table.families operation.family →
      Eq.{1}
        (YulangClosure.NativeCallbackGrantBridgeR31.decodeOperation table
          (YulangClosure.NativeCallbackGrantBridgeR31.operationKey table operation))
        (some.{0} operation) :=
⋯
'YulangClosure.NativeCallbackGrantBridgeR31.operation_round_trip' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.NativeCallbackGrantBridgeR31.operationKey_injective : ∀ {Module Parse Green : Type}
  [inst : DecidableEq.{1} Module] [inst_1 : DecidableEq.{1} Parse] [inst_2 : DecidableEq.{1} Green]
  (table : YulangClosure.NativeCallbackGrantBridgeR31.IdentityTable Module Parse Green)
  {a b : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green},
  Membership.mem.{0, 0} table.operations a →
    Membership.mem.{0, 0} table.operations b →
      Eq.{1} (YulangClosure.NativeCallbackGrantBridgeR31.operationKey table a)
          (YulangClosure.NativeCallbackGrantBridgeR31.operationKey table b) →
        Eq.{1} a b :=
⋯
'YulangClosure.NativeCallbackGrantBridgeR31.operationKey_injective' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.NativeCallbackGrantBridgeR31.encoded_family_member : ∀ {Module Parse Green : Type}
  [inst : DecidableEq.{1} Module] [inst_1 : DecidableEq.{1} Parse] [inst_2 : DecidableEq.{1} Green]
  (table : YulangClosure.NativeCallbackGrantBridgeR31.IdentityTable Module Parse Green)
  {family : YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green}
  {row : List.{0} (YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green)},
  Membership.mem.{0, 0} row family →
    Membership.mem.{0, 0} (List.map.{0, 0} (fun a => List.idxOf.{0} a table.families) row)
      (List.idxOf.{0} family table.families) :=
⋯
'YulangClosure.NativeCallbackGrantBridgeR31.encoded_family_member' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.NativeCallbackGrantBridgeR31.encoded_family_member_iff : ∀ {Module Parse Green : Type}
  [inst : DecidableEq.{1} Module] [inst_1 : DecidableEq.{1} Parse] [inst_2 : DecidableEq.{1} Green]
  (table : YulangClosure.NativeCallbackGrantBridgeR31.IdentityTable Module Parse Green)
  {family : YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green}
  {row : List.{0} (YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green)},
  (∀ (f : YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green),
      Membership.mem.{0, 0} row f → Membership.mem.{0, 0} table.families f) →
    Membership.mem.{0, 0} table.families family →
      (Membership.mem.{0, 0} (List.map.{0, 0} (fun a => List.idxOf.{0} a table.families) row)
          (List.idxOf.{0} family table.families) ↔
        Membership.mem.{0, 0} row family) :=
⋯
'YulangClosure.NativeCallbackGrantBridgeR31.encoded_family_member_iff' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.NativeCallbackGrantBridgeR31.callback_use_ready : ∀
  (e : YulangClosure.CallbackHygieneCorrespondence.Entry) (n : YulangClosure.CallbackHygieneCorrespondence.NameRead)
  (u : YulangClosure.CallbackHygieneCorrespondence.CallbackUse),
  Eq.{1} e.permission.port YulangClosure.CallbackHygieneCorrespondence.Port.callbackResult →
    Eq.{1} e.formalReceipt.owner e.permission.owner →
      Eq.{1} e.formalReceipt.view e.view →
        Eq.{1} e.formalReceipt.site e.permission.lambdaSite →
          Eq.{1} e.formalReceipt.formal (some.{0} e.permission.formal) →
            Eq.{1} n.entry e.handle →
              Eq.{1} n.formal e.permission.formal →
                Eq.{1} n.receipt.owner e.permission.owner →
                  Eq.{1} n.receipt.view e.view →
                    Eq.{1} n.receipt.site n.site →
                      Eq.{1} n.receipt.formal none.{0} →
                        Eq.{1} u.entry e.handle →
                          Eq.{1} u.owner e.permission.owner →
                            Eq.{1} u.sourceView e.view →
                              Eq.{1} u.formalReceipt e.formalReceipt.handle →
                                Eq.{1} u.nameReceipt n.receipt.handle →
                                  Eq.{1} u.callee n.site →
                                    Eq.{1} u.resultReceipt.owner u.owner →
                                      Eq.{1} u.resultReceipt.view u.resultView →
                                        Eq.{1} u.resultReceipt.site u.applySite →
                                          Eq.{1} u.resultReceipt.formal none.{0} →
                                            YulangClosure.CallbackHygieneCorrespondence.UseReady e n u :=
⋯
'YulangClosure.NativeCallbackGrantBridgeR31.callback_use_ready' does not depend on any axioms
theorem YulangClosure.NativeCallbackGrantBridgeR31.callback_checked_catch : ∀ {Module Parse Green : Type}
  [inst : DecidableEq.{1} Module] [inst_1 : DecidableEq.{1} Parse] [inst_2 : DecidableEq.{1} Green]
  (table : YulangClosure.NativeCallbackGrantBridgeR31.IdentityTable Module Parse Green)
  (r : YulangClosure.NativeCallbackGrantBridgeR31.NativeRequest Module Parse Green)
  (c : YulangClosure.NativeCallbackGrantBridgeR31.NativeConsumer Module Parse Green)
  (a : YulangClosure.NativeCallbackGrantBridgeR31.NativeArm Module Parse Green)
  (e : YulangClosure.CallbackHygieneCorrespondence.Entry) (n : YulangClosure.CallbackHygieneCorrespondence.NameRead)
  (u : YulangClosure.CallbackHygieneCorrespondence.CallbackUse)
  (x : YulangClosure.CallbackHygieneCorrespondence.Execution)
  (active :
    List.{0}
      (YulangClosure.CallbackHygieneCorrespondence.Id YulangClosure.CallbackHygieneCorrespondence.Kind.invocation))
  (installation : YulangClosure.CallbackHygieneCorrespondence.InstalledCatch)
  (families : List.{0} (YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green)),
  YulangClosure.CallbackHygieneCorrespondence.UseReady e n u →
    Eq.{1} x.useHandle u.handle →
      Eq.{1} x.view u.resultView →
        Eq.{1} x.receipt u.resultReceipt.handle →
          Eq.{1} r.coordinates.origin (YulangClosure.CallbackHygieneCorrespondence.Origin.callback x) →
            Eq.{1} e.permission.families (List.map.{0, 0} (fun a => List.idxOf.{0} a table.families) families) →
              Membership.mem.{0, 0} families r.operation.family →
                Membership.mem.{0, 0} active c.coordinates.owner →
                  Eq.{1} c.coordinates.owner e.permission.owner →
                    Eq.{1} c.operation r.operation →
                      Eq.{1} c.coordinates.event r.coordinates.event →
                        Eq.{1} c.coordinates.payload r.coordinates.payload →
                          Eq.{1} c.coordinates.handler installation.handle →
                            Eq.{1} c.coordinates.catchSite installation.site →
                              Eq.{1} c.coordinates.owner installation.owner →
                                Membership.mem.{0, 0} installation.arms
                                    (YulangClosure.NativeCallbackGrantBridgeR31.armKey table a) →
                                  Eq.{1} c.coordinates.arm a.coordinates.handle →
                                    Eq.{1} c.coordinates.armSite a.coordinates.site →
                                      Eq.{1} c.operation a.operation →
                                        Eq.{1}
                                          (YulangClosure.CallbackHygieneCorrespondence.checkedCatch
                                            (YulangClosure.NativeCallbackGrantBridgeR31.callbackSlice e n u x
                                              (YulangClosure.NativeCallbackGrantBridgeR31.requestKey table r)
                                              e.permission active installation)
                                            (YulangClosure.NativeCallbackGrantBridgeR31.requestKey table r)
                                            (YulangClosure.NativeCallbackGrantBridgeR31.consumerKey table c)
                                            e.permission)
                                          (some.{0}
                                            { request := YulangClosure.NativeCallbackGrantBridgeR31.requestKey table r,
                                              consumer :=
                                                YulangClosure.NativeCallbackGrantBridgeR31.consumerKey table c,
                                              permission := e.permission }) :=
⋯
'YulangClosure.NativeCallbackGrantBridgeR31.callback_checked_catch' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.NativeCallbackGrantBridgeR32.referenced_operations_covered : ∀ {Module Parse Green : Type}
  (r c a : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green)
  (families : List.{0} (YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green))
  (op : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green),
  Membership.mem.{0, 0} (List.cons.{0} r (List.cons.{0} c (List.cons.{0} a List.nil.{0}))) op →
    Membership.mem.{0, 0} (YulangClosure.NativeCallbackGrantBridgeR32.coveringTable r c a families).operations op :=
⋯
'YulangClosure.NativeCallbackGrantBridgeR32.referenced_operations_covered' does not depend on any axioms
theorem YulangClosure.NativeCallbackGrantBridgeR32.referenced_families_covered : ∀ {Module Parse Green : Type}
  (r c a : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green)
  (families : List.{0} (YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green))
  (op : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green),
  Membership.mem.{0, 0} (List.cons.{0} r (List.cons.{0} c (List.cons.{0} a List.nil.{0}))) op →
    Membership.mem.{0, 0} (YulangClosure.NativeCallbackGrantBridgeR32.coveringTable r c a families).families
      op.family :=
⋯
'YulangClosure.NativeCallbackGrantBridgeR32.referenced_families_covered' depends on axioms: [propext]
theorem YulangClosure.NativeCallbackGrantBridgeR32.permission_families_covered : ∀ {Module Parse Green : Type}
  (r c a : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green)
  (families : List.{0} (YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green))
  (f : YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green),
  Membership.mem.{0, 0} families f →
    Membership.mem.{0, 0} (YulangClosure.NativeCallbackGrantBridgeR32.coveringTable r c a families).families f :=
⋯
'YulangClosure.NativeCallbackGrantBridgeR32.permission_families_covered' does not depend on any axioms
theorem YulangClosure.NativeCallbackGrantBridgeR32.referenced_operation_round_trip : ∀ {Module Parse Green : Type}
  [inst : DecidableEq.{1} Module] [inst_1 : DecidableEq.{1} Parse] [inst_2 : DecidableEq.{1} Green]
  (r c a : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green)
  (families : List.{0} (YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green))
  {op : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green},
  Membership.mem.{0, 0} (List.cons.{0} r (List.cons.{0} c (List.cons.{0} a List.nil.{0}))) op →
    Eq.{1}
      (YulangClosure.NativeCallbackGrantBridgeR31.decodeOperation
        (YulangClosure.NativeCallbackGrantBridgeR32.coveringTable r c a families)
        (YulangClosure.NativeCallbackGrantBridgeR31.operationKey
          (YulangClosure.NativeCallbackGrantBridgeR32.coveringTable r c a families) op))
      (some.{0} op) :=
⋯
'YulangClosure.NativeCallbackGrantBridgeR32.referenced_operation_round_trip' depends on axioms: [propext,
 Quot.sound.{u}]
theorem YulangClosure.NativeCallbackGrantBridgeR32.covered_operation_keys_distinct : ∀ {Module Parse Green : Type}
  [inst : DecidableEq.{1} Module] [inst_1 : DecidableEq.{1} Parse] [inst_2 : DecidableEq.{1} Green]
  (r c a : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green)
  (families : List.{0} (YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green))
  {left right : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green},
  Membership.mem.{0, 0} (List.cons.{0} r (List.cons.{0} c (List.cons.{0} a List.nil.{0}))) left →
    Membership.mem.{0, 0} (List.cons.{0} r (List.cons.{0} c (List.cons.{0} a List.nil.{0}))) right →
      Ne.{1} left right →
        Ne.{1}
          (YulangClosure.NativeCallbackGrantBridgeR31.operationKey
            (YulangClosure.NativeCallbackGrantBridgeR32.coveringTable r c a families) left)
          (YulangClosure.NativeCallbackGrantBridgeR31.operationKey
            (YulangClosure.NativeCallbackGrantBridgeR32.coveringTable r c a families) right) :=
⋯
'YulangClosure.NativeCallbackGrantBridgeR32.covered_operation_keys_distinct' depends on axioms: [propext,
 Quot.sound.{u}]
theorem YulangClosure.NativeCallbackGrantBridgeR32.covered_family_membership_iff : ∀ {Module Parse Green : Type}
  [inst : DecidableEq.{1} Module] [inst_1 : DecidableEq.{1} Parse] [inst_2 : DecidableEq.{1} Green]
  (r c a : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green)
  (families : List.{0} (YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green))
  {op : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green},
  Membership.mem.{0, 0} (List.cons.{0} r (List.cons.{0} c (List.cons.{0} a List.nil.{0}))) op →
    (Membership.mem.{0, 0}
        (List.map.{0, 0}
          (fun a_1 =>
            List.idxOf.{0} a_1 (YulangClosure.NativeCallbackGrantBridgeR32.coveringTable r c a families).families)
          families)
        (List.idxOf.{0} op.family (YulangClosure.NativeCallbackGrantBridgeR32.coveringTable r c a families).families) ↔
      Membership.mem.{0, 0} families op.family) :=
⋯
'YulangClosure.NativeCallbackGrantBridgeR32.covered_family_membership_iff' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.NativeCallbackGrantBridgeR32.permission_row_round_trip : ∀ {Module Parse Green : Type}
  [inst : DecidableEq.{1} Module] [inst_1 : DecidableEq.{1} Parse] [inst_2 : DecidableEq.{1} Green]
  (r c a : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green)
  (families : List.{0} (YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green))
  {f : YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green},
  Membership.mem.{0, 0} families f →
    have table := YulangClosure.NativeCallbackGrantBridgeR32.coveringTable r c a families;
    Eq.{1} (getElem?.{0, 0, 0} table.families (List.idxOf.{0} f table.families)) (some.{0} f) ∧
      (Membership.mem.{0, 0} (List.map.{0, 0} (fun a => List.idxOf.{0} a table.families) families)
          (List.idxOf.{0} f table.families) ↔
        Membership.mem.{0, 0} families f) :=
⋯
'YulangClosure.NativeCallbackGrantBridgeR32.permission_row_round_trip' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.NativeCallbackGrantBridgeR32.entryWithRow_use_ready : ∀ {Module Parse Green : Type}
  [inst : DecidableEq.{1} Module] [inst_1 : DecidableEq.{1} Parse] [inst_2 : DecidableEq.{1} Green]
  (table : YulangClosure.NativeCallbackGrantBridgeR31.IdentityTable Module Parse Green)
  (families : List.{0} (YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green))
  (e : YulangClosure.CallbackHygieneCorrespondence.Entry) (n : YulangClosure.CallbackHygieneCorrespondence.NameRead)
  (u : YulangClosure.CallbackHygieneCorrespondence.CallbackUse),
  YulangClosure.CallbackHygieneCorrespondence.UseReady e n u →
    YulangClosure.CallbackHygieneCorrespondence.UseReady
      (YulangClosure.NativeCallbackGrantBridgeR32.entryWithRow table families e) n u :=
⋯
'YulangClosure.NativeCallbackGrantBridgeR32.entryWithRow_use_ready' does not depend on any axioms
theorem YulangClosure.NativeCallbackGrantBridgeR32.empty_table_collapse : ∀ {Module Parse Green : Type}
  [inst : DecidableEq.{1} Module] [inst_1 : DecidableEq.{1} Parse] [inst_2 : DecidableEq.{1} Green]
  (left right : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green),
  Eq.{1}
      (YulangClosure.NativeCallbackGrantBridgeR31.operationKey { families := List.nil.{0}, operations := List.nil.{0} }
        left)
      (YulangClosure.NativeCallbackGrantBridgeR31.operationKey { families := List.nil.{0}, operations := List.nil.{0} }
        right) ∧
    Eq.{1}
      (YulangClosure.NativeCallbackGrantBridgeR31.decodeOperation
        { families := List.nil.{0}, operations := List.nil.{0} }
        (YulangClosure.NativeCallbackGrantBridgeR31.operationKey
          { families := List.nil.{0}, operations := List.nil.{0} } left))
      none.{0} :=
⋯
'YulangClosure.NativeCallbackGrantBridgeR32.empty_table_collapse' depends on axioms: [propext]
theorem YulangClosure.NativeCallbackGrantBridgeR32.empty_table_not_covered : ∀ {Module Parse Green : Type}
  (op : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green),
  ¬Membership.mem.{0, 0} { families := List.nil.{0}, operations := List.nil.{0} }.operations op :=
⋯
'YulangClosure.NativeCallbackGrantBridgeR32.empty_table_not_covered' depends on axioms: [propext]
theorem YulangClosure.NativeCallbackGrantBridgeR32.covered_checked_catch : ∀ {Module Parse Green : Type}
  [inst : DecidableEq.{1} Module] [inst_1 : DecidableEq.{1} Parse] [inst_2 : DecidableEq.{1} Green]
  (r : YulangClosure.NativeCallbackGrantBridgeR31.NativeRequest Module Parse Green)
  (c : YulangClosure.NativeCallbackGrantBridgeR31.NativeConsumer Module Parse Green)
  (a : YulangClosure.NativeCallbackGrantBridgeR31.NativeArm Module Parse Green)
  (e : YulangClosure.CallbackHygieneCorrespondence.Entry) (n : YulangClosure.CallbackHygieneCorrespondence.NameRead)
  (u : YulangClosure.CallbackHygieneCorrespondence.CallbackUse)
  (x : YulangClosure.CallbackHygieneCorrespondence.Execution)
  (active :
    List.{0}
      (YulangClosure.CallbackHygieneCorrespondence.Id YulangClosure.CallbackHygieneCorrespondence.Kind.invocation))
  (installation : YulangClosure.CallbackHygieneCorrespondence.InstalledCatch)
  (families : List.{0} (YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green)),
  YulangClosure.CallbackHygieneCorrespondence.UseReady e n u →
    Eq.{1} x.useHandle u.handle →
      Eq.{1} x.view u.resultView →
        Eq.{1} x.receipt u.resultReceipt.handle →
          Eq.{1} r.coordinates.origin (YulangClosure.CallbackHygieneCorrespondence.Origin.callback x) →
            Membership.mem.{0, 0} families r.operation.family →
              Membership.mem.{0, 0} active c.coordinates.owner →
                Eq.{1} c.coordinates.owner e.permission.owner →
                  Eq.{1} c.operation r.operation →
                    Eq.{1} c.coordinates.event r.coordinates.event →
                      Eq.{1} c.coordinates.payload r.coordinates.payload →
                        Eq.{1} c.coordinates.handler installation.handle →
                          Eq.{1} c.coordinates.catchSite installation.site →
                            Eq.{1} c.coordinates.owner installation.owner →
                              Membership.mem.{0, 0} installation.arms
                                  (YulangClosure.NativeCallbackGrantBridgeR31.armKey
                                    (YulangClosure.NativeCallbackGrantBridgeR32.coveringTable r.operation c.operation
                                      a.operation families)
                                    a) →
                                Eq.{1} c.coordinates.arm a.coordinates.handle →
                                  Eq.{1} c.coordinates.armSite a.coordinates.site →
                                    Eq.{1} c.operation a.operation →
                                      have table :=
                                        YulangClosure.NativeCallbackGrantBridgeR32.coveringTable r.operation c.operation
                                          a.operation families;
                                      have projectedEntry :=
                                        YulangClosure.NativeCallbackGrantBridgeR32.entryWithRow table families e;
                                      Eq.{1}
                                          (YulangClosure.NativeCallbackGrantBridgeR31.decodeOperation table
                                            (YulangClosure.NativeCallbackGrantBridgeR31.requestKey table r).operation)
                                          (some.{0} r.operation) ∧
                                        Eq.{1}
                                            (YulangClosure.NativeCallbackGrantBridgeR31.decodeOperation table
                                              (YulangClosure.NativeCallbackGrantBridgeR31.consumerKey table
                                                  c).operation)
                                            (some.{0} c.operation) ∧
                                          Eq.{1}
                                              (YulangClosure.NativeCallbackGrantBridgeR31.decodeOperation table
                                                (YulangClosure.NativeCallbackGrantBridgeR31.armKey table a).operation)
                                              (some.{0} a.operation) ∧
                                            (Membership.mem.{0, 0} projectedEntry.permission.families
                                                  (YulangClosure.NativeCallbackGrantBridgeR31.requestKey table
                                                        r).operation.family ↔
                                                Membership.mem.{0, 0} families r.operation.family) ∧
                                              Eq.{1}
                                                (YulangClosure.CallbackHygieneCorrespondence.checkedCatch
                                                  (YulangClosure.NativeCallbackGrantBridgeR31.callbackSlice
                                                    projectedEntry n u x
                                                    (YulangClosure.NativeCallbackGrantBridgeR31.requestKey table r)
                                                    projectedEntry.permission active installation)
                                                  (YulangClosure.NativeCallbackGrantBridgeR31.requestKey table r)
                                                  (YulangClosure.NativeCallbackGrantBridgeR31.consumerKey table c)
                                                  projectedEntry.permission)
                                                (some.{0}
                                                  {
                                                    request :=
                                                      YulangClosure.NativeCallbackGrantBridgeR31.requestKey table r,
                                                    consumer :=
                                                      YulangClosure.NativeCallbackGrantBridgeR31.consumerKey table c,
                                                    permission := projectedEntry.permission }) :=
⋯
'YulangClosure.NativeCallbackGrantBridgeR32.covered_checked_catch' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.NativeCallbackCoordinatesR33.family_wrong_token : ∀ {Token Module Parse Green : Type}
  [inst : DecidableEq.{1} Token] (s : YulangClosure.NativeCallbackCoordinatesR33.HirSnapshot Token Module Parse Green)
  (q : YulangClosure.NativeCallbackCoordinatesR33.FamilyCoordinate Token),
  Ne.{1} q.snapshotToken s.token →
    Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.decodeFamilyCoordinate s q) none.{0} :=
⋯
'YulangClosure.NativeCallbackCoordinatesR33.family_wrong_token' depends on axioms: [propext]
theorem YulangClosure.NativeCallbackCoordinatesR33.operation_wrong_token : ∀ {Token Module Parse Green : Type}
  [inst : DecidableEq.{1} Token] [inst_1 : DecidableEq.{1} Module] [inst_2 : DecidableEq.{1} Parse]
  [inst_3 : DecidableEq.{1} Green] (s : YulangClosure.NativeCallbackCoordinatesR33.HirSnapshot Token Module Parse Green)
  (q : YulangClosure.NativeCallbackCoordinatesR33.OperationCoordinate Token),
  Ne.{1} q.family.snapshotToken s.token →
    Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.decodeOperationCoordinate s q) none.{0} :=
⋯
'YulangClosure.NativeCallbackCoordinatesR33.operation_wrong_token' depends on axioms: [propext]
theorem YulangClosure.NativeCallbackCoordinatesR33.family_out_of_range : ∀ {Token Module Parse Green : Type}
  [inst : DecidableEq.{1} Token] (s : YulangClosure.NativeCallbackCoordinatesR33.HirSnapshot Token Module Parse Green)
  (q : YulangClosure.NativeCallbackCoordinatesR33.FamilyCoordinate Token),
  LE.le.{0} (List.length.{0} s.effects) q.effectIndex →
    Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.decodeFamilyCoordinate s q) none.{0} :=
⋯
'YulangClosure.NativeCallbackCoordinatesR33.family_out_of_range' depends on axioms: [propext]
theorem YulangClosure.NativeCallbackCoordinatesR33.operation_effect_out_of_range : ∀ {Token Module Parse Green : Type}
  [inst : DecidableEq.{1} Token] [inst_1 : DecidableEq.{1} Module] [inst_2 : DecidableEq.{1} Parse]
  [inst_3 : DecidableEq.{1} Green] (s : YulangClosure.NativeCallbackCoordinatesR33.HirSnapshot Token Module Parse Green)
  (q : YulangClosure.NativeCallbackCoordinatesR33.OperationCoordinate Token),
  LE.le.{0} (List.length.{0} s.effects) q.family.effectIndex →
    Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.decodeOperationCoordinate s q) none.{0} :=
⋯
'YulangClosure.NativeCallbackCoordinatesR33.operation_effect_out_of_range' depends on axioms: [propext]
theorem YulangClosure.NativeCallbackCoordinatesR33.operation_out_of_range : ∀ {Token Module Parse Green : Type}
  [inst : DecidableEq.{1} Token] [inst_1 : DecidableEq.{1} Module] [inst_2 : DecidableEq.{1} Parse]
  [inst_3 : DecidableEq.{1} Green] (s : YulangClosure.NativeCallbackCoordinatesR33.HirSnapshot Token Module Parse Green)
  (q : YulangClosure.NativeCallbackCoordinatesR33.OperationCoordinate Token)
  (effect : YulangClosure.NativeCallbackCoordinatesR33.HirEffect Module Parse Green),
  Eq.{1} (getElem?.{0, 0, 0} s.effects q.family.effectIndex) (some.{0} effect) →
    LE.le.{0} (List.length.{0} effect.operations) q.operationIndex →
      Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.decodeOperationCoordinate s q) none.{0} :=
⋯
'YulangClosure.NativeCallbackCoordinatesR33.operation_out_of_range' depends on axioms: [propext]
theorem YulangClosure.NativeCallbackCoordinatesR33.operation_wrong_family : ∀ {Token Module Parse Green : Type}
  [inst : DecidableEq.{1} Token] [inst_1 : DecidableEq.{1} Module] [inst_2 : DecidableEq.{1} Parse]
  [inst_3 : DecidableEq.{1} Green] (s : YulangClosure.NativeCallbackCoordinatesR33.HirSnapshot Token Module Parse Green)
  (q : YulangClosure.NativeCallbackCoordinatesR33.OperationCoordinate Token)
  (effect : YulangClosure.NativeCallbackCoordinatesR33.HirEffect Module Parse Green)
  (operation : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green),
  Eq.{1} (getElem?.{0, 0, 0} s.effects q.family.effectIndex) (some.{0} effect) →
    Eq.{1} (getElem?.{0, 0, 0} effect.operations q.operationIndex) (some.{0} operation) →
      Ne.{1} operation.family effect.identity →
        Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.decodeOperationCoordinate s q) none.{0} :=
⋯
'YulangClosure.NativeCallbackCoordinatesR33.operation_wrong_family' depends on axioms: [propext]
theorem YulangClosure.NativeCallbackCoordinatesR33.family_decode_exact : ∀ {Token Module Parse Green : Type}
  [inst : DecidableEq.{1} Token] (s : YulangClosure.NativeCallbackCoordinatesR33.HirSnapshot Token Module Parse Green)
  (q : YulangClosure.NativeCallbackCoordinatesR33.FamilyCoordinate Token)
  {family : YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green},
  Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.decodeFamilyCoordinate s q) (some.{0} family) →
    Eq.{1} q.snapshotToken s.token ∧
      Exists.{1} fun effect =>
        Eq.{1} (getElem?.{0, 0, 0} s.effects q.effectIndex) (some.{0} effect) ∧ Eq.{1} family effect.identity :=
⋯
'YulangClosure.NativeCallbackCoordinatesR33.family_decode_exact' depends on axioms: [propext]
theorem YulangClosure.NativeCallbackCoordinatesR33.family_decode_bounded : ∀ {Token Module Parse Green : Type}
  [inst : DecidableEq.{1} Token] (s : YulangClosure.NativeCallbackCoordinatesR33.HirSnapshot Token Module Parse Green)
  (q : YulangClosure.NativeCallbackCoordinatesR33.FamilyCoordinate Token)
  {family : YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green},
  Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.decodeFamilyCoordinate s q) (some.{0} family) →
    Eq.{1} q.snapshotToken s.token ∧
      Exists.{0} fun bound => Eq.{1} family (getElem.{0, 0, 0} s.effects q.effectIndex bound).identity :=
⋯
'YulangClosure.NativeCallbackCoordinatesR33.family_decode_bounded' depends on axioms: [propext]
theorem YulangClosure.NativeCallbackCoordinatesR33.operation_decode_exact : ∀ {Token Module Parse Green : Type}
  [inst : DecidableEq.{1} Token] [inst_1 : DecidableEq.{1} Module] [inst_2 : DecidableEq.{1} Parse]
  [inst_3 : DecidableEq.{1} Green] (s : YulangClosure.NativeCallbackCoordinatesR33.HirSnapshot Token Module Parse Green)
  (q : YulangClosure.NativeCallbackCoordinatesR33.OperationCoordinate Token)
  {operation : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green},
  Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.decodeOperationCoordinate s q) (some.{0} operation) →
    Eq.{1} q.family.snapshotToken s.token ∧
      Exists.{1} fun effect =>
        Eq.{1} (getElem?.{0, 0, 0} s.effects q.family.effectIndex) (some.{0} effect) ∧
          Eq.{1} (getElem?.{0, 0, 0} effect.operations q.operationIndex) (some.{0} operation) ∧
            Eq.{1} operation.family effect.identity :=
⋯
'YulangClosure.NativeCallbackCoordinatesR33.operation_decode_exact' depends on axioms: [propext]
theorem YulangClosure.NativeCallbackCoordinatesR33.operation_decode_bounded : ∀ {Token Module Parse Green : Type}
  [inst : DecidableEq.{1} Token] [inst_1 : DecidableEq.{1} Module] [inst_2 : DecidableEq.{1} Parse]
  [inst_3 : DecidableEq.{1} Green] (s : YulangClosure.NativeCallbackCoordinatesR33.HirSnapshot Token Module Parse Green)
  (q : YulangClosure.NativeCallbackCoordinatesR33.OperationCoordinate Token)
  {operation : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green},
  Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.decodeOperationCoordinate s q) (some.{0} operation) →
    Eq.{1} q.family.snapshotToken s.token ∧
      Exists.{1} fun effect =>
        (Exists.{0} fun bound => Eq.{1} (getElem.{0, 0, 0} s.effects q.family.effectIndex bound) effect) ∧
          (Exists.{0} fun bound => Eq.{1} (getElem.{0, 0, 0} effect.operations q.operationIndex bound) operation) ∧
            Eq.{1} operation.family effect.identity :=
⋯
'YulangClosure.NativeCallbackCoordinatesR33.operation_decode_bounded' depends on axioms: [propext]
theorem YulangClosure.NativeCallbackCoordinatesR33.operation_family_decode : ∀ {Token Module Parse Green : Type}
  [inst : DecidableEq.{1} Token] [inst_1 : DecidableEq.{1} Module] [inst_2 : DecidableEq.{1} Parse]
  [inst_3 : DecidableEq.{1} Green] (s : YulangClosure.NativeCallbackCoordinatesR33.HirSnapshot Token Module Parse Green)
  (q : YulangClosure.NativeCallbackCoordinatesR33.OperationCoordinate Token)
  {operation : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green},
  Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.decodeOperationCoordinate s q) (some.{0} operation) →
    Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.decodeFamilyCoordinate s q.family) (some.{0} operation.family) :=
⋯
'YulangClosure.NativeCallbackCoordinatesR33.operation_family_decode' depends on axioms: [propext]
theorem YulangClosure.NativeCallbackCoordinatesR33.row_decode_length : ∀ {Token Module Parse Green : Type}
  [inst : DecidableEq.{1} Token] (s : YulangClosure.NativeCallbackCoordinatesR33.HirSnapshot Token Module Parse Green)
  (coordinates : List.{0} (YulangClosure.NativeCallbackCoordinatesR33.FamilyCoordinate Token))
  {families : List.{0} (YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green)},
  Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.decodeFamilyRow s coordinates) (some.{0} families) →
    Eq.{1} (List.length.{0} families) (List.length.{0} coordinates) :=
⋯
'YulangClosure.NativeCallbackCoordinatesR33.row_decode_length' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.NativeCallbackCoordinatesR33.row_bad_member_rejected : ∀ {Token Module Parse Green : Type}
  [inst : DecidableEq.{1} Token] (s : YulangClosure.NativeCallbackCoordinatesR33.HirSnapshot Token Module Parse Green)
  (coordinates : List.{0} (YulangClosure.NativeCallbackCoordinatesR33.FamilyCoordinate Token))
  {bad : YulangClosure.NativeCallbackCoordinatesR33.FamilyCoordinate Token},
  Membership.mem.{0, 0} coordinates bad →
    Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.decodeFamilyCoordinate s bad) none.{0} →
      Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.decodeFamilyRow s coordinates) none.{0} :=
⋯
'YulangClosure.NativeCallbackCoordinatesR33.row_bad_member_rejected' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.NativeCallbackCoordinatesR33.permission_row_exact : ∀ {Token Module Parse Green : Type}
  [inst : DecidableEq.{1} Token] [inst_1 : DecidableEq.{1} Module] [inst_2 : DecidableEq.{1} Parse]
  [inst_3 : DecidableEq.{1} Green] (s : YulangClosure.NativeCallbackCoordinatesR33.HirSnapshot Token Module Parse Green)
  (coordinates : List.{0} (YulangClosure.NativeCallbackCoordinatesR33.FamilyCoordinate Token))
  {families : List.{0} (YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green)},
  Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.translatePermissionRow s coordinates) (some.{0} families) →
    Eq.{1} families s.permissionRow ∧
      Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.decodeFamilyRow s coordinates) (some.{0} families) ∧
        Eq.{1} (List.length.{0} families) (List.length.{0} coordinates) :=
⋯
'YulangClosure.NativeCallbackCoordinatesR33.permission_row_exact' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.NativeCallbackCoordinatesR33.incomplete_row_rejected : ∀ {Token Module Parse Green : Type}
  [inst : DecidableEq.{1} Token] [inst_1 : DecidableEq.{1} Module] [inst_2 : DecidableEq.{1} Parse]
  [inst_3 : DecidableEq.{1} Green] (s : YulangClosure.NativeCallbackCoordinatesR33.HirSnapshot Token Module Parse Green)
  (coordinates : List.{0} (YulangClosure.NativeCallbackCoordinatesR33.FamilyCoordinate Token))
  (families : List.{0} (YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green)),
  Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.decodeFamilyRow s coordinates) (some.{0} families) →
    Ne.{1} families s.permissionRow →
      Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.translatePermissionRow s coordinates) none.{0} :=
⋯
'YulangClosure.NativeCallbackCoordinatesR33.incomplete_row_rejected' depends on axioms: [propext]
theorem YulangClosure.NativeCallbackCoordinatesR33.bad_row_rejected : ∀ {Token Module Parse Green : Type}
  [inst : DecidableEq.{1} Token] [inst_1 : DecidableEq.{1} Module] [inst_2 : DecidableEq.{1} Parse]
  [inst_3 : DecidableEq.{1} Green] (s : YulangClosure.NativeCallbackCoordinatesR33.HirSnapshot Token Module Parse Green)
  (coordinates : List.{0} (YulangClosure.NativeCallbackCoordinatesR33.FamilyCoordinate Token)),
  Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.decodeFamilyRow s coordinates) none.{0} →
    Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.translatePermissionRow s coordinates) none.{0} :=
⋯
'YulangClosure.NativeCallbackCoordinatesR33.bad_row_rejected' depends on axioms: [propext]
theorem YulangClosure.NativeCallbackCoordinatesR33.translation_exact : ∀ {Token Module Parse Green : Type}
  [inst : DecidableEq.{1} Token] [inst_1 : DecidableEq.{1} Module] [inst_2 : DecidableEq.{1} Parse]
  [inst_3 : DecidableEq.{1} Green] (s : YulangClosure.NativeCallbackCoordinatesR33.HirSnapshot Token Module Parse Green)
  (request consumer arm : YulangClosure.NativeCallbackCoordinatesR33.OperationCoordinate Token)
  (row : List.{0} (YulangClosure.NativeCallbackCoordinatesR33.FamilyCoordinate Token))
  {out : YulangClosure.NativeCallbackCoordinatesR33.DecodedCoordinates Module Parse Green},
  Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.translateCoordinates s request consumer arm row) (some.{0} out) →
    Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.decodeOperationCoordinate s request) (some.{0} out.request) ∧
      Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.decodeOperationCoordinate s consumer) (some.{0} out.consumer) ∧
        Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.decodeOperationCoordinate s arm) (some.{0} out.arm) ∧
          Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.translatePermissionRow s row) (some.{0} out.families) :=
⋯
'YulangClosure.NativeCallbackCoordinatesR33.translation_exact' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.NativeCallbackCoordinatesR33.translation_to_r32 : ∀ {Token Module Parse Green : Type}
  [inst : DecidableEq.{1} Token] [inst_1 : DecidableEq.{1} Module] [inst_2 : DecidableEq.{1} Parse]
  [inst_3 : DecidableEq.{1} Green] (s : YulangClosure.NativeCallbackCoordinatesR33.HirSnapshot Token Module Parse Green)
  (request consumer arm : YulangClosure.NativeCallbackCoordinatesR33.OperationCoordinate Token)
  (row : List.{0} (YulangClosure.NativeCallbackCoordinatesR33.FamilyCoordinate Token))
  {out : YulangClosure.NativeCallbackCoordinatesR33.DecodedCoordinates Module Parse Green},
  Eq.{1} (YulangClosure.NativeCallbackCoordinatesR33.translateCoordinates s request consumer arm row) (some.{0} out) →
    have table :=
      YulangClosure.NativeCallbackGrantBridgeR32.coveringTable out.request out.consumer out.arm out.families;
    Eq.{1} out.families s.permissionRow ∧
      Eq.{1} (List.length.{0} out.families) (List.length.{0} row) ∧
        Eq.{1} request.family.snapshotToken s.token ∧
          Eq.{1} consumer.family.snapshotToken s.token ∧
            Eq.{1} arm.family.snapshotToken s.token ∧
              (Exists.{1} fun effect =>
                  Membership.mem.{0, 0} s.effects effect ∧
                    Membership.mem.{0, 0} effect.operations out.request ∧ Eq.{1} out.request.family effect.identity) ∧
                (Exists.{1} fun effect =>
                    Membership.mem.{0, 0} s.effects effect ∧
                      Membership.mem.{0, 0} effect.operations out.consumer ∧
                        Eq.{1} out.consumer.family effect.identity) ∧
                  (Exists.{1} fun effect =>
                      Membership.mem.{0, 0} s.effects effect ∧
                        Membership.mem.{0, 0} effect.operations out.arm ∧ Eq.{1} out.arm.family effect.identity) ∧
                    (∀ (op : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green),
                        Membership.mem.{0, 0}
                            (List.cons.{0} out.request
                              (List.cons.{0} out.consumer (List.cons.{0} out.arm List.nil.{0})))
                            op →
                          Membership.mem.{0, 0} table.operations op) ∧
                      (∀ (family : YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green),
                          Membership.mem.{0, 0} s.permissionRow family → Membership.mem.{0, 0} table.families family) ∧
                        Eq.{1}
                            (YulangClosure.NativeCallbackGrantBridgeR31.decodeOperation table
                              (YulangClosure.NativeCallbackGrantBridgeR31.operationKey table out.request))
                            (some.{0} out.request) ∧
                          Eq.{1}
                              (YulangClosure.NativeCallbackGrantBridgeR31.decodeOperation table
                                (YulangClosure.NativeCallbackGrantBridgeR31.operationKey table out.consumer))
                              (some.{0} out.consumer) ∧
                            Eq.{1}
                                (YulangClosure.NativeCallbackGrantBridgeR31.decodeOperation table
                                  (YulangClosure.NativeCallbackGrantBridgeR31.operationKey table out.arm))
                                (some.{0} out.arm) ∧
                              ∀ (family : YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green),
                                Membership.mem.{0, 0} s.permissionRow family →
                                  Eq.{1} (getElem?.{0, 0, 0} table.families (List.idxOf.{0} family table.families))
                                      (some.{0} family) ∧
                                    (Membership.mem.{0, 0}
                                        (List.map.{0, 0} (fun a => List.idxOf.{0} a table.families) out.families)
                                        (List.idxOf.{0} family table.families) ↔
                                      Membership.mem.{0, 0} out.families family) :=
⋯
'YulangClosure.NativeCallbackCoordinatesR33.translation_to_r32' depends on axioms: [propext, Quot.sound.{u}]

STDERR:
```
