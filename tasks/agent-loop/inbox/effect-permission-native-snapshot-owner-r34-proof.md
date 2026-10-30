# R34 proof handoff — frozen revision 1

Assignment `/root/effect_permission_r31_lean`, R34 session. Exact leases: this
handoff and `notes/theory/lean/YulangClosure/NativeSnapshotOwnerR34.lean`.
Single author, no descendants. Requested Sol/high; observed model/effort metadata
UNKNOWN. Independent review and Luna adjudication pending, no self-certification.

Outcome: kernel-accepted concrete finite retained-owner model, clone/issuance/
foreign rejection laws and composition with R33/R32. Source inspection supplies
the candidate Arc-owner map, not a Lean proof of Rust allocator internals or
native execution. Serializer/offline token correspondence, complete native
provenance and all original parents remain OPEN.

## Authority, original parent and frozen dependencies

Read R34 contract/manifest, exact R33 module/handoff/review, current frozen Rust
owner implementation/handoff, HIR owner definition and pinned Lean source APIs.
Root AGENTS.md, goal-driven sprint rules and Lean proof skill/source/execution
references were read in this leaf session. Original source-preservation
§§1,3,5 with birth-level correction §§2–6 and annotation-effect policy
§§1.1,1.2,3,4 retain authority. Original quantifiers range over every supported
source, lawful finite Simple-sub history and retained extrusion occurrence,
with unchanged scopes, complete Call/effects, correlated evidence and one shared
strategy. No research draft, finite model or kernel receipt changes that scope.

- `tasks/agent-loop/sprints/effect-permission-native-snapshot-owner-20261031-r34.md`: `e81a6b7316623bc009f6f1488fdf5d9ba6e258efe9e6144d164f5c81d1061ff2`.
- `tasks/agent-loop/sprints/effect-permission-native-snapshot-owner-20261031-r34-inputs-r1.json`: `57c07d14d9074a50e55c1b116c656599240883e61879b214f53448005da8e8ca`.
- `tools/inference-playground/src/runtime/program.rs`: `9823cd8d5c972e0c6ec2766d66f9d21c6564727317bc2646d2480a9e85132f74`.
- `crates/yu-hir/src/module.rs`: `6bf92c93fa37f425a7380248c12c50c0d04ea6eb282e76edb6df54e628260646`.
- `tasks/agent-loop/inbox/effect-permission-native-snapshot-owner-r34-rust.md`: `556d0ffda6e3c6d1f3b3e6722b0640564a72ff834be77cf632d1e293f061ea79`.
- `tasks/agent-loop/artifacts/native-snapshot-owner-r34.patch`: `36d96676c3c561bf2f525cd167ef33840221da4f2a93236b33932e70c9bc5361`.
- `notes/theory/2026-10-13-intrusion-source-preservation-proof.md`: `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271`.
- `notes/design/2026-10-24-birth-level-scc-intrusion.md`: `ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae`.
- `notes/design/2026-10-10-annotation-effect-hygiene-integration.md`: `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18`.

Exact entire R33 module is the unchanged 66862-byte prefix, SHA
`9d138f84ede8c38161195fad4a324d9f164a72632dcfa575b5a5197d2685a436`;
R33 proof SHA `b2837f9f2b7aa7dbb5e735103d8d9c8234be290c1dcdeaa8c74f0407604b0884`.
The preserved prefix contains exact R32 SHA
`bf2908ae347814c71ddc32ffae0f64a62103b855d96655a47aa1b9db0dc9690c`,
R31 SHA `a0a8b53e1f73ed44e92ee01b3e87531d310775af0804999d30d6fbb0a68e378d`
and R26 SHA `0621f43739c12ce1e7919a50de129414a4748d8359bf46740babd69f4854011e`.
R33 independent review SHA
`6413a347f4593ed61d9154331a54e5a3186b91161598c09152ec652e9d6044a8`
was read: its Unit-token/same-index counterexample motivates concrete owner
issuance. No dependency bytes were changed.

Program baseline per manifest was
`6607c4371366739c0e593b29a5da96becbb0bd743b2618a3755653f1b0ac3907`;
the updated frozen owner implementation is hashed above. R30 archive/member
pins remain `5c3c991dec9e54ad3e2665a1c722a0abf2d80a9efe719664606824558351a790`,
`machine.rs` `b74c8345e6e07155f482440bb9299b5fc12763accb666ca8f543156dd4a87425`,
`receiving.rs` `55b468cda3c3cf8180647a6429da28fc70badf7a371bf1b327539c8556b9b0f2`.
No archive extraction or quarantined runtime-path access in this packet.

## Concrete owner construction and source map

Namespace `YulangClosure.NativeSnapshotOwnerR34` (N below).
`AllocationHistory.empty` has no OwnerId (`Empty`). Allocating a HIR extends the
owner-name type to `Option` of the previous type: fresh owner is `none`, every
retained owner is embedded as `some old`. RetainedPool supplies immutable payload
lookup for every valid allocation name; allocate binds exactly the new payload
and preserves all retained payloads. RuntimeOwner contains its HIR allocation
name; ownerToken and issuedSnapshot derive from that same name. They cannot
supply an independently chosen token/owner pair.

No distinct-owner inequality is assumed. Fresh/retained separation is proved
by disjoint constructors, including two allocations with identical HIR contents.
The retained-name embedding preserves equality in both directions. This also
explains the representation change when ghost history grows: native tokens do
not change their pointer on other allocations; their identity equivalence is
preserved by this ghost embedding. Cloning preserves the name, exact snapshot
and actual coordinate translation.

These are ghost allocation names in one finite retained allocation history,
not HIR-relative declaration indices, raw pointer integers, a serialized token,
a Rust global counter or an added runtime data structure. The source code adds
no such history/counter. It uses the existing retained Arc allocation.

| Rust owner/source field | Lean interpretation | Evidence/limit |
| --- | --- | --- |
| RuntimeProgram::_hir: Arc<HirModule> | RuntimeOwner.hirOwner | denotes HIR allocation, not RuntimeProgram allocation |
| private HirSnapshotToken(Arc<HirModule>) | ownerToken of the same RuntimeOwner | sole initializer at program.rs:1272–1274 clones both from the same received hir |
| hir_snapshot_token accessor and derived Clone | cloneOwner preserves ownerToken | program.rs:40 and :332–333 retain the same strong Arc |
| identifies_same_snapshot / Arc::ptr_eq | equality of OwnerId names in one retained history | program.rs:43–44; actual Arc semantics are not proved by Lean |
| strong Arc lifetime | immutable total RetainedPool binding while capabilities remain retained | abstract retention domain; no model of Drop/refcounts/allocator reuse |

RuntimeProgram::from_hir and from_candidate_world route to the one
from_hir_with_roots construction. Two RuntimePrograms using clones of the same
HIR Arc share one HIR owner name. A separately allocated HIR gets a fresh name
even when its structure equals an existing HIR. The concrete source uses
Arc::ptr_eq rather than structural Eq, Debug, source text, spans or indices.

HirData is a fixed certificate view of HIR effects and one complete selected
source permission row. The row's AST/annotation origin is an OPEN extraction
premise. Owner equality does not prove row provenance or assert that a HIR has
only one permission annotation; another row/view requires the corresponding
source-scope instantiation. No row is selected globally by token identity.

## Exact theorem surface and axioms

Complete exact printed types and every #print axioms appear below. All definitions
and 76 theorems checked: 59 unchanged prefix declarations plus 17 new R34.

| New N theorem | Premises/conclusion summary | Complete axioms |
| --- | --- | --- |
| retention_preserves_token_equality | retained-name equality iff original token equality | none |
| clone_preserves_token | clone owner has the same token | none |
| clone_preserves_snapshot | clone owner has the same issued snapshot | none |
| issued_snapshot_exact | token, effects and complete row come from the same retained owner lookup | none |
| allocation_preserves_retained | allocation preserves the exact old payload under retained-name embedding | none |
| allocation_binds_fresh | fresh name retrieves exactly the newly supplied HIR view | none |
| fresh_owner_foreign | every retained owner token differs from the next freshly issued token; no inequality premise | none |
| equal_payload_allocations_foreign | two successive allocations of identical data have equal payloads and unequal owner tokens | none |
| foreign_family_rejected | coordinates issued by any retained owner reject under the fresh owner | propext |
| foreign_operation_rejected | nested operation coordinates from any retained owner reject under fresh owner | propext |
| fresh_family_rejected_by_retained | fresh-owner family coordinates reject under any retained owner | propext |
| fresh_operation_rejected_by_retained | fresh-owner nested operation coordinates reject under any retained owner | propext |
| owner_family_exact | successful owner-bound family decode supplies token equality, finite effect bound and exact stored identity | propext |
| owner_operation_exact | successful owner-bound operation decode supplies token equality, both finite bounds, exact stored operation and structural family join | propext |
| clone_preserves_translation | actual R33 coordinate computation unchanged by owner cloning | propext |
| owner_complete_row | successful row computation preserves exact complete retained source row, all decoded elements and length | propext, Quot.sound |
| owner_translation_to_r32 | successful owner-bound computation supplies exact retained-HIR memberships, complete row, all token joins and constructed/used R32 coverage and round trips | propext, Quot.sound |

New totals: eight no axioms; seven propext; two propext + Quot.sound. No target
decode/round-trip, source correspondence or inequality is supplied as an
assumption to establish these owner laws. Successful computation is the explicit
input to inversion/application theorems; it is not assumed for a concrete native
instance. No concrete native instance is constructed by defining these theorems.

## Parent application and remaining seam

N.owner_translation_to_r32 applies the actual R33 translation theorem to the
issued snapshot, hence R32 constructed operation/family coverage and its
round-trip/equivalence laws. The complete row and exact identity data come from
one retained owner view. Full names are present in the printed theorem types.
It is conditional finite mathematics and a source-qualified ownership map, not
a Rust execution, compiler theorem or native simulation.

First remaining owner: the quarantined serializer/certificate integration seam.
The proposal must attach owner-issued opaque Arc token clones and compare them
with the same retained owner's token before any coordinate lookup, preserve the
complete row and typed selected-arm identity, and establish the extraction
correspondence into this Lean retained-owner history. Source AST/annotation/
Name/Apply provenance, row authenticity, numeric conversion, observations and
Grant guards, actual request mint/emission, invocation lifetime and native
Step/History remain OPEN. The implemented token has no JSON representation;
offline/persisted certificates require a separately justified binding design.
The frozen Rust patch is an unapplied integration proposal, uncompiled and
untested. No quarantined consumer integration or native foreign-rejection receipt.

The native domain is same-process simultaneously retained strong Arc capabilities
for immutable HIR. No claim covers cross-process persistence, weak references,
released/reused addresses, mutation, Rust allocator internals or refcount/Drop
implementation. Relating the concrete Arc::ptr_eq relation to allocation-name
equality is explicitly source/native correspondence, not a hidden Lean axiom.
Original A/B, full accepted source scope and shared strategy, full hygiene/
soundness/principality/progress/termination and production remain OPEN.

## Execution, failure and resource receipt

All audits used:
`bwrap --ro-bind / / --dev /dev --proc /proc /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean --stdin -j1 -M1024`.
Stdin contained the complete module and #print / #print axioms for every theorem,
pp.universes true, pp.proofs false. Final audit: exit0,76 types/full axiom lists,
no diagnostics, empty stderr; 3.538853843 measured subprocess seconds.
Version check: same bwrap mounts with pinned executable --version, exit0:
Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)

Attempt1 exited1 in3.473093543s: instance synthesis did not unfold OwnerId's
recursive type. The actual diagnostics and Lean's downstream recovery sorryAx
reports are retained below as invalid completion evidence. Repair explicitly
changed the goals to DecidableEq Empty / DecidableEq (Option (OwnerId previous))
before constructing their real instances. Attempt2 checked75 declarations,
exit0,3.140296359s,no diagnostics. Then retention_preserves_token_equality was
added to make history-extension identity preservation explicit; final attempt3
checked all76 again. No source proof hole/project axiom was used.

The skill checker is incompatible with this packet's no-Lake/build/generated-file
boundary; the approved direct pinned stdin audit was used. Read-only bwrap
prevents ordinary filesystem writes, not a syscall-capture receipt. Stdout/stderr
remained in memory until written into this exact handoff. No Lake/Cargo/test,
build/target/cache, project copy/environment/installation, archive extraction,
external directory, scratch/separate log, compiler/runtime/config/root import,
scheduling record or Git mutation. Only the two exact leased files were written.
The complete module source scan contains no sorry/admit/project axiom/native_decide
or kernel-check bypass tokens. No native/runtime/checker receipt was fabricated.

Fresh R34 cap1600s; no R33 allowance transfer. Measured construction, proof
repair/audit and handoff interval: Unix1793380634.631349 through 1793381140.2658365 =
505.634487 seconds. Startup reads before that were unmeasured; aggregate active
and remaining-cap figures are UNKNOWN, not inferred from elapsed gaps. Audit
subprocess times are included in this interval, not extra usage.

Artifact SHA `24ca25828e1a58f9c3246e5f50f2c73ba8ead6d2d003d05c8c2a8a3d2e85795a`. Handoff hash returned after freezing without
self-reference. STOPPED; writes stopped after revision1; no descendants,
unreported outputs or generated caches. Independent review pending.

## Preserved complete audit output

### Construction interval marker

Measured construction interval start Unix 1793380634.631349; startup reads before that unmeasured. Fresh Lean cap1600 seconds, no R33 transfer.

## Audit attempt 1

Command: `bwrap --ro-bind / / --dev /dev --proc /proc /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean --stdin -j1 -M1024`; stdin complete module plus every theorem type and axioms. Exit 1; subprocess seconds 3.473093543001596.

```text
<stdin>:1326:14: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  DecidableEq (OwnerId AllocationHistory.empty)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
<stdin>:1329:4: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  DecidableEq (OwnerId previous.allocated)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
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
@[defeq] theorem YulangClosure.NativeSnapshotOwnerR34.clone_preserves_token : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory}
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history),
  Eq.{1} (YulangClosure.NativeSnapshotOwnerR34.ownerToken (YulangClosure.NativeSnapshotOwnerR34.cloneOwner owner))
    (YulangClosure.NativeSnapshotOwnerR34.ownerToken owner) :=
⋯
'YulangClosure.NativeSnapshotOwnerR34.clone_preserves_token' does not depend on any axioms
@[defeq] theorem YulangClosure.NativeSnapshotOwnerR34.clone_preserves_snapshot : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Module Parse Green : Type}
  (pool : YulangClosure.NativeSnapshotOwnerR34.RetainedPool history Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history),
  Eq.{1}
    (YulangClosure.NativeSnapshotOwnerR34.issuedSnapshot pool (YulangClosure.NativeSnapshotOwnerR34.cloneOwner owner))
    (YulangClosure.NativeSnapshotOwnerR34.issuedSnapshot pool owner) :=
⋯
'YulangClosure.NativeSnapshotOwnerR34.clone_preserves_snapshot' does not depend on any axioms
theorem YulangClosure.NativeSnapshotOwnerR34.issued_snapshot_exact : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Module Parse Green : Type}
  (pool : YulangClosure.NativeSnapshotOwnerR34.RetainedPool history Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history),
  Eq.{1} (YulangClosure.NativeSnapshotOwnerR34.issuedSnapshot pool owner).token
      (YulangClosure.NativeSnapshotOwnerR34.ownerToken owner) ∧
    Eq.{1} (YulangClosure.NativeSnapshotOwnerR34.issuedSnapshot pool owner).effects (pool.data owner.hirOwner).effects ∧
      Eq.{1} (YulangClosure.NativeSnapshotOwnerR34.issuedSnapshot pool owner).permissionRow
        (pool.data owner.hirOwner).permissionRow :=
⋯
'YulangClosure.NativeSnapshotOwnerR34.issued_snapshot_exact' does not depend on any axioms
@[defeq] theorem YulangClosure.NativeSnapshotOwnerR34.allocation_preserves_retained : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Module Parse Green : Type}
  (pool : YulangClosure.NativeSnapshotOwnerR34.RetainedPool history Module Parse Green)
  (hir : YulangClosure.NativeSnapshotOwnerR34.HirData Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history),
  Eq.{1}
    ((YulangClosure.NativeSnapshotOwnerR34.allocate pool hir).data
      (YulangClosure.NativeSnapshotOwnerR34.ownerToken (YulangClosure.NativeSnapshotOwnerR34.retainOwner owner)))
    (pool.data owner.hirOwner) :=
⋯
'YulangClosure.NativeSnapshotOwnerR34.allocation_preserves_retained' does not depend on any axioms
@[defeq] theorem YulangClosure.NativeSnapshotOwnerR34.allocation_binds_fresh : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Module Parse Green : Type}
  (pool : YulangClosure.NativeSnapshotOwnerR34.RetainedPool history Module Parse Green)
  (hir : YulangClosure.NativeSnapshotOwnerR34.HirData Module Parse Green),
  Eq.{1}
    ((YulangClosure.NativeSnapshotOwnerR34.allocate pool hir).data
      (YulangClosure.NativeSnapshotOwnerR34.ownerToken (YulangClosure.NativeSnapshotOwnerR34.freshOwner history)))
    hir :=
⋯
'YulangClosure.NativeSnapshotOwnerR34.allocation_binds_fresh' does not depend on any axioms
theorem YulangClosure.NativeSnapshotOwnerR34.fresh_owner_foreign : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory}
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history),
  Ne.{1} (YulangClosure.NativeSnapshotOwnerR34.ownerToken (YulangClosure.NativeSnapshotOwnerR34.retainOwner owner))
    (YulangClosure.NativeSnapshotOwnerR34.ownerToken (YulangClosure.NativeSnapshotOwnerR34.freshOwner history)) :=
⋯
'YulangClosure.NativeSnapshotOwnerR34.fresh_owner_foreign' does not depend on any axioms
theorem YulangClosure.NativeSnapshotOwnerR34.equal_payload_allocations_foreign : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Module Parse Green : Type}
  (pool : YulangClosure.NativeSnapshotOwnerR34.RetainedPool history Module Parse Green)
  (hir : YulangClosure.NativeSnapshotOwnerR34.HirData Module Parse Green),
  have extended :=
    YulangClosure.NativeSnapshotOwnerR34.allocate (YulangClosure.NativeSnapshotOwnerR34.allocate pool hir) hir;
  have retained :=
    YulangClosure.NativeSnapshotOwnerR34.retainOwner (YulangClosure.NativeSnapshotOwnerR34.freshOwner history);
  have fresh := YulangClosure.NativeSnapshotOwnerR34.freshOwner history.allocated;
  Eq.{1} (extended.data (YulangClosure.NativeSnapshotOwnerR34.ownerToken retained))
      (extended.data (YulangClosure.NativeSnapshotOwnerR34.ownerToken fresh)) ∧
    Ne.{1} (YulangClosure.NativeSnapshotOwnerR34.ownerToken retained)
      (YulangClosure.NativeSnapshotOwnerR34.ownerToken fresh) :=
⋯
'YulangClosure.NativeSnapshotOwnerR34.equal_payload_allocations_foreign' does not depend on any axioms
theorem YulangClosure.NativeSnapshotOwnerR34.foreign_family_rejected : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Module Parse Green : Type}
  (pool : YulangClosure.NativeSnapshotOwnerR34.RetainedPool history Module Parse Green)
  (hir : YulangClosure.NativeSnapshotOwnerR34.HirData Module Parse Green)
  (old : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (index : Nat),
  Eq.{1}
    (YulangClosure.NativeCallbackCoordinatesR33.decodeFamilyCoordinate
      (YulangClosure.NativeSnapshotOwnerR34.issuedSnapshot (YulangClosure.NativeSnapshotOwnerR34.allocate pool hir)
        (YulangClosure.NativeSnapshotOwnerR34.freshOwner history))
      (YulangClosure.NativeSnapshotOwnerR34.issuedFamily (YulangClosure.NativeSnapshotOwnerR34.retainOwner old) index))
    none.{0} :=
⋯
'YulangClosure.NativeSnapshotOwnerR34.foreign_family_rejected' depends on axioms: [propext, sorryAx.{u}]
theorem YulangClosure.NativeSnapshotOwnerR34.foreign_operation_rejected : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Module Parse Green : Type}
  [inst : DecidableEq.{1} Module] [inst_1 : DecidableEq.{1} Parse] [inst_2 : DecidableEq.{1} Green]
  (pool : YulangClosure.NativeSnapshotOwnerR34.RetainedPool history Module Parse Green)
  (hir : YulangClosure.NativeSnapshotOwnerR34.HirData Module Parse Green)
  (old : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (familyIndex operationIndex : Nat),
  Eq.{1}
    (YulangClosure.NativeCallbackCoordinatesR33.decodeOperationCoordinate
      (YulangClosure.NativeSnapshotOwnerR34.issuedSnapshot (YulangClosure.NativeSnapshotOwnerR34.allocate pool hir)
        (YulangClosure.NativeSnapshotOwnerR34.freshOwner history))
      (YulangClosure.NativeSnapshotOwnerR34.issuedOperation (YulangClosure.NativeSnapshotOwnerR34.retainOwner old)
        familyIndex operationIndex))
    none.{0} :=
⋯
'YulangClosure.NativeSnapshotOwnerR34.foreign_operation_rejected' depends on axioms: [propext, sorryAx.{u}]
theorem YulangClosure.NativeSnapshotOwnerR34.fresh_family_rejected_by_retained : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Module Parse Green : Type}
  (pool : YulangClosure.NativeSnapshotOwnerR34.RetainedPool history Module Parse Green)
  (hir : YulangClosure.NativeSnapshotOwnerR34.HirData Module Parse Green)
  (old : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (index : Nat),
  Eq.{1}
    (YulangClosure.NativeCallbackCoordinatesR33.decodeFamilyCoordinate
      (YulangClosure.NativeSnapshotOwnerR34.issuedSnapshot (YulangClosure.NativeSnapshotOwnerR34.allocate pool hir)
        (YulangClosure.NativeSnapshotOwnerR34.retainOwner old))
      (YulangClosure.NativeSnapshotOwnerR34.issuedFamily (YulangClosure.NativeSnapshotOwnerR34.freshOwner history)
        index))
    none.{0} :=
⋯
'YulangClosure.NativeSnapshotOwnerR34.fresh_family_rejected_by_retained' depends on axioms: [propext, sorryAx.{u}]
theorem YulangClosure.NativeSnapshotOwnerR34.fresh_operation_rejected_by_retained : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Module Parse Green : Type}
  [inst : DecidableEq.{1} Module] [inst_1 : DecidableEq.{1} Parse] [inst_2 : DecidableEq.{1} Green]
  (pool : YulangClosure.NativeSnapshotOwnerR34.RetainedPool history Module Parse Green)
  (hir : YulangClosure.NativeSnapshotOwnerR34.HirData Module Parse Green)
  (old : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (familyIndex operationIndex : Nat),
  Eq.{1}
    (YulangClosure.NativeCallbackCoordinatesR33.decodeOperationCoordinate
      (YulangClosure.NativeSnapshotOwnerR34.issuedSnapshot (YulangClosure.NativeSnapshotOwnerR34.allocate pool hir)
        (YulangClosure.NativeSnapshotOwnerR34.retainOwner old))
      (YulangClosure.NativeSnapshotOwnerR34.issuedOperation (YulangClosure.NativeSnapshotOwnerR34.freshOwner history)
        familyIndex operationIndex))
    none.{0} :=
⋯
'YulangClosure.NativeSnapshotOwnerR34.fresh_operation_rejected_by_retained' depends on axioms: [propext, sorryAx.{u}]
theorem YulangClosure.NativeSnapshotOwnerR34.owner_family_exact : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Module Parse Green : Type}
  (pool : YulangClosure.NativeSnapshotOwnerR34.RetainedPool history Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history)
  (q :
    YulangClosure.NativeCallbackCoordinatesR33.FamilyCoordinate (YulangClosure.NativeSnapshotOwnerR34.OwnerId history))
  {family : YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green},
  Eq.{1}
      (YulangClosure.NativeCallbackCoordinatesR33.decodeFamilyCoordinate
        (YulangClosure.NativeSnapshotOwnerR34.issuedSnapshot pool owner) q)
      (some.{0} family) →
    Eq.{1} q.snapshotToken (YulangClosure.NativeSnapshotOwnerR34.ownerToken owner) ∧
      Exists.{0} fun bound =>
        Eq.{1} family (getElem.{0, 0, 0} (pool.data owner.hirOwner).effects q.effectIndex bound).identity :=
⋯
'YulangClosure.NativeSnapshotOwnerR34.owner_family_exact' depends on axioms: [propext, sorryAx.{u}]
theorem YulangClosure.NativeSnapshotOwnerR34.owner_operation_exact : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Module Parse Green : Type}
  [inst : DecidableEq.{1} Module] [inst_1 : DecidableEq.{1} Parse] [inst_2 : DecidableEq.{1} Green]
  (pool : YulangClosure.NativeSnapshotOwnerR34.RetainedPool history Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history)
  (q :
    YulangClosure.NativeCallbackCoordinatesR33.OperationCoordinate
      (YulangClosure.NativeSnapshotOwnerR34.OwnerId history))
  {operation : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green},
  Eq.{1}
      (YulangClosure.NativeCallbackCoordinatesR33.decodeOperationCoordinate
        (YulangClosure.NativeSnapshotOwnerR34.issuedSnapshot pool owner) q)
      (some.{0} operation) →
    Eq.{1} q.family.snapshotToken (YulangClosure.NativeSnapshotOwnerR34.ownerToken owner) ∧
      Exists.{1} fun effect =>
        (Exists.{0} fun bound =>
            Eq.{1} (getElem.{0, 0, 0} (pool.data owner.hirOwner).effects q.family.effectIndex bound) effect) ∧
          (Exists.{0} fun bound => Eq.{1} (getElem.{0, 0, 0} effect.operations q.operationIndex bound) operation) ∧
            Eq.{1} operation.family effect.identity :=
⋯
'YulangClosure.NativeSnapshotOwnerR34.owner_operation_exact' depends on axioms: [propext, sorryAx.{u}]
@[defeq] theorem YulangClosure.NativeSnapshotOwnerR34.clone_preserves_translation : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Module Parse Green : Type}
  [inst : DecidableEq.{1} Module] [inst_1 : DecidableEq.{1} Parse] [inst_2 : DecidableEq.{1} Green]
  (pool : YulangClosure.NativeSnapshotOwnerR34.RetainedPool history Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history)
  (request consumer arm :
    YulangClosure.NativeCallbackCoordinatesR33.OperationCoordinate
      (YulangClosure.NativeSnapshotOwnerR34.OwnerId history))
  (row :
    List.{0}
      (YulangClosure.NativeCallbackCoordinatesR33.FamilyCoordinate
        (YulangClosure.NativeSnapshotOwnerR34.OwnerId history))),
  Eq.{1}
    (YulangClosure.NativeCallbackCoordinatesR33.translateCoordinates
      (YulangClosure.NativeSnapshotOwnerR34.issuedSnapshot pool (YulangClosure.NativeSnapshotOwnerR34.cloneOwner owner))
      request consumer arm row)
    (YulangClosure.NativeCallbackCoordinatesR33.translateCoordinates
      (YulangClosure.NativeSnapshotOwnerR34.issuedSnapshot pool owner) request consumer arm row) :=
⋯
'YulangClosure.NativeSnapshotOwnerR34.clone_preserves_translation' depends on axioms: [propext, sorryAx.{u}]
theorem YulangClosure.NativeSnapshotOwnerR34.owner_complete_row : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Module Parse Green : Type}
  [inst : DecidableEq.{1} Module] [inst_1 : DecidableEq.{1} Parse] [inst_2 : DecidableEq.{1} Green]
  (pool : YulangClosure.NativeSnapshotOwnerR34.RetainedPool history Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history)
  (row :
    List.{0}
      (YulangClosure.NativeCallbackCoordinatesR33.FamilyCoordinate
        (YulangClosure.NativeSnapshotOwnerR34.OwnerId history)))
  {families : List.{0} (YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green)},
  Eq.{1}
      (YulangClosure.NativeCallbackCoordinatesR33.translatePermissionRow
        (YulangClosure.NativeSnapshotOwnerR34.issuedSnapshot pool owner) row)
      (some.{0} families) →
    Eq.{1} families (pool.data owner.hirOwner).permissionRow ∧
      Eq.{1}
          (YulangClosure.NativeCallbackCoordinatesR33.decodeFamilyRow
            (YulangClosure.NativeSnapshotOwnerR34.issuedSnapshot pool owner) row)
          (some.{0} families) ∧
        Eq.{1} (List.length.{0} families) (List.length.{0} row) :=
⋯
'YulangClosure.NativeSnapshotOwnerR34.owner_complete_row' depends on axioms: [propext, sorryAx.{u}, Quot.sound.{u}]
theorem YulangClosure.NativeSnapshotOwnerR34.owner_translation_to_r32 : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Module Parse Green : Type}
  [inst : DecidableEq.{1} Module] [inst_1 : DecidableEq.{1} Parse] [inst_2 : DecidableEq.{1} Green]
  (pool : YulangClosure.NativeSnapshotOwnerR34.RetainedPool history Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history)
  (request consumer arm :
    YulangClosure.NativeCallbackCoordinatesR33.OperationCoordinate
      (YulangClosure.NativeSnapshotOwnerR34.OwnerId history))
  (row :
    List.{0}
      (YulangClosure.NativeCallbackCoordinatesR33.FamilyCoordinate
        (YulangClosure.NativeSnapshotOwnerR34.OwnerId history)))
  {out : YulangClosure.NativeCallbackCoordinatesR33.DecodedCoordinates Module Parse Green},
  Eq.{1}
      (YulangClosure.NativeCallbackCoordinatesR33.translateCoordinates
        (YulangClosure.NativeSnapshotOwnerR34.issuedSnapshot pool owner) request consumer arm row)
      (some.{0} out) →
    have table :=
      YulangClosure.NativeCallbackGrantBridgeR32.coveringTable out.request out.consumer out.arm out.families;
    Eq.{1} out.families (pool.data owner.hirOwner).permissionRow ∧
      Eq.{1} (List.length.{0} out.families) (List.length.{0} row) ∧
        Eq.{1} request.family.snapshotToken (YulangClosure.NativeSnapshotOwnerR34.ownerToken owner) ∧
          Eq.{1} consumer.family.snapshotToken (YulangClosure.NativeSnapshotOwnerR34.ownerToken owner) ∧
            Eq.{1} arm.family.snapshotToken (YulangClosure.NativeSnapshotOwnerR34.ownerToken owner) ∧
              (Exists.{1} fun effect =>
                  Membership.mem.{0, 0} (pool.data owner.hirOwner).effects effect ∧
                    Membership.mem.{0, 0} effect.operations out.request ∧ Eq.{1} out.request.family effect.identity) ∧
                (Exists.{1} fun effect =>
                    Membership.mem.{0, 0} (pool.data owner.hirOwner).effects effect ∧
                      Membership.mem.{0, 0} effect.operations out.consumer ∧
                        Eq.{1} out.consumer.family effect.identity) ∧
                  (Exists.{1} fun effect =>
                      Membership.mem.{0, 0} (pool.data owner.hirOwner).effects effect ∧
                        Membership.mem.{0, 0} effect.operations out.arm ∧ Eq.{1} out.arm.family effect.identity) ∧
                    (∀ (op : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green),
                        Membership.mem.{0, 0}
                            (List.cons.{0} out.request
                              (List.cons.{0} out.consumer (List.cons.{0} out.arm List.nil.{0})))
                            op →
                          Membership.mem.{0, 0} table.operations op) ∧
                      (∀ (family : YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green),
                          Membership.mem.{0, 0} (pool.data owner.hirOwner).permissionRow family →
                            Membership.mem.{0, 0} table.families family) ∧
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
                                Membership.mem.{0, 0} (pool.data owner.hirOwner).permissionRow family →
                                  Eq.{1} (getElem?.{0, 0, 0} table.families (List.idxOf.{0} family table.families))
                                      (some.{0} family) ∧
                                    (Membership.mem.{0, 0}
                                        (List.map.{0, 0} (fun a => List.idxOf.{0} a table.families) out.families)
                                        (List.idxOf.{0} family table.families) ↔
                                      Membership.mem.{0, 0} out.families family) :=
⋯
'YulangClosure.NativeSnapshotOwnerR34.owner_translation_to_r32' depends on axioms: [propext,
 sorryAx.{u},
 Quot.sound.{u}]

STDERR:
```

## Audit attempt 2

Same pinned bwrap command and all75 theorem audits; owner identity decidable equality unfolds its exact recursive target. Exit 0; subprocess seconds 3.1402963590007857.

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
@[defeq] theorem YulangClosure.NativeSnapshotOwnerR34.clone_preserves_token : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory}
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history),
  Eq.{1} (YulangClosure.NativeSnapshotOwnerR34.ownerToken (YulangClosure.NativeSnapshotOwnerR34.cloneOwner owner))
    (YulangClosure.NativeSnapshotOwnerR34.ownerToken owner) :=
⋯
'YulangClosure.NativeSnapshotOwnerR34.clone_preserves_token' does not depend on any axioms
@[defeq] theorem YulangClosure.NativeSnapshotOwnerR34.clone_preserves_snapshot : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Module Parse Green : Type}
  (pool : YulangClosure.NativeSnapshotOwnerR34.RetainedPool history Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history),
  Eq.{1}
    (YulangClosure.NativeSnapshotOwnerR34.issuedSnapshot pool (YulangClosure.NativeSnapshotOwnerR34.cloneOwner owner))
    (YulangClosure.NativeSnapshotOwnerR34.issuedSnapshot pool owner) :=
⋯
'YulangClosure.NativeSnapshotOwnerR34.clone_preserves_snapshot' does not depend on any axioms
theorem YulangClosure.NativeSnapshotOwnerR34.issued_snapshot_exact : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Module Parse Green : Type}
  (pool : YulangClosure.NativeSnapshotOwnerR34.RetainedPool history Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history),
  Eq.{1} (YulangClosure.NativeSnapshotOwnerR34.issuedSnapshot pool owner).token
      (YulangClosure.NativeSnapshotOwnerR34.ownerToken owner) ∧
    Eq.{1} (YulangClosure.NativeSnapshotOwnerR34.issuedSnapshot pool owner).effects (pool.data owner.hirOwner).effects ∧
      Eq.{1} (YulangClosure.NativeSnapshotOwnerR34.issuedSnapshot pool owner).permissionRow
        (pool.data owner.hirOwner).permissionRow :=
⋯
'YulangClosure.NativeSnapshotOwnerR34.issued_snapshot_exact' does not depend on any axioms
@[defeq] theorem YulangClosure.NativeSnapshotOwnerR34.allocation_preserves_retained : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Module Parse Green : Type}
  (pool : YulangClosure.NativeSnapshotOwnerR34.RetainedPool history Module Parse Green)
  (hir : YulangClosure.NativeSnapshotOwnerR34.HirData Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history),
  Eq.{1}
    ((YulangClosure.NativeSnapshotOwnerR34.allocate pool hir).data
      (YulangClosure.NativeSnapshotOwnerR34.ownerToken (YulangClosure.NativeSnapshotOwnerR34.retainOwner owner)))
    (pool.data owner.hirOwner) :=
⋯
'YulangClosure.NativeSnapshotOwnerR34.allocation_preserves_retained' does not depend on any axioms
@[defeq] theorem YulangClosure.NativeSnapshotOwnerR34.allocation_binds_fresh : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Module Parse Green : Type}
  (pool : YulangClosure.NativeSnapshotOwnerR34.RetainedPool history Module Parse Green)
  (hir : YulangClosure.NativeSnapshotOwnerR34.HirData Module Parse Green),
  Eq.{1}
    ((YulangClosure.NativeSnapshotOwnerR34.allocate pool hir).data
      (YulangClosure.NativeSnapshotOwnerR34.ownerToken (YulangClosure.NativeSnapshotOwnerR34.freshOwner history)))
    hir :=
⋯
'YulangClosure.NativeSnapshotOwnerR34.allocation_binds_fresh' does not depend on any axioms
theorem YulangClosure.NativeSnapshotOwnerR34.fresh_owner_foreign : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory}
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history),
  Ne.{1} (YulangClosure.NativeSnapshotOwnerR34.ownerToken (YulangClosure.NativeSnapshotOwnerR34.retainOwner owner))
    (YulangClosure.NativeSnapshotOwnerR34.ownerToken (YulangClosure.NativeSnapshotOwnerR34.freshOwner history)) :=
⋯
'YulangClosure.NativeSnapshotOwnerR34.fresh_owner_foreign' does not depend on any axioms
theorem YulangClosure.NativeSnapshotOwnerR34.equal_payload_allocations_foreign : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Module Parse Green : Type}
  (pool : YulangClosure.NativeSnapshotOwnerR34.RetainedPool history Module Parse Green)
  (hir : YulangClosure.NativeSnapshotOwnerR34.HirData Module Parse Green),
  have extended :=
    YulangClosure.NativeSnapshotOwnerR34.allocate (YulangClosure.NativeSnapshotOwnerR34.allocate pool hir) hir;
  have retained :=
    YulangClosure.NativeSnapshotOwnerR34.retainOwner (YulangClosure.NativeSnapshotOwnerR34.freshOwner history);
  have fresh := YulangClosure.NativeSnapshotOwnerR34.freshOwner history.allocated;
  Eq.{1} (extended.data (YulangClosure.NativeSnapshotOwnerR34.ownerToken retained))
      (extended.data (YulangClosure.NativeSnapshotOwnerR34.ownerToken fresh)) ∧
    Ne.{1} (YulangClosure.NativeSnapshotOwnerR34.ownerToken retained)
      (YulangClosure.NativeSnapshotOwnerR34.ownerToken fresh) :=
⋯
'YulangClosure.NativeSnapshotOwnerR34.equal_payload_allocations_foreign' does not depend on any axioms
theorem YulangClosure.NativeSnapshotOwnerR34.foreign_family_rejected : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Module Parse Green : Type}
  (pool : YulangClosure.NativeSnapshotOwnerR34.RetainedPool history Module Parse Green)
  (hir : YulangClosure.NativeSnapshotOwnerR34.HirData Module Parse Green)
  (old : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (index : Nat),
  Eq.{1}
    (YulangClosure.NativeCallbackCoordinatesR33.decodeFamilyCoordinate
      (YulangClosure.NativeSnapshotOwnerR34.issuedSnapshot (YulangClosure.NativeSnapshotOwnerR34.allocate pool hir)
        (YulangClosure.NativeSnapshotOwnerR34.freshOwner history))
      (YulangClosure.NativeSnapshotOwnerR34.issuedFamily (YulangClosure.NativeSnapshotOwnerR34.retainOwner old) index))
    none.{0} :=
⋯
'YulangClosure.NativeSnapshotOwnerR34.foreign_family_rejected' depends on axioms: [propext]
theorem YulangClosure.NativeSnapshotOwnerR34.foreign_operation_rejected : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Module Parse Green : Type}
  [inst : DecidableEq.{1} Module] [inst_1 : DecidableEq.{1} Parse] [inst_2 : DecidableEq.{1} Green]
  (pool : YulangClosure.NativeSnapshotOwnerR34.RetainedPool history Module Parse Green)
  (hir : YulangClosure.NativeSnapshotOwnerR34.HirData Module Parse Green)
  (old : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (familyIndex operationIndex : Nat),
  Eq.{1}
    (YulangClosure.NativeCallbackCoordinatesR33.decodeOperationCoordinate
      (YulangClosure.NativeSnapshotOwnerR34.issuedSnapshot (YulangClosure.NativeSnapshotOwnerR34.allocate pool hir)
        (YulangClosure.NativeSnapshotOwnerR34.freshOwner history))
      (YulangClosure.NativeSnapshotOwnerR34.issuedOperation (YulangClosure.NativeSnapshotOwnerR34.retainOwner old)
        familyIndex operationIndex))
    none.{0} :=
⋯
'YulangClosure.NativeSnapshotOwnerR34.foreign_operation_rejected' depends on axioms: [propext]
theorem YulangClosure.NativeSnapshotOwnerR34.fresh_family_rejected_by_retained : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Module Parse Green : Type}
  (pool : YulangClosure.NativeSnapshotOwnerR34.RetainedPool history Module Parse Green)
  (hir : YulangClosure.NativeSnapshotOwnerR34.HirData Module Parse Green)
  (old : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (index : Nat),
  Eq.{1}
    (YulangClosure.NativeCallbackCoordinatesR33.decodeFamilyCoordinate
      (YulangClosure.NativeSnapshotOwnerR34.issuedSnapshot (YulangClosure.NativeSnapshotOwnerR34.allocate pool hir)
        (YulangClosure.NativeSnapshotOwnerR34.retainOwner old))
      (YulangClosure.NativeSnapshotOwnerR34.issuedFamily (YulangClosure.NativeSnapshotOwnerR34.freshOwner history)
        index))
    none.{0} :=
⋯
'YulangClosure.NativeSnapshotOwnerR34.fresh_family_rejected_by_retained' depends on axioms: [propext]
theorem YulangClosure.NativeSnapshotOwnerR34.fresh_operation_rejected_by_retained : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Module Parse Green : Type}
  [inst : DecidableEq.{1} Module] [inst_1 : DecidableEq.{1} Parse] [inst_2 : DecidableEq.{1} Green]
  (pool : YulangClosure.NativeSnapshotOwnerR34.RetainedPool history Module Parse Green)
  (hir : YulangClosure.NativeSnapshotOwnerR34.HirData Module Parse Green)
  (old : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (familyIndex operationIndex : Nat),
  Eq.{1}
    (YulangClosure.NativeCallbackCoordinatesR33.decodeOperationCoordinate
      (YulangClosure.NativeSnapshotOwnerR34.issuedSnapshot (YulangClosure.NativeSnapshotOwnerR34.allocate pool hir)
        (YulangClosure.NativeSnapshotOwnerR34.retainOwner old))
      (YulangClosure.NativeSnapshotOwnerR34.issuedOperation (YulangClosure.NativeSnapshotOwnerR34.freshOwner history)
        familyIndex operationIndex))
    none.{0} :=
⋯
'YulangClosure.NativeSnapshotOwnerR34.fresh_operation_rejected_by_retained' depends on axioms: [propext]
theorem YulangClosure.NativeSnapshotOwnerR34.owner_family_exact : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Module Parse Green : Type}
  (pool : YulangClosure.NativeSnapshotOwnerR34.RetainedPool history Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history)
  (q :
    YulangClosure.NativeCallbackCoordinatesR33.FamilyCoordinate (YulangClosure.NativeSnapshotOwnerR34.OwnerId history))
  {family : YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green},
  Eq.{1}
      (YulangClosure.NativeCallbackCoordinatesR33.decodeFamilyCoordinate
        (YulangClosure.NativeSnapshotOwnerR34.issuedSnapshot pool owner) q)
      (some.{0} family) →
    Eq.{1} q.snapshotToken (YulangClosure.NativeSnapshotOwnerR34.ownerToken owner) ∧
      Exists.{0} fun bound =>
        Eq.{1} family (getElem.{0, 0, 0} (pool.data owner.hirOwner).effects q.effectIndex bound).identity :=
⋯
'YulangClosure.NativeSnapshotOwnerR34.owner_family_exact' depends on axioms: [propext]
theorem YulangClosure.NativeSnapshotOwnerR34.owner_operation_exact : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Module Parse Green : Type}
  [inst : DecidableEq.{1} Module] [inst_1 : DecidableEq.{1} Parse] [inst_2 : DecidableEq.{1} Green]
  (pool : YulangClosure.NativeSnapshotOwnerR34.RetainedPool history Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history)
  (q :
    YulangClosure.NativeCallbackCoordinatesR33.OperationCoordinate
      (YulangClosure.NativeSnapshotOwnerR34.OwnerId history))
  {operation : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green},
  Eq.{1}
      (YulangClosure.NativeCallbackCoordinatesR33.decodeOperationCoordinate
        (YulangClosure.NativeSnapshotOwnerR34.issuedSnapshot pool owner) q)
      (some.{0} operation) →
    Eq.{1} q.family.snapshotToken (YulangClosure.NativeSnapshotOwnerR34.ownerToken owner) ∧
      Exists.{1} fun effect =>
        (Exists.{0} fun bound =>
            Eq.{1} (getElem.{0, 0, 0} (pool.data owner.hirOwner).effects q.family.effectIndex bound) effect) ∧
          (Exists.{0} fun bound => Eq.{1} (getElem.{0, 0, 0} effect.operations q.operationIndex bound) operation) ∧
            Eq.{1} operation.family effect.identity :=
⋯
'YulangClosure.NativeSnapshotOwnerR34.owner_operation_exact' depends on axioms: [propext]
@[defeq] theorem YulangClosure.NativeSnapshotOwnerR34.clone_preserves_translation : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Module Parse Green : Type}
  [inst : DecidableEq.{1} Module] [inst_1 : DecidableEq.{1} Parse] [inst_2 : DecidableEq.{1} Green]
  (pool : YulangClosure.NativeSnapshotOwnerR34.RetainedPool history Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history)
  (request consumer arm :
    YulangClosure.NativeCallbackCoordinatesR33.OperationCoordinate
      (YulangClosure.NativeSnapshotOwnerR34.OwnerId history))
  (row :
    List.{0}
      (YulangClosure.NativeCallbackCoordinatesR33.FamilyCoordinate
        (YulangClosure.NativeSnapshotOwnerR34.OwnerId history))),
  Eq.{1}
    (YulangClosure.NativeCallbackCoordinatesR33.translateCoordinates
      (YulangClosure.NativeSnapshotOwnerR34.issuedSnapshot pool (YulangClosure.NativeSnapshotOwnerR34.cloneOwner owner))
      request consumer arm row)
    (YulangClosure.NativeCallbackCoordinatesR33.translateCoordinates
      (YulangClosure.NativeSnapshotOwnerR34.issuedSnapshot pool owner) request consumer arm row) :=
⋯
'YulangClosure.NativeSnapshotOwnerR34.clone_preserves_translation' depends on axioms: [propext]
theorem YulangClosure.NativeSnapshotOwnerR34.owner_complete_row : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Module Parse Green : Type}
  [inst : DecidableEq.{1} Module] [inst_1 : DecidableEq.{1} Parse] [inst_2 : DecidableEq.{1} Green]
  (pool : YulangClosure.NativeSnapshotOwnerR34.RetainedPool history Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history)
  (row :
    List.{0}
      (YulangClosure.NativeCallbackCoordinatesR33.FamilyCoordinate
        (YulangClosure.NativeSnapshotOwnerR34.OwnerId history)))
  {families : List.{0} (YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green)},
  Eq.{1}
      (YulangClosure.NativeCallbackCoordinatesR33.translatePermissionRow
        (YulangClosure.NativeSnapshotOwnerR34.issuedSnapshot pool owner) row)
      (some.{0} families) →
    Eq.{1} families (pool.data owner.hirOwner).permissionRow ∧
      Eq.{1}
          (YulangClosure.NativeCallbackCoordinatesR33.decodeFamilyRow
            (YulangClosure.NativeSnapshotOwnerR34.issuedSnapshot pool owner) row)
          (some.{0} families) ∧
        Eq.{1} (List.length.{0} families) (List.length.{0} row) :=
⋯
'YulangClosure.NativeSnapshotOwnerR34.owner_complete_row' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.NativeSnapshotOwnerR34.owner_translation_to_r32 : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Module Parse Green : Type}
  [inst : DecidableEq.{1} Module] [inst_1 : DecidableEq.{1} Parse] [inst_2 : DecidableEq.{1} Green]
  (pool : YulangClosure.NativeSnapshotOwnerR34.RetainedPool history Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history)
  (request consumer arm :
    YulangClosure.NativeCallbackCoordinatesR33.OperationCoordinate
      (YulangClosure.NativeSnapshotOwnerR34.OwnerId history))
  (row :
    List.{0}
      (YulangClosure.NativeCallbackCoordinatesR33.FamilyCoordinate
        (YulangClosure.NativeSnapshotOwnerR34.OwnerId history)))
  {out : YulangClosure.NativeCallbackCoordinatesR33.DecodedCoordinates Module Parse Green},
  Eq.{1}
      (YulangClosure.NativeCallbackCoordinatesR33.translateCoordinates
        (YulangClosure.NativeSnapshotOwnerR34.issuedSnapshot pool owner) request consumer arm row)
      (some.{0} out) →
    have table :=
      YulangClosure.NativeCallbackGrantBridgeR32.coveringTable out.request out.consumer out.arm out.families;
    Eq.{1} out.families (pool.data owner.hirOwner).permissionRow ∧
      Eq.{1} (List.length.{0} out.families) (List.length.{0} row) ∧
        Eq.{1} request.family.snapshotToken (YulangClosure.NativeSnapshotOwnerR34.ownerToken owner) ∧
          Eq.{1} consumer.family.snapshotToken (YulangClosure.NativeSnapshotOwnerR34.ownerToken owner) ∧
            Eq.{1} arm.family.snapshotToken (YulangClosure.NativeSnapshotOwnerR34.ownerToken owner) ∧
              (Exists.{1} fun effect =>
                  Membership.mem.{0, 0} (pool.data owner.hirOwner).effects effect ∧
                    Membership.mem.{0, 0} effect.operations out.request ∧ Eq.{1} out.request.family effect.identity) ∧
                (Exists.{1} fun effect =>
                    Membership.mem.{0, 0} (pool.data owner.hirOwner).effects effect ∧
                      Membership.mem.{0, 0} effect.operations out.consumer ∧
                        Eq.{1} out.consumer.family effect.identity) ∧
                  (Exists.{1} fun effect =>
                      Membership.mem.{0, 0} (pool.data owner.hirOwner).effects effect ∧
                        Membership.mem.{0, 0} effect.operations out.arm ∧ Eq.{1} out.arm.family effect.identity) ∧
                    (∀ (op : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green),
                        Membership.mem.{0, 0}
                            (List.cons.{0} out.request
                              (List.cons.{0} out.consumer (List.cons.{0} out.arm List.nil.{0})))
                            op →
                          Membership.mem.{0, 0} table.operations op) ∧
                      (∀ (family : YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green),
                          Membership.mem.{0, 0} (pool.data owner.hirOwner).permissionRow family →
                            Membership.mem.{0, 0} table.families family) ∧
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
                                Membership.mem.{0, 0} (pool.data owner.hirOwner).permissionRow family →
                                  Eq.{1} (getElem?.{0, 0, 0} table.families (List.idxOf.{0} family table.families))
                                      (some.{0} family) ∧
                                    (Membership.mem.{0, 0}
                                        (List.map.{0, 0} (fun a => List.idxOf.{0} a table.families) out.families)
                                        (List.idxOf.{0} family table.families) ↔
                                      Membership.mem.{0, 0} out.families family) :=
⋯
'YulangClosure.NativeSnapshotOwnerR34.owner_translation_to_r32' depends on axioms: [propext, Quot.sound.{u}]

STDERR:
```

## Audit attempt 3 — final surface

Same pinned bwrap command; all76 theorem types and complete axioms. Added equality-preservation under retained-name embedding. Exit 0; subprocess seconds 3.5388538429979235.

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
theorem YulangClosure.NativeSnapshotOwnerR34.retention_preserves_token_equality : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory}
  (left right : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history),
  Eq.{1} (YulangClosure.NativeSnapshotOwnerR34.ownerToken (YulangClosure.NativeSnapshotOwnerR34.retainOwner left))
      (YulangClosure.NativeSnapshotOwnerR34.ownerToken (YulangClosure.NativeSnapshotOwnerR34.retainOwner right)) ↔
    Eq.{1} (YulangClosure.NativeSnapshotOwnerR34.ownerToken left)
      (YulangClosure.NativeSnapshotOwnerR34.ownerToken right) :=
⋯
'YulangClosure.NativeSnapshotOwnerR34.retention_preserves_token_equality' does not depend on any axioms
@[defeq] theorem YulangClosure.NativeSnapshotOwnerR34.clone_preserves_token : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory}
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history),
  Eq.{1} (YulangClosure.NativeSnapshotOwnerR34.ownerToken (YulangClosure.NativeSnapshotOwnerR34.cloneOwner owner))
    (YulangClosure.NativeSnapshotOwnerR34.ownerToken owner) :=
⋯
'YulangClosure.NativeSnapshotOwnerR34.clone_preserves_token' does not depend on any axioms
@[defeq] theorem YulangClosure.NativeSnapshotOwnerR34.clone_preserves_snapshot : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Module Parse Green : Type}
  (pool : YulangClosure.NativeSnapshotOwnerR34.RetainedPool history Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history),
  Eq.{1}
    (YulangClosure.NativeSnapshotOwnerR34.issuedSnapshot pool (YulangClosure.NativeSnapshotOwnerR34.cloneOwner owner))
    (YulangClosure.NativeSnapshotOwnerR34.issuedSnapshot pool owner) :=
⋯
'YulangClosure.NativeSnapshotOwnerR34.clone_preserves_snapshot' does not depend on any axioms
theorem YulangClosure.NativeSnapshotOwnerR34.issued_snapshot_exact : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Module Parse Green : Type}
  (pool : YulangClosure.NativeSnapshotOwnerR34.RetainedPool history Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history),
  Eq.{1} (YulangClosure.NativeSnapshotOwnerR34.issuedSnapshot pool owner).token
      (YulangClosure.NativeSnapshotOwnerR34.ownerToken owner) ∧
    Eq.{1} (YulangClosure.NativeSnapshotOwnerR34.issuedSnapshot pool owner).effects (pool.data owner.hirOwner).effects ∧
      Eq.{1} (YulangClosure.NativeSnapshotOwnerR34.issuedSnapshot pool owner).permissionRow
        (pool.data owner.hirOwner).permissionRow :=
⋯
'YulangClosure.NativeSnapshotOwnerR34.issued_snapshot_exact' does not depend on any axioms
@[defeq] theorem YulangClosure.NativeSnapshotOwnerR34.allocation_preserves_retained : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Module Parse Green : Type}
  (pool : YulangClosure.NativeSnapshotOwnerR34.RetainedPool history Module Parse Green)
  (hir : YulangClosure.NativeSnapshotOwnerR34.HirData Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history),
  Eq.{1}
    ((YulangClosure.NativeSnapshotOwnerR34.allocate pool hir).data
      (YulangClosure.NativeSnapshotOwnerR34.ownerToken (YulangClosure.NativeSnapshotOwnerR34.retainOwner owner)))
    (pool.data owner.hirOwner) :=
⋯
'YulangClosure.NativeSnapshotOwnerR34.allocation_preserves_retained' does not depend on any axioms
@[defeq] theorem YulangClosure.NativeSnapshotOwnerR34.allocation_binds_fresh : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Module Parse Green : Type}
  (pool : YulangClosure.NativeSnapshotOwnerR34.RetainedPool history Module Parse Green)
  (hir : YulangClosure.NativeSnapshotOwnerR34.HirData Module Parse Green),
  Eq.{1}
    ((YulangClosure.NativeSnapshotOwnerR34.allocate pool hir).data
      (YulangClosure.NativeSnapshotOwnerR34.ownerToken (YulangClosure.NativeSnapshotOwnerR34.freshOwner history)))
    hir :=
⋯
'YulangClosure.NativeSnapshotOwnerR34.allocation_binds_fresh' does not depend on any axioms
theorem YulangClosure.NativeSnapshotOwnerR34.fresh_owner_foreign : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory}
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history),
  Ne.{1} (YulangClosure.NativeSnapshotOwnerR34.ownerToken (YulangClosure.NativeSnapshotOwnerR34.retainOwner owner))
    (YulangClosure.NativeSnapshotOwnerR34.ownerToken (YulangClosure.NativeSnapshotOwnerR34.freshOwner history)) :=
⋯
'YulangClosure.NativeSnapshotOwnerR34.fresh_owner_foreign' does not depend on any axioms
theorem YulangClosure.NativeSnapshotOwnerR34.equal_payload_allocations_foreign : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Module Parse Green : Type}
  (pool : YulangClosure.NativeSnapshotOwnerR34.RetainedPool history Module Parse Green)
  (hir : YulangClosure.NativeSnapshotOwnerR34.HirData Module Parse Green),
  have extended :=
    YulangClosure.NativeSnapshotOwnerR34.allocate (YulangClosure.NativeSnapshotOwnerR34.allocate pool hir) hir;
  have retained :=
    YulangClosure.NativeSnapshotOwnerR34.retainOwner (YulangClosure.NativeSnapshotOwnerR34.freshOwner history);
  have fresh := YulangClosure.NativeSnapshotOwnerR34.freshOwner history.allocated;
  Eq.{1} (extended.data (YulangClosure.NativeSnapshotOwnerR34.ownerToken retained))
      (extended.data (YulangClosure.NativeSnapshotOwnerR34.ownerToken fresh)) ∧
    Ne.{1} (YulangClosure.NativeSnapshotOwnerR34.ownerToken retained)
      (YulangClosure.NativeSnapshotOwnerR34.ownerToken fresh) :=
⋯
'YulangClosure.NativeSnapshotOwnerR34.equal_payload_allocations_foreign' does not depend on any axioms
theorem YulangClosure.NativeSnapshotOwnerR34.foreign_family_rejected : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Module Parse Green : Type}
  (pool : YulangClosure.NativeSnapshotOwnerR34.RetainedPool history Module Parse Green)
  (hir : YulangClosure.NativeSnapshotOwnerR34.HirData Module Parse Green)
  (old : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (index : Nat),
  Eq.{1}
    (YulangClosure.NativeCallbackCoordinatesR33.decodeFamilyCoordinate
      (YulangClosure.NativeSnapshotOwnerR34.issuedSnapshot (YulangClosure.NativeSnapshotOwnerR34.allocate pool hir)
        (YulangClosure.NativeSnapshotOwnerR34.freshOwner history))
      (YulangClosure.NativeSnapshotOwnerR34.issuedFamily (YulangClosure.NativeSnapshotOwnerR34.retainOwner old) index))
    none.{0} :=
⋯
'YulangClosure.NativeSnapshotOwnerR34.foreign_family_rejected' depends on axioms: [propext]
theorem YulangClosure.NativeSnapshotOwnerR34.foreign_operation_rejected : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Module Parse Green : Type}
  [inst : DecidableEq.{1} Module] [inst_1 : DecidableEq.{1} Parse] [inst_2 : DecidableEq.{1} Green]
  (pool : YulangClosure.NativeSnapshotOwnerR34.RetainedPool history Module Parse Green)
  (hir : YulangClosure.NativeSnapshotOwnerR34.HirData Module Parse Green)
  (old : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (familyIndex operationIndex : Nat),
  Eq.{1}
    (YulangClosure.NativeCallbackCoordinatesR33.decodeOperationCoordinate
      (YulangClosure.NativeSnapshotOwnerR34.issuedSnapshot (YulangClosure.NativeSnapshotOwnerR34.allocate pool hir)
        (YulangClosure.NativeSnapshotOwnerR34.freshOwner history))
      (YulangClosure.NativeSnapshotOwnerR34.issuedOperation (YulangClosure.NativeSnapshotOwnerR34.retainOwner old)
        familyIndex operationIndex))
    none.{0} :=
⋯
'YulangClosure.NativeSnapshotOwnerR34.foreign_operation_rejected' depends on axioms: [propext]
theorem YulangClosure.NativeSnapshotOwnerR34.fresh_family_rejected_by_retained : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Module Parse Green : Type}
  (pool : YulangClosure.NativeSnapshotOwnerR34.RetainedPool history Module Parse Green)
  (hir : YulangClosure.NativeSnapshotOwnerR34.HirData Module Parse Green)
  (old : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (index : Nat),
  Eq.{1}
    (YulangClosure.NativeCallbackCoordinatesR33.decodeFamilyCoordinate
      (YulangClosure.NativeSnapshotOwnerR34.issuedSnapshot (YulangClosure.NativeSnapshotOwnerR34.allocate pool hir)
        (YulangClosure.NativeSnapshotOwnerR34.retainOwner old))
      (YulangClosure.NativeSnapshotOwnerR34.issuedFamily (YulangClosure.NativeSnapshotOwnerR34.freshOwner history)
        index))
    none.{0} :=
⋯
'YulangClosure.NativeSnapshotOwnerR34.fresh_family_rejected_by_retained' depends on axioms: [propext]
theorem YulangClosure.NativeSnapshotOwnerR34.fresh_operation_rejected_by_retained : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Module Parse Green : Type}
  [inst : DecidableEq.{1} Module] [inst_1 : DecidableEq.{1} Parse] [inst_2 : DecidableEq.{1} Green]
  (pool : YulangClosure.NativeSnapshotOwnerR34.RetainedPool history Module Parse Green)
  (hir : YulangClosure.NativeSnapshotOwnerR34.HirData Module Parse Green)
  (old : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (familyIndex operationIndex : Nat),
  Eq.{1}
    (YulangClosure.NativeCallbackCoordinatesR33.decodeOperationCoordinate
      (YulangClosure.NativeSnapshotOwnerR34.issuedSnapshot (YulangClosure.NativeSnapshotOwnerR34.allocate pool hir)
        (YulangClosure.NativeSnapshotOwnerR34.retainOwner old))
      (YulangClosure.NativeSnapshotOwnerR34.issuedOperation (YulangClosure.NativeSnapshotOwnerR34.freshOwner history)
        familyIndex operationIndex))
    none.{0} :=
⋯
'YulangClosure.NativeSnapshotOwnerR34.fresh_operation_rejected_by_retained' depends on axioms: [propext]
theorem YulangClosure.NativeSnapshotOwnerR34.owner_family_exact : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Module Parse Green : Type}
  (pool : YulangClosure.NativeSnapshotOwnerR34.RetainedPool history Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history)
  (q :
    YulangClosure.NativeCallbackCoordinatesR33.FamilyCoordinate (YulangClosure.NativeSnapshotOwnerR34.OwnerId history))
  {family : YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green},
  Eq.{1}
      (YulangClosure.NativeCallbackCoordinatesR33.decodeFamilyCoordinate
        (YulangClosure.NativeSnapshotOwnerR34.issuedSnapshot pool owner) q)
      (some.{0} family) →
    Eq.{1} q.snapshotToken (YulangClosure.NativeSnapshotOwnerR34.ownerToken owner) ∧
      Exists.{0} fun bound =>
        Eq.{1} family (getElem.{0, 0, 0} (pool.data owner.hirOwner).effects q.effectIndex bound).identity :=
⋯
'YulangClosure.NativeSnapshotOwnerR34.owner_family_exact' depends on axioms: [propext]
theorem YulangClosure.NativeSnapshotOwnerR34.owner_operation_exact : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Module Parse Green : Type}
  [inst : DecidableEq.{1} Module] [inst_1 : DecidableEq.{1} Parse] [inst_2 : DecidableEq.{1} Green]
  (pool : YulangClosure.NativeSnapshotOwnerR34.RetainedPool history Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history)
  (q :
    YulangClosure.NativeCallbackCoordinatesR33.OperationCoordinate
      (YulangClosure.NativeSnapshotOwnerR34.OwnerId history))
  {operation : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green},
  Eq.{1}
      (YulangClosure.NativeCallbackCoordinatesR33.decodeOperationCoordinate
        (YulangClosure.NativeSnapshotOwnerR34.issuedSnapshot pool owner) q)
      (some.{0} operation) →
    Eq.{1} q.family.snapshotToken (YulangClosure.NativeSnapshotOwnerR34.ownerToken owner) ∧
      Exists.{1} fun effect =>
        (Exists.{0} fun bound =>
            Eq.{1} (getElem.{0, 0, 0} (pool.data owner.hirOwner).effects q.family.effectIndex bound) effect) ∧
          (Exists.{0} fun bound => Eq.{1} (getElem.{0, 0, 0} effect.operations q.operationIndex bound) operation) ∧
            Eq.{1} operation.family effect.identity :=
⋯
'YulangClosure.NativeSnapshotOwnerR34.owner_operation_exact' depends on axioms: [propext]
@[defeq] theorem YulangClosure.NativeSnapshotOwnerR34.clone_preserves_translation : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Module Parse Green : Type}
  [inst : DecidableEq.{1} Module] [inst_1 : DecidableEq.{1} Parse] [inst_2 : DecidableEq.{1} Green]
  (pool : YulangClosure.NativeSnapshotOwnerR34.RetainedPool history Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history)
  (request consumer arm :
    YulangClosure.NativeCallbackCoordinatesR33.OperationCoordinate
      (YulangClosure.NativeSnapshotOwnerR34.OwnerId history))
  (row :
    List.{0}
      (YulangClosure.NativeCallbackCoordinatesR33.FamilyCoordinate
        (YulangClosure.NativeSnapshotOwnerR34.OwnerId history))),
  Eq.{1}
    (YulangClosure.NativeCallbackCoordinatesR33.translateCoordinates
      (YulangClosure.NativeSnapshotOwnerR34.issuedSnapshot pool (YulangClosure.NativeSnapshotOwnerR34.cloneOwner owner))
      request consumer arm row)
    (YulangClosure.NativeCallbackCoordinatesR33.translateCoordinates
      (YulangClosure.NativeSnapshotOwnerR34.issuedSnapshot pool owner) request consumer arm row) :=
⋯
'YulangClosure.NativeSnapshotOwnerR34.clone_preserves_translation' depends on axioms: [propext]
theorem YulangClosure.NativeSnapshotOwnerR34.owner_complete_row : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Module Parse Green : Type}
  [inst : DecidableEq.{1} Module] [inst_1 : DecidableEq.{1} Parse] [inst_2 : DecidableEq.{1} Green]
  (pool : YulangClosure.NativeSnapshotOwnerR34.RetainedPool history Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history)
  (row :
    List.{0}
      (YulangClosure.NativeCallbackCoordinatesR33.FamilyCoordinate
        (YulangClosure.NativeSnapshotOwnerR34.OwnerId history)))
  {families : List.{0} (YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green)},
  Eq.{1}
      (YulangClosure.NativeCallbackCoordinatesR33.translatePermissionRow
        (YulangClosure.NativeSnapshotOwnerR34.issuedSnapshot pool owner) row)
      (some.{0} families) →
    Eq.{1} families (pool.data owner.hirOwner).permissionRow ∧
      Eq.{1}
          (YulangClosure.NativeCallbackCoordinatesR33.decodeFamilyRow
            (YulangClosure.NativeSnapshotOwnerR34.issuedSnapshot pool owner) row)
          (some.{0} families) ∧
        Eq.{1} (List.length.{0} families) (List.length.{0} row) :=
⋯
'YulangClosure.NativeSnapshotOwnerR34.owner_complete_row' depends on axioms: [propext, Quot.sound.{u}]
theorem YulangClosure.NativeSnapshotOwnerR34.owner_translation_to_r32 : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Module Parse Green : Type}
  [inst : DecidableEq.{1} Module] [inst_1 : DecidableEq.{1} Parse] [inst_2 : DecidableEq.{1} Green]
  (pool : YulangClosure.NativeSnapshotOwnerR34.RetainedPool history Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history)
  (request consumer arm :
    YulangClosure.NativeCallbackCoordinatesR33.OperationCoordinate
      (YulangClosure.NativeSnapshotOwnerR34.OwnerId history))
  (row :
    List.{0}
      (YulangClosure.NativeCallbackCoordinatesR33.FamilyCoordinate
        (YulangClosure.NativeSnapshotOwnerR34.OwnerId history)))
  {out : YulangClosure.NativeCallbackCoordinatesR33.DecodedCoordinates Module Parse Green},
  Eq.{1}
      (YulangClosure.NativeCallbackCoordinatesR33.translateCoordinates
        (YulangClosure.NativeSnapshotOwnerR34.issuedSnapshot pool owner) request consumer arm row)
      (some.{0} out) →
    have table :=
      YulangClosure.NativeCallbackGrantBridgeR32.coveringTable out.request out.consumer out.arm out.families;
    Eq.{1} out.families (pool.data owner.hirOwner).permissionRow ∧
      Eq.{1} (List.length.{0} out.families) (List.length.{0} row) ∧
        Eq.{1} request.family.snapshotToken (YulangClosure.NativeSnapshotOwnerR34.ownerToken owner) ∧
          Eq.{1} consumer.family.snapshotToken (YulangClosure.NativeSnapshotOwnerR34.ownerToken owner) ∧
            Eq.{1} arm.family.snapshotToken (YulangClosure.NativeSnapshotOwnerR34.ownerToken owner) ∧
              (Exists.{1} fun effect =>
                  Membership.mem.{0, 0} (pool.data owner.hirOwner).effects effect ∧
                    Membership.mem.{0, 0} effect.operations out.request ∧ Eq.{1} out.request.family effect.identity) ∧
                (Exists.{1} fun effect =>
                    Membership.mem.{0, 0} (pool.data owner.hirOwner).effects effect ∧
                      Membership.mem.{0, 0} effect.operations out.consumer ∧
                        Eq.{1} out.consumer.family effect.identity) ∧
                  (Exists.{1} fun effect =>
                      Membership.mem.{0, 0} (pool.data owner.hirOwner).effects effect ∧
                        Membership.mem.{0, 0} effect.operations out.arm ∧ Eq.{1} out.arm.family effect.identity) ∧
                    (∀ (op : YulangClosure.NativeCallbackGrantBridgeR31.SourceOperationId Module Parse Green),
                        Membership.mem.{0, 0}
                            (List.cons.{0} out.request
                              (List.cons.{0} out.consumer (List.cons.{0} out.arm List.nil.{0})))
                            op →
                          Membership.mem.{0, 0} table.operations op) ∧
                      (∀ (family : YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green),
                          Membership.mem.{0, 0} (pool.data owner.hirOwner).permissionRow family →
                            Membership.mem.{0, 0} table.families family) ∧
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
                                Membership.mem.{0, 0} (pool.data owner.hirOwner).permissionRow family →
                                  Eq.{1} (getElem?.{0, 0, 0} table.families (List.idxOf.{0} family table.families))
                                      (some.{0} family) ∧
                                    (Membership.mem.{0, 0}
                                        (List.map.{0, 0} (fun a => List.idxOf.{0} a table.families) out.families)
                                        (List.idxOf.{0} family table.families) ↔
                                      Membership.mem.{0, 0} out.families family) :=
⋯
'YulangClosure.NativeSnapshotOwnerR34.owner_translation_to_r32' depends on axioms: [propext, Quot.sound.{u}]

STDERR:
```
