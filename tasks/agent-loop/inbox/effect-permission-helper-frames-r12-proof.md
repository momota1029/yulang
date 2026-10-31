# R12 proof handoff — sequential revision 2

Status: **SYNTAX REPAIR CONSTRUCTED, UNCHECKED; WRITES STOPPED**. Amendment 01 SHA256 `94661003e31471dd4bdfcf1e96b0e789a9441e2d7c69bdb009f668e7f443f868` grants only this sequential repair. Artifact revision 2: 15691 bytes, SHA256 `92531e0849a08a03a37bbb35315f01b831d31bdffb108712c5b0a4a7eaaa75dd`.

Exact delta: flatten the three multiline `HelperState` record updates in `applyOp`; consistently rename reserved Lean identifier `prefix` to `priorPermissions` (including the `Cut` field and its references). This is a binder/field-label alpha-renaming plus layout repair. No operation, state content, theorem meaning, hypothesis, endpoint or retained path changed. `operation_preserves_allocator` retains its original case/rfl proof: audit-1 errors in later branches follow the earlier `applyOp` parse failure. `reservation_projection` likewise retains its original proof, for reassessment by primary's final audit. No further tactic changes were needed by static inspection; this is not evidence those proofs elaborate.

Primary audit 1 is preserved at `/tmp/yulang-effect-permission-helper-frames-20261029-r12/attempt-1/audit-receipt.json`, SHA256 `00a9fdc3795cec81e4e7b16ec090bfb4e566bd244a20538edf76dcdce7953376`: exit 1, 12.92 seconds, max RSS 798608 KiB, zero theorem types/axiom reports. Read actual raw diagnostics: first record parse error at line 80, later allocator rfl/reservation goals, and reserved `prefix` cascade. This is a syntax/build failure, not a counterexample. Raw audit 1 was not modified. Revision-1 artifact is retained in primary's immutable attempt-1 project; revision-1 handoff hash remains `0dec12d68266bd8abf3e858eb47d406fb29cfbc8a2b40d3c15518e9d96f9efe3`, with its contents reproduced below as historical revision 1.

Read frozen amendment, audit receipt/raw stdout, frozen source handoff and revision-1 bytes before repairing. No Lean/Lake/checker probe, test, compiler/Git command, descendant or other path write occurred. Nine public theorem roots and all semantic limitations remain those of revision 1; their source declaration binders now use `priorPermissions`. Actual new theorem types/axioms remain unavailable pending primary audit 2. The full native retained-path/relative-path map and execution correspondence remain OPEN.

**Writes stopped:** artifact and this sequential handoff are frozen. The repair write script completed within its 30-second write bound.

---

Historical revision 1 follows verbatim; its artifact hash/status/theorem binder spelling are historical.

# R12 proof handoff — revision 1

Status: **CONSTRUCTED, UNCHECKED; WRITES STOPPED**. This is a source-operation footprint transcription and conditional R11 application. It is not a kernel-accepted result, independent review, Rust execution witness or parent closure. The primary owns the isolated Lean audit and may freeze these bytes.

## Authority, inputs and exact writes

- Author/lease: `/root/effect_permission_helper_frames_r12_lean`, registered `lean_prover`, 600-second fixed leaf packet. No descendants.
- Contract `tasks/agent-loop/sprints/effect-permission-helper-frames-20261029-r12.md`: SHA256 `7c7573abd1778414300f78b7b0271d5d3479b7f3e9c296a343bfb51c6102ecd4`.
- Manifest `tasks/agent-loop/sprints/effect-permission-helper-frames-20261029-r12-inputs.json`: SHA256 `057f4dafaa51ab8343a090de4f789adf2bce1d4e8db08d630551cb1d013f9a8c`. All 133 entries were read-only authenticated: zero missing/hash mismatches.
- Frozen source handoff `tasks/agent-loop/inbox/effect-permission-helper-frames-r12-source.md`: SHA256 `e270f74164f29816f5823687afc431617843b49ae7e28ffb06bc942d5a8e385b`; read before final construction.
- Immutable R11 dependency `notes/theory/lean/YulangClosure/FormalPermissionSourceInstance.lean`: SHA256 `828eef57d8caaa538c8feb91ad023dc45eb41e421b4eb430532e383ee1c75e91`; reauthenticated unchanged. Its accepted outcome and independent review were read.
- Only written paths: `notes/theory/lean/YulangClosure/FormalPermissionHelperFrames.lean` and this handoff. No scratch/generated/cache paths.
- R12 artifact: 15493 bytes, SHA256 `ed099b3f78fc4d7138d2342b81bf39938bcfbf90433ce5a5ac036a5bef6c5d68`. Import: `YulangClosure.FormalPermissionSourceInstance`; no root import changed.

## Original claim, sources and corrections

The original parent remains the universally quantified source-preservation/principal-coverage/soundness/progress/termination obligation in `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §1, retaining one joint witness and all supported source programs. Its original paper locators are recorded in §2; no new paper claim is derived here. The authoritative correction is `notes/design/2026-10-24-birth-level-scc-intrusion.md` §§2–4: immutable Value birth levels and the induced graph at each birth. The whole-language closure guide and Lean README retain all original parent gates OPEN. These claims/corrections were inspected; R12 changes none of their quantifiers or accepted features.

Exact immediate parent is R11 `FormalPermissionSourceInstance.exact_tree_r9_application`, under `Reservations` and 13 local `TreeFrames` fields. Definitions read: `FormalPermissionSourceAllocation.Allocator`, `Projection`, `HelperFrames`, `SourcePair`, `SourcePortSuccess`, and the exact R11 `Frame`, `FunctionFrames`, `TreeFrames`, supplier/application. This remains the R5 selected Int/Unit/Function/Tuple instance; R12 does not generalize it to the whole language or remove unrepresented source constructors from the parent.

Pinned Rust sources: `crates/yu-solver/src/candidate_effect.rs` SHA256 `1f64d4fec8f2abceb11a48a51f5b615aa2cf605c9586ba742f15f9024a6a2717`, especially 1617–1788; `crates/yu-solver/src/lib.rs` SHA256 `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07`, especially `reserve_f5b` 135+, `reserve_typed_route_lane!` 9088+, `fresh_effect_at_level` 10487+, `with_term_events` 10594+, sampling 10774–11017. The source handoff owns the operation-to-cut mapping; no stronger correspondence is claimed.

## Construction and cuts

`HelperState` explicitly separates four allocator vectors plus the local permission sequence from term-arena state, capacity events, capacity lanes, accounting flags/counters/ledgers, graph/local scratch byte counters, retained-path/concrete copy buffers, tuple buffers and traversal path. Nat/List Nat payloads abstract arena/accounting contents; they are neither Rust objects nor implementations of APIs. `HelperOp` writes only the explicit owning fields. There is no arbitrary helper callback that can mutate the allocator and no protected-field endpoint equality in an operation constructor.

Int/Unit cuts use two `collectedLeafRead` operations: the actual Rust branches read cached batch terms. Port/Function/Tuple completion call shapes each contain two explicit arena constructor/drain sequences plus supplied event-processing operations. The event trace is an overapproximation of permitted writes, not a proof that a particular event sequence or successful return occurred. The test snapshot field is an opaque replacement payload for its actual ring-buffer write footprint; no append semantics for that ring buffer is asserted.

Every operation preserves the full allocator data; induction composes this fact. `localProjection` drops an arbitrary preexisting full permission prefix without rewriting any retained record. Nonempty call programs lift to `HelperFrames` using explicit `.cons` steps; `.nil` terminates the interpreted tail only. `Cut` stores initial coordinates and an operation program. Its entry equations identify the initial row count and `prefix ++ entries`; it has no final state, no endpoint equality, no `HelperFrames`, no `TreeFrames` and no successful-return premise. `Call` has a leaf/port/function/tuple index and a nonempty program; it does not claim native authenticity.

`FunctionOperations` names five corresponding programs. `TreeOperations` retains both five-cut functions, inner Int, inner Tuple, root Tuple, exact R11 sequential row coordinates, local paths, metadata and ordinals. `tree_frames_from_operations` applies the footprint lifting at these 13 cuts. `exact_tree_r9_from_operations` passes those frames to R11 and returns its SAME constructed `out`/`SourcePair`, four births and arbitrary allocator permission-prefix equation. No default/empty frame is supplied for an unknown call.

`pushPermission` is separate from `HelperOp`. `permission_append_delta` states a row frame plus an exact permission delta, never a permission frame. `concretePreparation` records retained-path reservation/copy, concrete reservation/copy, backing-byte charge, then the separate append, then completion. The same `Retained` entry supplies path, metadata/concrete members and append record. The generic and ordered concrete delta theorems preserve the full arbitrary initial permission sequence and append exactly that entry.

Reservation writes only capacity. Capacity integers, byte counts, term payloads and event transcripts have no built-in claim of observed values, monotonicity, machine-word arithmetic validity, availability or successful return. Fresh pushes and four `Reservations` remain R11 obligations. R12 does not erase error paths by proving success.

## Exact public theorem surface

All names below are in `YulangClosure.FormalPermissionHelperFrames`. These are source declaration types, **not printed checker types**. Each must receive a fresh actual type/axiom audit from the primary. Private helpers are transitively included.

```lean
theorem operation_preserves_allocator (op : HelperOp) (s : HelperState) :
    (applyOp op s).allocator = s.allocator
```

```lean
theorem operations_preserve_allocator (ops : List HelperOp) (s : HelperState) :
    (runOps ops s).allocator = s.allocator
```

```lean
theorem nonempty_operations_frame (first : HelperOp) (rest : List HelperOp)
    (prefix : List Retained) (s : HelperState) :
    HelperFrames (localProjection prefix s)
      (localProjection prefix (runOps (first :: rest) s))
```

```lean
theorem reservation_projection (s : HelperState) (lane : CapacityLane) (capacity : Nat) :
    (applyOp (.reserveCapacity lane capacity) s).capacities lane = capacity ∧
    (applyOp (.reserveCapacity lane capacity) s).allocator = s.allocator
```

```lean
theorem permission_append_delta (s : HelperState) (entry : Retained) :
    (pushPermission s entry).allocator.bounds = s.allocator.bounds ∧
    (pushPermission s entry).allocator.permissions = s.allocator.permissions ++ [entry]
```

```lean
theorem concrete_port_prefix_delta (before after : List HelperOp)
    (s : HelperState) (entry : Retained) :
    (runOps after (pushPermission (runOps before s) entry)).allocator.bounds = s.allocator.bounds ∧
    (runOps after (pushPermission (runOps before s) entry)).allocator.permissions =
      s.allocator.permissions ++ [entry]
```

```lean
theorem ordered_concrete_port_delta (entry : Retained)
    (pathCapacity concreteCapacity backing : Nat) (after : List HelperOp) (s : HelperState) :
    (runOps after (pushPermission
      (runOps (concretePreparation entry pathCapacity concreteCapacity backing) s) entry)).allocator.bounds =
        s.allocator.bounds ∧
    (runOps after (pushPermission
      (runOps (concretePreparation entry pathCapacity concreteCapacity backing) s) entry)).allocator.permissions =
        s.allocator.permissions ++ [entry]
```

```lean
theorem tree_frames_from_operations (s : State) (ops : TreeOperations s) : TreeFrames s
```

```lean
theorem exact_tree_r9_from_operations (s : State) (a : Allocator) (level : Nat)
    (length : a.bounds.length = s.nextEffect) (aligned : Aligned a)
    (ready : Reservations a level) (ops : TreeOperations s) :
    ∃ out : ValueDecoded FormalPermissionAuthenticatedNativeDecode.context false s,
      SourcePair FormalPermissionAuthenticatedNativeDecode.context false
        FormalPermissionAuthenticatedNativeDecode.tree
        (FormalPermissionAuthenticatedNativeDecode.code 0 1) s out ∧
      out = FormalPermissionAuthenticatedNativeDecode.output s 0 1 ∧
      out.entries = FormalPermissionAuthenticatedNativeDecode.retained s.nextEffect ∧
      out.births = [s.nextEffect, s.nextEffect + 1, s.nextEffect + 2, s.nextEffect + 3] ∧
      out.state = {s with nextEffect := s.nextEffect + 4} ∧
      Aligned (afterFour a level) ∧
      (afterFour a level).permissions = a.permissions ++ out.entries
```

## Verification and resource receipt

Read `.agents/skills/yulang-lean-proofs/SKILL.md`, `references/sources.md` and `references/execution.md`, root `AGENTS.md`/`AGENTS.pre-sprint.md`, governing sprint rule, exact contract and relevant manuscript/correction/declarations. Read `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`: project pin is Lean 4.35.0, no external packages, project process flags `-j1 -M1024`. The actual native tool version was not executed by this leaf because the primary retained all Lean/Lake/checker ownership. Local pinned Lean source consulted: `Init/Data/List/TakeDrop.lean` (`List.drop_left`) and `Init/Data/List/Nat/TakeDrop.lean`.

Actual checks: Python SHA256 authentication of 133 manifest entries (exit 0; zero mismatches), dependency/artifact hash reads, source searches, and prohibited-token search on the changed Lean source (no `sorry`, `admit`, project `axiom`, or checker-bypass tokens). These are static construction checks, not kernel evidence. No Lean, Lake, bundled checker, tests, Cargo, compiler execution, install, Git or descendant launch occurred. No new theorem has an actual axiom result yet. Do not infer the R11 imported audit's results for these new declarations. No actual Lean diagnostic or model/runtime receipt exists for R12 at this handoff. Audit attempts consumed by leaf: 0.

Primary audit target: module `YulangClosure.FormalPermissionHelperFrames`, all nine public theorem roots above. Fresh isolated project/cache and complete dependency inventory belong to primary. This leaf has created no temporary proof, audit, resource or cache files. Exact measured active reasoning duration is unavailable; the assignment's fixed maximum is 600 seconds and no worker-side build/check process ran.

## Precise remaining premises and next gate

The operation-frame mathematics is conditional on the displayed *operation transcription*, not equivalent to an established Rust execution. The first remaining bridge, owned by the primary/source-native lane, is an actual per-cut execution-to-program relation: which native state fields and full retained-path records project to each `Cut`, which exact operations/event payloads occur, and where each helper returns or errors. A generic nonallocating write footprint alone cannot prove that relation. In particular R11 uses relative local paths such as `[]` / `[result]`, while Rust uses full `FormalPortStep` paths. `localProjection` only removes a permission **list prefix**; it does not normalize a structural path. No checked full-path/relative-path map has been constructed or assumed as a proved bridge. Entry-coordinate equations must be obtained from the actual connected trace, not supplied from desired endpoints.

Also OPEN: primitive/arena/copy/Vec alias and library behavior; reservation/checked-arithmetic/copy/term availability; native success and capacity observations; complete publication to graph `formal_permissions`; complete Rust projection/native authenticity; original parent; effect hygiene; consumer residual; soundness; principality; termination; production. Fresh kernel audit and independent review are required even for this bounded operation model. R12 supplies no compiler change or execution witness and does not claim original parent closure.

Next in-scope step: primary freezes these bytes, runs the separately released focused pinned audit, then obtains independent review of operation coverage and application boundary. Any repair requires a new exact primary instruction; no writes continue after this handoff.

**Writes stopped:** only the two leased paths were changed; no background process, children, unresolved generated output, Git mutation or other path write remains.
