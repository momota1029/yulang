# R285 storage-reference closure — producer handoff (in progress)

The exact universal target was attempted in the leased R285 Lean module. The temporary declaration was removed after the direct Lean check exposed the first undischarged branch:

```text
YulangClosure/OriginalExtrusionStorageClosureR285.lean:241:21: error: unsolved goals
case some.mk
funds : Funding
s : State
hs : StorageClosed s
task : Work
popped : State
hselect : select s = some (task, popped)
⊢ StorageClosed (resultState (perform funds popped task))
```

The `select = none` branch closed. This is proof-state evidence, not a theorem or counterexample. The selected-work branch still needs closure transfer through queue removal and every `perform` constructor, including partial failure publication.

## Authority, inputs, and exact scope

Parent: `R70-ORDINARY-EXTRUSION-ENTRY-RETURN-1` in `notes/theory/2026-10-19-r70-ordinary-extrusion-invariant.md` §§1–3, 5, 7. The original inference direction is `notes/design/2026-10-11-yulang-inference-top-level-principles.md` §§1–3. This packet concerns only `YulangClosure.OriginalExtrusionWork` in the existing model. The 27 exact input paths in `tasks/agent-loop/sprints/extrusion-storage-closure-r285-inputs.json` all matched their SHA-256 values before construction. Manifest SHA-256: `931a1fa15351521aeb2f325b0e1822ffe6c8cbd3395b33c0846b8d38281d2ef8`. Contract SHA-256: `77d26a9082294f73a2f6aca12fbccfe5e9a76307705c8673328193b8745857f7`; reviewed R284 receipt SHA-256: `232160d1b932eaea4fa037134395c203e78f3ab047ca47e798aeb589d3fe4d0b`.

Notation in the inventory: `V r` is raw Value row `r`, `E r` is raw Effect row `r`; `qv r` and `qe r` are the kind-separated canonical row ordinals. Each raw row must be below its kind's vector length, and its canonical ordinal must be below the same vector length. `T t` is a raw term label found by `State.storedTerm`; `W v` is a published view ID (`s.views v ≠ none`). A published view tail is `E r` and requires both bounds. `RowsValid` supplies the row, term, memo, queue, port, and parent bounds; the new `StorageClosed` conjoins capture, view, leaf, bucket, memo-kind, and parent-kind clauses. A source/native row is not certified by these abstract-model checks.

## Finite State-field consumer inventory

| State field | References, kind/bound and canonical read | Actual or latent consumer | Model write / publication / transfer owner |
| --- | --- | --- | --- |
| `operation` | `initial` is a Value or Effect endpoint; row case needs `V r/qv r` or `E r/qe r`. `caller.lower/upper` can each contain raw Value rows; `target`, `occurrence`, `processing`, `sources`, `qualified` are not row/view ordinals. | `step` canonicalizes `initial` for root lookup; `State.retain` stores the whole operation in a Parent; `boundRequest` publishes it externally. The caller endpoints are copied, not dereferenced locally. | `initializeLocal` replaces operation, `State.retain` copies it, `boundRequest` transfers it. There is no caller validation in `step`. |
| `qv` | Value-only map: each consumed raw `V r` has a same-kind bounded `qv r`; rigid Value endpoints remain rigid. | `State.canonical`, `canonicalBound`, `readValue`, `childKey`, `physicalInsert`, root lookup. | `State.allocate` extends identity at the new Value ordinal; other modeled transitions retain it. |
| `qe` | Effect-only map: each consumed raw `E r` has a same-kind bounded `qe r`; rigid Effect endpoints remain rigid. | `State.canonical`, `canonicalBound`, `readEffect`, `incomingJobs`, `visitStructure`, `physicalInsert`. | `State.allocate` extends identity at the new Effect ordinal; other modeled transitions retain it. |
| `values` | Every `Bounds` entry has `level` and selected `lowerRows/upperRows` (`V r/qv r`); `lowerAtoms/upperAtoms` may carry raw Value rows or `T t` structural endpoints. | `State.rowInfo` reads selected side by polarity; `selectedValue` makes latent child and original-bound refs; `physicalInsert` reads canonical owner and appends a physical slot. | `State.allocate` appends an empty row; `physicalInsert` writes one canonical row with `addValue`. No deletion. |
| `effects` | Same row-vector rules for `E r/qe r`; atom endpoints can also carry `W v` via Allowance, Support, or AnnotationMember. `contribution` is a rigid ID, not an Effect row. | `rowInfo`, `selectedEffect`, `physicalInsert`; rigid view-bearing atoms may later enter a Visit. | `State.allocate` appends; `physicalInsert` writes one row with `addEffect`. |
| `terms` | Explicit `(raw T t, StoredCell)` directory. `valueLeaf(.row r)` needs `V r/qv r`; `effectLeaf(.row r)` needs `E r/qe r`. `structure` Function ports, tuple elements, record field types and variant payloads each need a published raw `T t`. Value leaves must not themselves contain structural-term endpoints (`OriginalInferenceTerminationResolution.valueTerm = none`). Effect leaves can carry `W v`. | `storedTerm`, `cells`, `readValue`, `readEffect`, `termView`, `functionKeys`, `collectPorts`, `matchesCell`, `functionMatches`, `rebuildOne`; some references are latent until a Work visit. | `internCell` reuses or prepends one cell; `endpointTerm`, `rebuildOne`, `finishFunction` can publish cells. A later `.constructAfter` failure retains already published cells. |
| `termLabel`, `termAllocations` | Allocator readout/count, not a row or view; a proposed raw term label must not collide with `storedTerm`. | `internCell` reads both. | `internCell` increments count and publishes a `(T t, cell)` pair on success; collision returns failure without publication. |
| `views` | `views v = some none` is a published closed view; `some (some r)` names raw `E r/qe r`. Every referenced `W v` must be published. | `visitStructure` reads the view and may queue a canonical Effect-tail Visit; `ViewRefsValid` also covers view identities in all other stored containers. | No write in this local model. Source `candidate_effect` view publication and imports are external correspondence owners. |
| `captures` | Each nonempty bucket key is raw tail `E id/qe id`; each `Capture.source` is raw `E r/qe r`; `Capture.view` is `W v`. Quantification covers latent buckets at every `Nat` index. | `incomingJobs` reads a bucket for positive Effect-row copies; it canonicalizes each source and queues Visit plus IncomingAllowance. | No write in this local model. Source registration/merge/import ownership remains external. |
| `rows`, `structureMemo` | `CopyKey.endpoint` and image both need bounded raw references; Value/Effect kind must agree. `lookup` prioritizes `rows`, then `structureMemo`. | `visit`, `rebuildOne`, `finishAggregate`, `effectView`, `bound`, `incomingAllowance`, final root lookup. Entries can be latent until later Work. | `remember` writes through `memoPut`; `prepared` is a computed helper modeling row insertion. |
| `work`, `pendingBounds` | Every stored `Work` payload has the constructor-specific references listed below. Either list can hold any constructor in an arbitrary State. | `select` pops `work` first, then `pendingBounds`; `step` passes selected item to `perform`. | `push`, `pushAll`, `visitFunction`, `visitAggregate`, `visitStructure`, `scheduleBounds` queue; `select` removes head. `pushed`/`scheduled` are exact computed helper states. |
| `tuplePorts` | Each `(CopyKey,T t)` carries a bounded/canonical key endpoint and published term label; view-bearing Effect keys need `W v`. `start/len` in aggregate Work are slice offsets, not row ordinals. | `slice`, `finishAggregate`, and external tuple/record/variant requests. | `collectPorts` appends after each successful `readValue`, including a prefix retained on later failure. |
| `parents` | Each `Parent.copy`, `parent`, and saved `operation.initial` has bounded raw/canonical refs; copy and parent kinds agree. Saved `operation.caller` is an opaque transferred Request. | `State.retain` uses length for pending index and appends; later source parent/group owner is outside this local `step`. | `State.retain` appends one Parent after allocation and may retain it through later failure. |
| `pendingParents` | Indices must be `< parents.length`; not row ordinals. | Latent handoff to later intrusion owner, not read by local `step`. | `State.retain` appends the current Parent index when qualified. |
| `calls` | Funding boundary index, not a row/view reference. | `check` and `rebuildOne` ask arbitrary `Funding` at each named point. | `check` increments even on failure; `rebuildOne` increments around construct and post-publication sampling. |

## Every Work constructor and result path

| Work constructor | Raw/canonical, kind, bound and actual consumer | Queue / mutation / publication owner |
| --- | --- | --- |
| `visit key` | Key endpoint `V r/qv r`, `E r/qe r`, `T t`, or rigid view `W v`; `rowInfo` reads a raw row, `visitStructure` reads term/view, `lookup` checks memo. `target` is a level, not row. | `visit` may memoize anchor, allocate/copy high row, schedule children or fail; `visitFunction`, `visitAggregate`, `visitStructure`, `boundJobs`, `incomingJobs`, `start` construct Visits. |
| `function key children originals` | Key and every child are checked refs; four `originals` are raw `T t` labels. `finishFunction` calls `rebuildTerms`, `lookup`, `endpointTerm`, `functionMatches`; actual Value/Effect/Effect/Value port kinds and signs are checked by the constructor. | `visitFunction` queues frame and four child Visits. `rebuildOne`/`internCell` can publish row leaf terms before `.failed`; `finishFunction` can publish Function term and `remember` image. |
| `tuple key start len` | Key checked; `start/len` are offsets into `tuplePorts`; each selected port has key and raw `T t`. | `visitAggregate`/`collectPorts` build port prefix, queue frame and Visits; `finishAggregate` may memoize or hand off `.external .tuple`. |
| `record key start len` | As tuple, plus key's raw structural `T t` is read by `termView` for record fields; field type term labels are in stored structure. | Same collection/queue path; `finishAggregate` may publish `.external .record` with fields and selected ports. |
| `variant key start len` | As record, with raw structural `T t` and alternative payload term labels. | Same path; `finishAggregate` may publish `.external .variant`. |
| `effectView key view child` | Key and child checked; `view` is `W v`; `lookup child` must yield an Effect row to publish external tail. | `visitStructure` constructs frame and child Visit after reading a published view tail; `perform` returns `.external` or `.failed` with popped state. |
| `bound owner polarity child source` | Owner and child's key refs checked; `source.owner/endpoint` are raw Value/Effect refs retained unchanged. `lookup child` yields copied endpoint; `boundRequest` canonicalizes destination with qv/qe and publishes all raw/canonical fields. | `boundJobs` builds from visit-time selected bounds. `perform` returns `.external .bound` or `.failed`, with no extra local write after pop. External fiber/physical insertion owner is outside this model. |
| `incomingAllowance tail view source original` | `tail` is raw `E r/qe r`, `view` is `W v`, source is a checked key, and `original` keeps raw bound refs. `lookup source` obtains copied endpoint. | `incomingJobs` constructs from a capture bucket. `perform` returns `.external .incomingAllowance` or `.failed`, with no extra local write after pop. External capture/evidence insertion owner remains open. |

`Result.next`, `.external` and `.failed` all retain the exact state in `OriginalExtrusionRowValidityR283.resultState`. `.failed` may retain prior allocation, row append, memo write, tuple-port prefix, term publication and call count. The `perform` transfer-only lemmas cover `bound`, `incomingAllowance` and `effectView` *after* queue pop; they do not prove selected-state closure. `runPrefix` stops at `.external`/`.failed` and recurses only through `.next`. There is no theorem for arbitrary fuel or the computed three-step prefix.

## Kernel-checked boundary counterexample and open proof edge

`YulangClosure.OriginalExtrusionStorageClosureR285.CallerRowsValid` checks both Value endpoints inside `State.operation.caller`. The model's `Computed.rowInput caller` stores any caller without inspecting its endpoints; `boundRequest` copies the caller to an external Bound request and `State.retain` stores it in a Parent. The concrete `invalidCaller.lower = .row 99` is out of bounds in `Computed.rowInput invalidCaller`, whose Value vector has length 2. The kernel proves `computed_rowInput_invalid_caller : ¬ CallerRowsValid (Computed.rowInput invalidCaller)` and the parametric `no_universal_computed_input_with_caller`: any predicate implying `CallerRowsValid` fails to hold for every computed row input. Thus a requirement to validate even opaque, externally transferred caller endpoints cannot coexist with assumption-free `∀ caller` initialization in this model. This is a counterexample to those joint requirements, not to the candidate local-read `StorageClosed` or to R70 source reachability. The handoff requires primary adjudication of whether externally copied caller payloads are in scope for the requested storage closure; no implicit narrowing is claimed.

The candidate `StorageClosed` does not check `operation.caller` or saved `Parent.operation.caller`; it checks all locally dereferenced storage references listed above. It implies R284 `CaptureComplete`, rejects both reviewed gaps and holds for `Computed.rowInput caller` for arbitrary caller. The exact `step_preserves_storage` attempt stopped at `select s = some (task,popped)` and the `perform` result goal printed at the top of this handoff. The first unproved model transfer is full `StorageClosed` through `select`'s queue pop and then through `perform` for every constructor and all Funding outcomes. In particular `State.retain`'s parent append, `physicalInsert`'s canonical row append, `collectPorts`'s partial prefix, and `internCell`'s retained publication are not composed into a universal proof. No `runPrefix_preserves_storage` or computed-prefix preservation follows. No kernel counterexample to the candidate universal step theorem was found or claimed.

Parent application: the local checked facts refine the storage part of R70's unproved W entry premise, but discharge no original R70 premise. The first source/native bridge remains W for every actual production entry, including source/session constructors and `candidate_source`/`candidate_intrusion` publication/merge owners. R70, Simple-sub A/B, whole-language parent, and production authority stay OPEN. Independent review has not run.
## Final focused verification and complete theorem audit

Pinned native Lake: `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`. `elan which lake` resolved this installed path (exit 0). `lake --version` reported Lake `5.0.0-src+eb6cafb`, Lean `4.35.0`; `lake env lean --version` reported Lean `4.35.0`, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` (both exit 0). From `notes/theory/lean`, `lake build +YulangClosure.OriginalExtrusionStorageClosureR285` built 15 focused jobs (exit 0), and `lake env lean -j1 -M1024 YulangClosure/OriginalExtrusionStorageClosureR285.lean` exited 0 with no diagnostics. The bundled checker command used `--module YulangClosure.OriginalExtrusionStorageClosureR285`, all 19 fully qualified theorem names printed below as `--theorem` arguments, the pinned `--lake` path and `--timeout 180`. It exited 0; its internal audit scratch directory was removed by the checker before return. The complete printed types and `#print axioms` results follow verbatim.

```text
cwd: /home/momota1029/rust/yulang/notes/theory/lean
$ /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake --version
Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)
[exit 0]
cwd: /home/momota1029/rust/yulang/notes/theory/lean
$ /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake --no-cache env lean --version
Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
[exit 0]
cwd: /home/momota1029/rust/yulang/notes/theory/lean
$ /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake --no-cache build +YulangClosure.OriginalExtrusionStorageClosureR285
Build completed successfully (15 jobs).
[exit 0]
cwd: /home/momota1029/rust/yulang/notes/theory/lean
$ /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake --no-cache env lean -j1 -M1024 --root=/tmp/yulang-lean-audit-gzdg54ee /tmp/yulang-lean-audit-gzdg54ee/YulangProofAudit.lean
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionStorageClosureR285.storage_implies_capture_complete
YulangClosure.OriginalExtrusionStorageClosureR285.storage_implies_capture_complete : ∀
  (s : YulangClosure.OriginalExtrusionWork.State),
  YulangClosure.OriginalExtrusionStorageClosureR285.StorageClosed s →
    YulangClosure.OriginalExtrusionCaptureValidityR284.CaptureComplete s
'YulangClosure.OriginalExtrusionStorageClosureR285.storage_implies_capture_complete' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionStorageClosureR285.storage_implies_capture_complete
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionStorageClosureR285.capture_gap_not_storage
YulangClosure.OriginalExtrusionStorageClosureR285.capture_gap_not_storage : ∀
  (caller : YulangClosure.NativeValueStructure.Request),
  ¬YulangClosure.OriginalExtrusionStorageClosureR285.StorageClosed
      (YulangClosure.OriginalExtrusionRowValidityR283.captureGap caller)
'YulangClosure.OriginalExtrusionStorageClosureR285.capture_gap_not_storage' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionStorageClosureR285.capture_gap_not_storage
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionStorageClosureR285.view_tail_gap_not_storage
YulangClosure.OriginalExtrusionStorageClosureR285.view_tail_gap_not_storage : ¬YulangClosure.OriginalExtrusionStorageClosureR285.StorageClosed
    YulangClosure.OriginalExtrusionCaptureValidityR284.viewTailGap
'YulangClosure.OriginalExtrusionStorageClosureR285.view_tail_gap_not_storage' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionStorageClosureR285.view_tail_gap_not_storage
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionStorageClosureR285.computed_rowInput_storage
YulangClosure.OriginalExtrusionStorageClosureR285.computed_rowInput_storage : ∀
  (caller : YulangClosure.NativeValueStructure.Request),
  YulangClosure.OriginalExtrusionStorageClosureR285.StorageClosed
    (YulangClosure.OriginalExtrusionWork.Computed.rowInput caller)
'YulangClosure.OriginalExtrusionStorageClosureR285.computed_rowInput_storage' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionStorageClosureR285.computed_rowInput_storage
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionStorageClosureR285.capture_source_transfer_allocate
YulangClosure.OriginalExtrusionStorageClosureR285.capture_source_transfer_allocate : ∀
  (s : YulangClosure.OriginalExtrusionWork.State) (key : YulangClosure.OriginalExtrusionWork.CopyKey) (source : Nat),
  YulangClosure.OriginalExtrusionCaptureValidityR284.CaptureSourceValid s source →
    YulangClosure.OriginalExtrusionCaptureValidityR284.CaptureSourceValid (s.allocate key) source
'YulangClosure.OriginalExtrusionStorageClosureR285.capture_source_transfer_allocate' depends on axioms: [propext,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionStorageClosureR285.capture_source_transfer_allocate
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionStorageClosureR285.value_canonical_old_after_allocate
YulangClosure.OriginalExtrusionStorageClosureR285.value_canonical_old_after_allocate : ∀
  (s : YulangClosure.OriginalExtrusionWork.State) (key : YulangClosure.OriginalExtrusionWork.CopyKey) (id : Nat),
  id < s.values.length → (s.allocate key).qv id = s.qv id
'YulangClosure.OriginalExtrusionStorageClosureR285.value_canonical_old_after_allocate' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionStorageClosureR285.value_canonical_old_after_allocate
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionStorageClosureR285.effect_canonical_old_after_allocate
YulangClosure.OriginalExtrusionStorageClosureR285.effect_canonical_old_after_allocate : ∀
  (s : YulangClosure.OriginalExtrusionWork.State) (key : YulangClosure.OriginalExtrusionWork.CopyKey) (id : Nat),
  id < s.effects.length → (s.allocate key).qe id = s.qe id
'YulangClosure.OriginalExtrusionStorageClosureR285.effect_canonical_old_after_allocate' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionStorageClosureR285.effect_canonical_old_after_allocate
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionStorageClosureR285.capture_buckets_transfer_allocate
YulangClosure.OriginalExtrusionStorageClosureR285.capture_buckets_transfer_allocate : ∀
  (s : YulangClosure.OriginalExtrusionWork.State) (key : YulangClosure.OriginalExtrusionWork.CopyKey),
  YulangClosure.OriginalExtrusionStorageClosureR285.CaptureBucketsValid s →
    YulangClosure.OriginalExtrusionStorageClosureR285.CaptureBucketsValid (s.allocate key)
'YulangClosure.OriginalExtrusionStorageClosureR285.capture_buckets_transfer_allocate' depends on axioms: [propext,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionStorageClosureR285.capture_buckets_transfer_allocate
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionStorageClosureR285.memo_kind_transfer_put
YulangClosure.OriginalExtrusionStorageClosureR285.memo_kind_transfer_put : ∀
  (memo : YulangClosure.OriginalExtrusionWork.Memo) (key : YulangClosure.OriginalExtrusionWork.CopyKey)
  (endpoint : YulangClosure.OriginalExtrusionWork.Endpoint),
  (∀ (query : YulangClosure.OriginalExtrusionWork.CopyKey) (image : YulangClosure.OriginalExtrusionWork.Endpoint),
      memo query = Option.some image →
        YulangClosure.OriginalExtrusionStorageClosureR285.SameKind query.endpoint image) →
    YulangClosure.OriginalExtrusionStorageClosureR285.SameKind key.endpoint endpoint →
      ∀ (query : YulangClosure.OriginalExtrusionWork.CopyKey) (image : YulangClosure.OriginalExtrusionWork.Endpoint),
        YulangClosure.OriginalExtrusionWork.memoPut memo key endpoint query = Option.some image →
          YulangClosure.OriginalExtrusionStorageClosureR285.SameKind query.endpoint image
'YulangClosure.OriginalExtrusionStorageClosureR285.memo_kind_transfer_put' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionStorageClosureR285.memo_kind_transfer_put
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionStorageClosureR285.view_tails_transfer_pushed
YulangClosure.OriginalExtrusionStorageClosureR285.view_tails_transfer_pushed : ∀
  (s : YulangClosure.OriginalExtrusionWork.State) (pending : Bool)
  (items : List YulangClosure.OriginalExtrusionWork.Work),
  YulangClosure.OriginalExtrusionStorageClosureR285.ViewTailsValid s →
    YulangClosure.OriginalExtrusionStorageClosureR285.ViewTailsValid
      (YulangClosure.OriginalExtrusionWork.pushed pending items s)
'YulangClosure.OriginalExtrusionStorageClosureR285.view_tails_transfer_pushed' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionStorageClosureR285.view_tails_transfer_pushed
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionStorageClosureR285.leaf_refs_transfer_pushed
YulangClosure.OriginalExtrusionStorageClosureR285.leaf_refs_transfer_pushed : ∀
  (s : YulangClosure.OriginalExtrusionWork.State) (pending : Bool)
  (items : List YulangClosure.OriginalExtrusionWork.Work),
  YulangClosure.OriginalExtrusionStorageClosureR285.LeafRefsValid s →
    YulangClosure.OriginalExtrusionStorageClosureR285.LeafRefsValid
      (YulangClosure.OriginalExtrusionWork.pushed pending items s)
'YulangClosure.OriginalExtrusionStorageClosureR285.leaf_refs_transfer_pushed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionStorageClosureR285.leaf_refs_transfer_pushed
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionStorageClosureR285.view_tails_transfer_memo
YulangClosure.OriginalExtrusionStorageClosureR285.view_tails_transfer_memo : ∀
  (s : YulangClosure.OriginalExtrusionWork.State) (row : Bool) (key : YulangClosure.OriginalExtrusionWork.CopyKey)
  (endpoint : YulangClosure.OriginalExtrusionWork.Endpoint),
  YulangClosure.OriginalExtrusionStorageClosureR285.ViewTailsValid s →
    YulangClosure.OriginalExtrusionStorageClosureR285.ViewTailsValid
      { operation := s.operation, qv := s.qv, qe := s.qe, values := s.values, effects := s.effects, terms := s.terms,
        termLabel := s.termLabel, termAllocations := s.termAllocations, views := s.views, captures := s.captures,
        rows := if row = Bool.true then YulangClosure.OriginalExtrusionWork.memoPut s.rows key endpoint else s.rows,
        structureMemo :=
          if row = Bool.true then s.structureMemo
          else YulangClosure.OriginalExtrusionWork.memoPut s.structureMemo key endpoint,
        work := s.work, pendingBounds := s.pendingBounds, tuplePorts := s.tuplePorts, parents := s.parents,
        pendingParents := s.pendingParents, calls := s.calls }
'YulangClosure.OriginalExtrusionStorageClosureR285.view_tails_transfer_memo' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.OriginalExtrusionStorageClosureR285.view_tails_transfer_memo
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionStorageClosureR285.view_tails_transfer_allocate
YulangClosure.OriginalExtrusionStorageClosureR285.view_tails_transfer_allocate : ∀
  (s : YulangClosure.OriginalExtrusionWork.State) (key : YulangClosure.OriginalExtrusionWork.CopyKey),
  YulangClosure.OriginalExtrusionStorageClosureR285.ViewTailsValid s →
    YulangClosure.OriginalExtrusionStorageClosureR285.ViewTailsValid (s.allocate key)
'YulangClosure.OriginalExtrusionStorageClosureR285.view_tails_transfer_allocate' depends on axioms: [propext,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionStorageClosureR285.view_tails_transfer_allocate
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionStorageClosureR285.queued_view_refs_pushed
YulangClosure.OriginalExtrusionStorageClosureR285.queued_view_refs_pushed : ∀
  (s : YulangClosure.OriginalExtrusionWork.State) (pending : Bool)
  (items : List YulangClosure.OriginalExtrusionWork.Work),
  (∀ (item : YulangClosure.OriginalExtrusionWork.Work),
      item ∈ s.work → YulangClosure.OriginalExtrusionStorageClosureR285.WorkViewRefValid s item) →
    (∀ (item : YulangClosure.OriginalExtrusionWork.Work),
        item ∈ s.pendingBounds → YulangClosure.OriginalExtrusionStorageClosureR285.WorkViewRefValid s item) →
      (∀ (item : YulangClosure.OriginalExtrusionWork.Work),
          item ∈ items → YulangClosure.OriginalExtrusionStorageClosureR285.WorkViewRefValid s item) →
        (∀ (item : YulangClosure.OriginalExtrusionWork.Work),
            item ∈ (YulangClosure.OriginalExtrusionWork.pushed pending items s).work →
              YulangClosure.OriginalExtrusionStorageClosureR285.WorkViewRefValid
                (YulangClosure.OriginalExtrusionWork.pushed pending items s) item) ∧
          ∀ (item : YulangClosure.OriginalExtrusionWork.Work),
            item ∈ (YulangClosure.OriginalExtrusionWork.pushed pending items s).pendingBounds →
              YulangClosure.OriginalExtrusionStorageClosureR285.WorkViewRefValid
                (YulangClosure.OriginalExtrusionWork.pushed pending items s) item
'YulangClosure.OriginalExtrusionStorageClosureR285.queued_view_refs_pushed' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionStorageClosureR285.queued_view_refs_pushed
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionStorageClosureR285.bound_perform_retains_state
YulangClosure.OriginalExtrusionStorageClosureR285.bound_perform_retains_state : ∀
  (funds : YulangClosure.OriginalExtrusionWork.Funding) (s : YulangClosure.OriginalExtrusionWork.State)
  (owner : YulangClosure.OriginalExtrusionWork.Endpoint) (p : YulangClosure.NativeMergeExpansion.Polarity)
  (child : YulangClosure.OriginalExtrusionWork.CopyKey) (source : YulangClosure.OriginalExtrusionWork.RawBound),
  YulangClosure.OriginalExtrusionRowValidityR283.resultState
      (YulangClosure.OriginalExtrusionWork.perform funds s
        (YulangClosure.OriginalExtrusionWork.Work.bound owner p child source)) =
    s
'YulangClosure.OriginalExtrusionStorageClosureR285.bound_perform_retains_state' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionStorageClosureR285.bound_perform_retains_state
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionStorageClosureR285.incoming_perform_retains_state
YulangClosure.OriginalExtrusionStorageClosureR285.incoming_perform_retains_state : ∀
  (funds : YulangClosure.OriginalExtrusionWork.Funding) (s : YulangClosure.OriginalExtrusionWork.State)
  (tail view : Nat) (source : YulangClosure.OriginalExtrusionWork.CopyKey)
  (original : YulangClosure.OriginalExtrusionWork.RawBound),
  YulangClosure.OriginalExtrusionRowValidityR283.resultState
      (YulangClosure.OriginalExtrusionWork.perform funds s
        (YulangClosure.OriginalExtrusionWork.Work.incomingAllowance tail view source original)) =
    s
'YulangClosure.OriginalExtrusionStorageClosureR285.incoming_perform_retains_state' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionStorageClosureR285.incoming_perform_retains_state
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionStorageClosureR285.effect_view_perform_retains_state
YulangClosure.OriginalExtrusionStorageClosureR285.effect_view_perform_retains_state : ∀
  (funds : YulangClosure.OriginalExtrusionWork.Funding) (s : YulangClosure.OriginalExtrusionWork.State)
  (key : YulangClosure.OriginalExtrusionWork.CopyKey) (view : Nat)
  (child : YulangClosure.OriginalExtrusionWork.CopyKey),
  YulangClosure.OriginalExtrusionRowValidityR283.resultState
      (YulangClosure.OriginalExtrusionWork.perform funds s
        (YulangClosure.OriginalExtrusionWork.Work.effectView key view child)) =
    s
'YulangClosure.OriginalExtrusionStorageClosureR285.effect_view_perform_retains_state' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionStorageClosureR285.effect_view_perform_retains_state
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionStorageClosureR285.computed_rowInput_invalid_caller
YulangClosure.OriginalExtrusionStorageClosureR285.computed_rowInput_invalid_caller : ¬YulangClosure.OriginalExtrusionStorageClosureR285.CallerRowsValid
    (YulangClosure.OriginalExtrusionWork.Computed.rowInput
      YulangClosure.OriginalExtrusionStorageClosureR285.invalidCaller)
'YulangClosure.OriginalExtrusionStorageClosureR285.computed_rowInput_invalid_caller' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionStorageClosureR285.computed_rowInput_invalid_caller
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionStorageClosureR285.no_universal_computed_input_with_caller
YulangClosure.OriginalExtrusionStorageClosureR285.no_universal_computed_input_with_caller : ∀
  (predicate : YulangClosure.OriginalExtrusionWork.State → Prop),
  (∀ (s : YulangClosure.OriginalExtrusionWork.State),
      predicate s → YulangClosure.OriginalExtrusionStorageClosureR285.CallerRowsValid s) →
    ¬∀ (caller : YulangClosure.NativeValueStructure.Request),
        predicate (YulangClosure.OriginalExtrusionWork.Computed.rowInput caller)
'YulangClosure.OriginalExtrusionStorageClosureR285.no_universal_computed_input_with_caller' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionStorageClosureR285.no_universal_computed_input_with_caller
[exit 0]
PASS: YulangClosure.OriginalExtrusionStorageClosureR285.storage_implies_capture_complete, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionStorageClosureR285.capture_gap_not_storage, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionStorageClosureR285.view_tail_gap_not_storage, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionStorageClosureR285.computed_rowInput_storage, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionStorageClosureR285.capture_source_transfer_allocate, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionStorageClosureR285.value_canonical_old_after_allocate, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionStorageClosureR285.effect_canonical_old_after_allocate, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionStorageClosureR285.capture_buckets_transfer_allocate, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionStorageClosureR285.memo_kind_transfer_put, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionStorageClosureR285.view_tails_transfer_pushed, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionStorageClosureR285.leaf_refs_transfer_pushed, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionStorageClosureR285.view_tails_transfer_memo, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionStorageClosureR285.view_tails_transfer_allocate, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionStorageClosureR285.queued_view_refs_pushed, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionStorageClosureR285.bound_perform_retains_state, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionStorageClosureR285.incoming_perform_retains_state, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionStorageClosureR285.effect_view_perform_retains_state, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionStorageClosureR285.computed_rowInput_invalid_caller, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionStorageClosureR285.no_universal_computed_input_with_caller, under its printed hypotheses; axiom whitelist satisfied.
Named declarations only; ordinary-mistake check, not independent review or source correspondence.
```

Audit summary: 19 exact begin/end pairs and 19 PASS lines, no FAIL lines. `view_tails_transfer_memo` has no axioms; `leaf_refs_transfer_pushed` uses `propext`, `Classical.choice`, `Quot.sound`; the remaining exact axiom lists are printed above. No project axioms or `sorryAx` appeared. The final `rg -n 'sorry|admit|^axiom|debug.skipKernelTC|unsafe|native_decide'` of the authored module returned no matches (exit 1). The final direct Lean check exited 0 with no diagnostics. All 27 frozen inputs still matched at final recheck. The final Lean source SHA-256 is `3000b88435c4cc43a1be5844c1c938470553a30217e351799f50f01bb9f8b9cb`.

Material failed attempts were retained: an early build failed because `h.2.2` referred to a conjunction rather than `ViewTailsValid`; `h.2.2.1` repaired it. A queue-pop lemma attempt exposed large state-record normalization goals, and the unimported `aesop` tactic was rejected; the unchecked declaration was removed. A first `CaptureBucketsValid` allocation proof did not split the endpoint before simplifying, then passed after splitting. The concrete invalid-caller proof first used `decide`, which lacked a `Decidable` instance; simplification proved it. None of these diagnostic failures was treated as a semantic counterexample. The decisive kernel counterexample is the final `computed_rowInput_invalid_caller`/`no_universal_computed_input_with_caller` pair, under its printed premises.

Only the two leased authored paths and the exclusive `.lake/build` cache were written. The single manually created `/tmp/yulang-r285-step-attempt.log` was copied into this handoff and removed after Luna's scope correction; the bundled checker's own temporary audit directory was absent after exit. No other scratch remains from this producer. No descendants, Git, compiler/test/source changes, dependency changes, broader suite, external contact, or checker bypass. CPU/RSS and total active wall time were not measured; all focused tool invocations returned before the 2,400-second bound, with no timeout. **STOP / WRITES_STOPPED**. Leases return to Luna for reconciliation and fresh independent review; no carryover requested.
