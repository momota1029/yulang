# Original inference termination: native Context descent and exact remaining global owner

Date: 2026-10-26
Producer: `/root/termination`, bounded leaf; no child delegation
Assigned baseline: `a9c746f31cc0eabeba9ebf5b673b6f121ed0ca82`, branch `yulang3`
Status: CONSTRUCTED / CHECKER-ACCEPTED; independent review PENDING
Original whole `SourceProblem.InferenceTermination`: OPEN, neither proved nor refuted
Production/compiler behavior: unchanged
Exact output leases: this handoff and `notes/theory/lean/YulangClosure/OriginalInferenceTermination.lean`

## 1. Result and the boundary that must remain prominent

The actual `NativeContextExpansion.scanStep` now has a proved strictly decreasing
measure, unconditional accessibility, and a fuel-free total presentation. Its
existing fuel-based `scanLoop` stabilizes at a bound derived from the initial
stack. Success and validation rejection are both covered. No finite successful
`ScanRun`, finite table/universe, table acyclicity premise, or resource cap is
assumed for the scanner theorem.

**`scanTotal` is the stack scan inside `candidate_zero_word_filters`; it is not
that function's post-scan `consume(self, &filters, residual)` callback, and is
not `run_candidate_typed_drain` or whole inference.** The callback can enter
Effect bound insertion and Replay enqueue. Those operations are still in the
open global progress obligation.

An independent construction reuses the existing
`NativeValuePorts.context_preserves_formation` lemma to derive the exact
child-ID topological law from `NativeContextTables.Store.intern` and its
actual successful history events. Commit, cancellation, and subsequent numeric
ID reuse are included. A ready-marker rank also proves well-foundedness of an
explicit overapproximation of the successful stack actions in Context fold,
rename, and payload discovery. That result covers control actions, not the
meaning/termination of an arbitrary external fold callback.

A separate negative theorem proves that the existing
`NativeDrainOwnership.Step` projection is not accessible at any state because
its unrestricted `reserveOther` event can always occur. This is an exact
counterexample to promoting that *event-conservation projection* into the
inference transition relation. It is **not** a source-qualified divergent
program or a refutation of original Yulang inference termination.

## 2. Original statement and governing source

The original root is `YulangClosure.SourceProblem.InferenceTermination` in
`notes/theory/lean/YulangClosure/Contracts.lean:151–155`:

```lean
∀ s x n, p.supported s → p.inferInitial s x n →
  Acc (fun next prev => p.inferStep prev next) n
```

It ranges over every supported source initial state, without requiring a
successful typing derivation. Rejection/error paths must therefore terminate
as well. It does not claim termination of program execution. The whole-language
closure document explicitly permits recursion and does not conclude evaluation
termination (`docs/yulang-whole-proof-closure-ja.md:41,77,305`).

Governing unchanged source scope:

- `notes/design/2026-10-11-yulang-inference-top-level-principles.md`, §§1, 1.1,
  Authority and integration: ordinary generation, accumulation, propagation,
  levels, extrusion, intrusion, generalization, natural progress and termination.
- `notes/design/2026-10-24-birth-level-scc-intrusion.md`, §§2–6: immutable Value
  birth levels and SCCs in each induced same-birth graph; retained actual polar
  parent/copy pairs. No superseded cross-level SCC example is reused.
- `notes/theory/2026-10-13-intrusion-source-preservation-proof.md`, §§1,3,5,
  read with that birth-level correction: the original supported source domain,
  original scopes/shared witnesses, complete Call, effect hygiene and ordinary
  inference remain in the parent. Local extrusion is not combined termination.
- `docs/yulang-whole-proof-closure-ja.md`, original goal and closure interfaces:
  finite-prefix/history results and conditional composition do not close the
  original native inference obligation.

The original external Simple-sub PDF/Scala paper implementation was not
available/read directly in this packet; no theorem transfer from it is claimed.
The historical directed-weight audit and explicit-effect termination source
map were inspected as gap locators, not current native counterexamples.

## 3. Exact proved declarations and meaning

All names below have prefix `YulangClosure.OriginalInferenceTermination`.
All printed types, including private/generated originating theorems, are in the
complete census log listed in §6.

### Exact existing scanner, arbitrary tables and malformed input

- `two_children_smaller`: `left < parent` and `right < parent` imply
  `3^left + 3^right < 3^parent`.
- `scanStep_decreases`: `scanStep t s = some u` implies
  `scanRank u < scanRank s`, where `scanRank` is the pending-stack sum of
  `3^id`. Zero/visited skips remove a positive summand; Prefix/Swap/Without
  replace it by one smaller child; Replay replaces it by two smaller children.
- `scanStep_wellFounded (t : Tables)` and `scanStep_accessible (t) (s)`:
  well-foundedness/accessibility of the reverse exact successful native scan
  transition, with no state invariant or successful transcript argument.
- `scanStep_varying_tables_wellFounded`:
  `WellFounded (fun next prev => ∃ t : Tables, scanStep t prev = some next)`.
  The bound is uniform even if tables grow/change between observations.
- `pendingRank_zero_iff`: the rank is zero exactly when the pending list is empty.
- `scanLoop_eq_total (t) (fuel) (s) (enough : scanRank s ≤ fuel)`:
  `scanLoop t fuel s = scanTotal t s`. `scanTotal` is defined by the unchanged
  scan transition and a checked well-founded recursion, with no fuel parameter.
- `scanLoop_stable`: every extension of an already sufficient fuel yields the
  same result, including `none`.
- `parse_stable (t) (root extra : Nat)`:
  `parse t (3^root + extra) root = parse t (3^root) root`.
  This is a proved sufficient ghost bound, including repeated binary Replay
  branching; it is not a production cap or an asymptotically tight runtime claim.
- `scanTotal_success_iff`: `scanTotal t s = some p ↔ ScanRun t s p`.
- `scanTotal_execution`: constructs `ScanExecution t s (scanTotal t s)` for
  every `t,s`. The concluded finite execution includes empty-stack finish,
  nonempty-stack validation rejection, and every successful scanner step.

No Context constructor is silently omitted: Prefix, Replay, Swap, Without
follow the native guards; Suffix/Both are explicitly rejected by this parser,
just as the existing `scanStep` definition does. Missing contexts/weights/views,
invalid child IDs, illegal parser mode, nonzero words, mismatched View metadata,
and mixed final flags retain their existing rejection behavior. The Lean
projection does not encode native memory reservation failure, which may stop
earlier; no success or recovery is asserted for it.

### Construction of actual stored Context topology

- `intern_contexts_formed`: existing `ContextsFormed` plus the actual constructor
  guard `∀ input ∈ contextInputs node, input ≤ s.contexts.length` implies
  formation of `(s.intern node).1`; it reuses the prior interner lemma.
- `store_step_contexts_formed`, `store_run_contexts_formed`, and
  `store_history_contexts_formed`: derive the invariant through every existing
  Store constructor, finite operation run, commit and cancellation history.
- `constructed_context_children (history : NativeContextTables.History s)
  (found : s.tables.contexts id = some node)`:
  `∀ child ∈ contextInputs node, child < id`.
  The six constructors and both Replay children are included. A cached intern
  reuses its old property; fresh insertion uses the actual old frontier.
- `native_context_scan_accessible (s : Store) (root : Nat)`:
  accessibility for the exact `s.tables` scanner initial state, including an
  invalid root. This theorem needs no Store history because scan guards suffice.

The `History` premise is confined to construction of stored topology; it is not
used to assume whole inference termination. Finite-history preservation never
proves that the complete native operation history itself must be finite.

### Other Context traversal control actions

`traversalRank` assigns an unready frame `4^id` and a ready marker `1`, and sums
the pending stack. `two_children_with_ready_smaller` proves
`4^left + 4^right + 1 < 4^parent` for the native strict child guards.
`context_children_with_ready_smaller` covers all six `Expr` constructors.
`traversalRank_append`, `traversalRank_reverse`, `traversalRank_filter_le` and
`traversalChildren_rank` retain native stack order and completed-child filtering.

`ContextTraversalStep` overapproximates successful stack actions: pop, or a
validated descent to the actual constructor children, optionally retaining a
ready marker. Its `backwards` flag preserves the different next-pop order of
payload `extend_from_slice` versus postorder reversed pushes. It does not define
callback evaluation or replace source typing.

- `contextTraversal_decreases` derives strict rank descent from these actions.
- `contextTraversal_wellFounded` and
  `contextTraversal_varying_tables_wellFounded` prove fixed- and varying-table
  accessibility of that control projection, without a fixed global universe.
- `constructed_postorder_descent` obtains the actual strict child guard from a
  `NativeContextTables.History` and successful native table readback.

The Rust-to-control-step refinement and the callback bodies are distinct owners;
they have not been silently assumed as whole native termination.

### Exact non-termination of the unsuitable projection

`drain_projection_not_accessible (s : NativeDrainOwnership.State)` proves

```lean
¬ Acc (fun next prev => NativeDrainOwnership.Step prev next) s
```

It follows directly from the existing `Step.reserveOther`, not a newly invented
transition or source restriction. Its only authored-root axiom dependency is
standard `propext`. It prevents an invalid parent application; it does not imply
an actual source program can produce endlessly many reserve events.

## 4. Native source map and first remaining global premise

| Source owner at the frozen bytes | Relation to result / remaining obligation |
| --- | --- |
| `candidate_context.rs:3669–3766`, `candidate_zero_word_filters` | The `while let Some((id, mode))` scan corresponds to `scanStep`; exact guards require each child ID smaller before pushing. The proof covers this loop. The post-loop `consume` call is outside the scanner proof. |
| `candidate_context.rs:2630–2657`, `context`; `:2786–2792`, `assert_context` | New Context nodes refer only to retained IDs; old cache hits retain their original children. Store events supply the corresponding guard and now derive topology through complete Store histories. |
| `candidate_context.rs:1566–1660`, `rename_contexts_impl` | Source frontier check and strict child check precede postorder descent. A ready marker and a memo of verified source IDs control traversal; fresh outputs do not become old source inputs. Control rank applies; full rename/table/callback refinement remains separate. |
| `candidate_context.rs:1696–1724`, `context_payloads` | Visited IDs, at most two strictly earlier children, and reversed next-pop order; BothFromRight is rejected by this owner. Control rank applies; enclosing capture closure can request more roots. |
| `candidate_context.rs:1739–1784`, `fold_context` | Strict child check before postorder descent, ready marker, completed-result filtering. Control rank applies; arbitrary evaluation callback totality is not supplied. |
| `lib.rs:14235–14258`, `run_candidate_typed_drain`; `:14289–14420`, `step_typed_drain` | Outer `More` loop resets Transport after Context/dispatch and may receive newly enqueued work. No decreasing global measure or source-owned transition instance is constructed. |
| `lib.rs:13507–13518`, `pair_is_current`; `:15223–15253`, `enqueue_item` | Memo currency includes actual relation and intrusion generation. Endpoint-pair finiteness alone does not bound work. Queue insertion does not establish semantic completion. |
| `candidate_extrusion.rs:24–612`, `candidate_extrude` | Per-invocation polar row/structure memo, fresh copies at target levels, retained parent links, selected-bound replay, structures and View copies. A global bound on repeated calls/copies is not proved by structural `extrudeTerm` or this scanner rank. |
| `candidate_intrusion.rs:568–597`, `settle_candidate_intrusion`; `:598–710`, `merge_candidate_rows` | Pending cursor advances and merge generation changes; merging copies retained bounds and enqueues Replay. Whole progress must count generation invalidation and later extrusion roots, using current birth-level qualification. |
| `candidate_context.rs:3992–4080`, `candidate_context_begin_replay`; `:4156–4229`, consume/drive | New contextual relations/Replay dependencies and per-operation children are created. No-provenance drive queues work; synchronous provenance can enter a child drain. Local finite child vectors do not supply global child completion. |
| `candidate_extrusion.rs:1070–1116`, `candidate_replay_bound` | Meets the actual opposite-bound snapshot and starts/drives Replay. Source bounds/fibers themselves can grow outside one call. |
| `candidate_scheme.rs:2557–2710`, capture; `:4178` onward, fresh use | Capture repeatedly discovers rows, bounds, latent contexts and View tails; fresh use reconstructs structures, Contexts, scopes and later replay. Original source/capture/fresh-use closure and its allocation bound remain required. |

**First missing parent bridge:** there is no concrete whole-language
`SourceProblem` instance supplying `inferInitial`/`inferStep` in the current
Lean sources. A repository-wide search found the generic fields/definition in
`Contracts.lean` and generic parameter in `CoreComposition.lean`, but no
`inferStep :=`, `inferInitial :=`, or concrete instance. The parent cannot be
instantiated by treating finite histories or `NativeDrainOwnership.Step` as
the native algorithm.

The responsible owner is the primary native inference/proof integration lane.
It must construct/authenticate the original source initial and step relation,
then prove a source-owned global well-founded progress argument for repeated
allocation, contextual callbacks, extrusion/intrusion invalidation, Replay,
capture, and generalization. The scanner theorem discharges one exact local
operation in that future refinement. The ready-marker law and constructed
Store topology discharge local traversal-side premises once native control
readback is connected.

Do not replace the remaining argument with an assumed finite universe, a fixed
final graph, an accepted finite transcript, a normal-progress assumption, an
arbitrary fuel cap, or rejection of otherwise supported source. No source-qualified
counterexample to the original claim was found in this bounded packet.

## 5. Files, hashes and input consistency

Proof SHA-256: `26aca31b41897e297e516bf98b6e11d63dab50482a69f5b8a1f98a739696f946`

The primary advanced repository HEAD during parallel integration; the observed
HEAD at final hashing was `de313acb2bcfc193596898478caa3ad578b91d8d`. All **24** owning source/configuration/
import-dependency files listed below were compared byte-for-byte against the
assigned `a9c746f31cc0eabeba9ebf5b673b6f121ed0ca82` objects: **no drift**. Every
import dependency also matched the isolated verification snapshot. No shared
import/root, source, configuration, test expectation or status file was edited.

### Proof dependency SHA-256

| Module | SHA-256 |
| --- | --- |
| `YulangClosure.OriginalInferenceTermination` | `26aca31b41897e297e516bf98b6e11d63dab50482a69f5b8a1f98a739696f946` |
| `YulangClosure.Contracts` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `YulangClosure.NativeContextExpansion` | `9887bef34e51678cead77eaf84a2f9b47916987ea9cffaad5d4ef74d53de2ea8` |
| `YulangClosure.NativeReplayCurrent` | `fdd7dfa32f944f09b2cfc7440caeff95edcfad1fd5c839094f186d27168d9088` |
| `YulangClosure.NativeMergeExpansion` | `f14bd35e8f7a6b9f326dadf003797c63f4a48fd0d0c0c9d68891c579560baf6e` |
| `YulangClosure.NativeReplayCoverage` | `e65d925ab5222fd6bbc4bf63e756701aaba1273fff677ceb052d7f66e6450b7e` |
| `YulangClosure.NativeDrainOwnership` | `d37edac29dcecc19dd90b91c3095e5385a0657310dcf08d805a8f20672872d18` |
| `YulangClosure.NativeContextTables` | `eaf2b037af40af01ad116e1ae413a6c7d5a0023d49c8b9f1b92d29c319d2df81` |
| `YulangClosure.NativeExecutionHistory` | `44ad2a6d5b9ac0526ea36adc9180e0ed66e3892e48fa39aa40b20999dc7a1da6` |
| `YulangClosure.NativeValuePorts` | `f49bf12537633c65b4dbdcb4e739df5de5eee76cfb5ad845c8dba50cef4101fa` |
| `YulangClosure.NativeRecordPlan` | `3cf43fdb754748b83a6816791d640752dda491b87f7e2513a27548a950b27d43` |
| `YulangClosure.RecordBoundaryPreservation` | `1bde9224c1b0d568d5cc73d84a5ccc5f1157452c87ea2ff428096c1dbd50d056` |
| `YulangClosure.NativeContextReadback` | `321d087c8d2df5099f67beb75e4316d44114806bbfae2aa64ebda22a34bd83f2` |

### Owning source / authority / configuration SHA-256

| Path | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |
| `crates/yu-solver/src/candidate_context.rs` | `57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| `crates/yu-solver/src/candidate_scheme.rs` | `02349de1a2d69289eb348f7ff807a9e36faa2e2028cf61d10c1af9cd364409c5` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| `notes/design/2026-10-24-birth-level-scc-intrusion.md` | `ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae` |
| `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` | `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271` |
| `docs/yulang-whole-proof-closure-ja.md` | `17f7518e72f5977b17ce085523adc788ba72a472041555fd18a24da96b4c79a5` |
| `notes/theory/lean/lakefile.toml` | `cab85ff9a8a7dc5103fe932739dcea0dfc02e6420b1277565449882c802473bd` |
| `notes/theory/lean/lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `notes/theory/lean/lake-manifest.json` | `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3` |

## 6. Actual checker evidence

Read-only pinned toolchain:
`/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake`.
Actual `lake --version`: `Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)`.
Actual `lake env lean --version`: Lean 4.35.0, x86_64 Linux,
commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, Release.
The already installed toolchain was not modified. Tool execution used the
primary-described approved escalation because default sandbox execution could
not resolve this installed distribution's configuration. No installation ran.

Final checks, all exit **0**:

1. `lake --no-cache build +YulangClosure.OriginalInferenceTermination` —
   successful **14-job** dependency/module target; no new warnings.
2. Repository `check_lean.py --project /workspace/scratch/e3678bef96db/lean-termination-work
   --lake <absolute native lake> --module YulangClosure.OriginalInferenceTermination
   --theorem <16 principal roots> --timeout 120` — versions, actual module build,
   printed root types, declaration-kind checks and complete allowed-axiom audits.
   The exact command and full output are retained in
   `/workspace/scratch/e3678bef96db/lean-termination-work/check-original-termination.log`.
3. `lake --no-cache env lean -j1 -M1024 AuditOriginalInferenceTermination.lean` —
   complete census of **75 originating theorem constants**, including all **28
   authored roots**, private helpers and generated equation/termination theorems.
   Printed full types and complete per-theorem `#print axioms` results are in
   `/workspace/scratch/e3678bef96db/lean-termination-work/census-original-termination.log`.
   The census validates theorem origins, rejects originating project axioms,
   checks every authored root is included, and rejects any non-whitelisted
   indirect axiom.

Census outcome:

| Exact dependency set | Theorem constants |
| --- | ---: |
| none | 20 |
| `propext` | 5 |
| `propext`, `Quot.sound` | 50 |

There are **zero** `Classical.choice` dependencies in this new module's census,
zero project axioms, zero proof holes or kernel bypasses, and zero census
warnings/errors. Among the 28 authored roots, `traversalRank_append` and
`drain_projection_not_accessible` use only `propext`; the other 26 use
`propext, Quot.sound`. These are standard Lean axioms, so the proof is not
reported as axiom-free.

The complete existing default project target was not built by this leaf. It is
left to the primary's integration owner, as are shared imports/audit-root edits.
No Rust/Cargo test or compiler execution was run. Checks establish kernel
acceptance of the printed statements, not independent review or original native
source completeness.

Material development failures were repaired before the final checks:

- First build: constructor `prefix` needed escaped syntax `«prefix»`.
- Second build: `split` selected nested record conditionals rather than the
  reflected native guard; explicit `by_cases`/guard simplification fixed
  dependent elimination failures.
- A first successful-run equivalence proof generalized the wrong outer state;
  direct induction on the actual `ScanRun` replaced it.
- First traversal proof used a nonexistent `Bool.true_eq_true`, a non-definitional
  zero-add `rfl`, and omitted an explicit power-positivity fact needed by `omega`.
  Those are repaired; none of the failed builds is counted as successful evidence.

Scratch/cache owner: this leaf only, at
`/workspace/scratch/e3678bef96db/lean-termination-work`.
It contains the copied 161-file Lean snapshot, isolated `.lake`, audit source,
complete audit logs, root-name list and `termination-dependency-hashes.json`.
These are scratch verification outputs, not additional repository writes.
No children, background processes, Cargo process, installation or Git mutation.

## 7. Parent application, review seam and cessation

Before: the existing parser only supplied sufficient fuel from an already finite
successful `ScanRun`. After: its exact successful transition is accessible from
every scan state, its exact total outcome is constructed, and checker fuel is
proved sufficient and stable independently of successful transcript existence.
Store topology is derived from actual constructor/history events and reused by
the sibling control traversal argument.

Apply `native_context_scan_accessible` to the `candidate_zero_word_filters`
scan subtransition, and `scanLoop_eq_total`/`scanTotal_execution` to remove an
assumed parser transcript/fuel-completeness premise. Apply
`constructed_context_children` at the interner/readback boundary and
`constructed_postorder_descent` to corresponding native walk actions. This
reduces those local premises; it supplies neither the `consume` callback's
completion nor the original whole `SourceProblem.InferenceTermination`.

Required primary changes outside this lease: choose the intended public import
and audit integration target; add this module there if accepted; authenticate
its source-owner readback and retain the named full inference gate OPEN; assign
fresh independent review before status promotion. No source, fixture, supported
domain, semantic rule or runtime resource limit needs changing for this result.

**Writes stopped:** the Lean artifact and this handoff are frozen at submission;
all verification subprocesses have exited. No descendants or continuing writes.
Further changes require a primary-issued follow-up and invalidate the reviewed
hash. Independent review remains PENDING at this producer handoff.
