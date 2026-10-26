# Original selected Bound: physical insertion followed by its captured-fiber loop

## Status and exact claim

`lean/YulangClosure/OriginalBoundWorkExecution.lean` constructs and proves the scoped **Value** branch from an actual selected extrusion `Work::Bound` through physical copied-bound insertion and the first executable-fiber loop. Its terminal success label is `Outcome.originMetadata`: the later origin-metadata loop is still to be executed. This is not a theorem that the entire `Work::Bound`, extrusion, drain, or original inference procedure terminates.

The strongest generic result takes the result of the **whole composed computation**, including insertion's fallible pre-return operations. It derives an actual physical-slot readback of the copied bound and delivery of every relation entry in the source head captured from the initial physical table. Each delivered child has a complete native `Key`, the same raw child ID in the native interner and destination fiber, the actual source set and Flow, and the same-parent post-check Context. An unrelated intermediate physical state or a separately supplied finished-fiber premise is not an argument.

The file also applies the complete existing three-step row producer and proves a nonempty concrete execution with two original source fibers. Separate computations prove preservation of partial writes when sampling fails after physical insertion and when it fails after native child interning and destination attachment.

Frozen source SHA256:

```text
b6d3d2e7c9f14b87cce55f69e2cb8fd87269e282732bdefa685fb1bfeaf099f0
```

The direct source check and all-origin audit pass. The source has 802 lines and 37 authored theorem roots. The audit covers all 545 originating declarations, including 196 theorem constants and 33 private declarations. Every transitive axiom is within `propext`, `Classical.choice`, and `Quot.sound`; no new axiom, `sorryAx`, native evaluator axiom, or opaque declaration occurs.

## Native order and mode distinction

The source correspondence is the unchanged `crates/yu-solver/src/candidate_extrusion.rs`, `candidate_effect.rs`, and `candidate_context.rs`. The important ordering is:

| Native owner | Executed projection in this module |
| --- | --- |
| `Work::Bound`, extrusion lines 399–420 | Use the selected work item and rows-first memo hit to construct the complete `BoundRequest`; preserve the popped Work state. |
| `candidate_insert_copied_bound`, lines 619–643 | Check graph presence and scoped mode. In scoped mode, import the snapshot of the original bound with `relation=None` and the missing-origin-association gap. |
| `candidate_insert_bound_with_evidence`, lines 703–875 | Canonicalize the two insertion endpoints; check owner kind/range; select the exact Value row/atom vector; admit origin/evidence; reserve emission; journal; perform capacity operations; append. |
| Same insertion body after append | Perform flags/counter bookkeeping; read the exact physical slot; check its complete key; perform Value capture registration; mark dirty; emit evidence; sample; only then return normally. |
| `candidate_transfer_bound_origins`, effect lines 685 onward | Capture the actual source head and run `OriginalFiberTransfer.transferBound` on the physical state retained by the insertion. |
| The subsequent `for index in 0..count` origin loop | External owner. `Outcome.originMetadata` is the cut immediately before this loop. |

Capture registration belongs **before insertion returns and before the executable-fiber loop**. `candidate_register_capture_bound` matches only an Effect-row/negative/Allowance bound. Therefore its Value branch is an actual no-op; the module does not assume a successful Effect capture operation.

The scoped/unscoped distinction is material. At `candidate_effect.rs` lines 530–590, scoped `BoundTransport` deliberately has `relation=None`. Its origin and evidence bookkeeping does not create an executable relation fiber. Unscoped insertion uses `OwnerEmission`, which can call the executable relation owner before the physical append. The module therefore stops at `InsertOutcome.unscopedOwnerEmission` in that mode; it does not apply the scoped unchanged-fiber argument to unscoped insertion. `unscoped_stops` proves this exact branch. A well-addressed Effect insertion stops at the separately named `effectOwner` after snapshot import and before its admission/capture owner.

`scopedAdmission` constructs the entire admission request from the complete `BoundRequest`, antecedent readout, and current typed-pair scope or bound-pair fallback. `scoped_admission_whole` proves all those fields and `relation=None`. The native typed-pair scope and `Operation.processing`'s raw RelationId are distinct data; neither is cast into the other.

## State, readouts, and partial errors

`State M` contains the existing Work state, the existing native relation/fiber state `OriginalFiberTransfer.State`, scoped mode and typed-pair scope, opaque insertion bookkeeping `M`, a dirty bit, emitted receipts, and an operation trace. No supplied post-insertion state occurs in `insert`, `continueBound`, or `execute`.

`Observation M A` consists only of retained bookkeeping and `Except Nat A`. Its error number is an opaque readout of the named native availability/error operation; it is not a theorem of successful admission. `observe` retains the returned bookkeeping and records the call site before branching on success or error. Thus metadata writes that precede a failing admission or resource sample are retained.

The external insertion readouts have exact cuts: snapshot import; the scoped origin/evidence admission, including its own sample; emission reservation; row journaling; preflight/reservation/capacity accounting; infallible flags/counter accounting immediately after the push; evidence emission; and the final resource sample, including the enabled test-only emission probe. Physical Value vectors, canonical representatives, actual slot addressing/readback, dirty state, and retained emission records are computed here. The private origin/evidence tables, allocation capacities, journals, and counter implementations are not reconstructed from an arbitrary integer ID.

The `bookkeeping` field is explicitly a **before-loop checkpoint** once transfer begins. The imported transfer module owns the subsequent native relation/fiber state and receives its existing external snapshot, discharge/residual, dependency/evidence, resource, and sampling readouts. This module does not claim that transfer leaves its opaque metadata unchanged or that those internal metadata tables have been threaded as a full Rust-state semantics. Partial native interner/fiber writes from a transfer failure are retained in the returned `TF.State`.

`loopInputs` replaces both representative functions of each transfer readout with `inserted.state.work.qv` and `.qe`. Callers cannot provide unrelated Value/Effect representatives for this join. `physical_representatives` proves that the actual `OriginalExtrusionWork.physicalInsert` preserves these functions. Canonicalization is performed on the insertion endpoints; no idempotence premise or endpoint quotient is introduced.

## Executable composition and theorem types

The definitions are in `YulangClosure.OriginalBoundWorkExecution`; `W`, `TF`, and `F` below are its aliases for the frozen Work, transfer, and fiber owners. The following are the actual generic theorem interfaces.

```lean
theorem selected_bound_execution
    (calls : Calls M) (inputs : TF.Inputs)
    (funds : W.Funding) (state : State M)
    (owner : Endpoint) (polarity : Polarity)
    (child : OriginalExtrusionWork.CopyKey) (original : RawBound)
    (popped : W.State) (copied : Endpoint)
    (selected : OriginalExtrusionWork.select state.work =
      some (.bound owner polarity child original, popped))
    (memo : popped.lookup child = some copied) :
    execute calls inputs funds state =
      continueBound calls inputs {state with work := popped}
        (W.boundRequest popped owner polarity copied original)

theorem bound_at_metadata
    (calls : Calls M) (inputs : TF.Inputs) (state : State M)
    (request : BoundRequest)
    (normal : (continueBound calls inputs state request).outcome =
      .originMetadata) :
    AtOriginMetadata state request (continueBound calls inputs state request)

theorem every_captured_delivered
    (calls : Calls M) (inputs : TF.Inputs)
    (state : State M) (request : BoundRequest)
    (normal : (continueBound calls inputs state request).outcome =
      .originMetadata)
    (index : Nat) (entry : OriginalBoundFibers.Entry RawBound)
    (captured : (index, entry) ∈ F.walk
      state.transfer.physical.fibers.entries state.transfer.valid.backward
      (state.transfer.physical.fibers.heads request.original)) :
    ∃ call ∈ (continueBound calls inputs state request).calls,
      call.index = index ∧ call.entry = entry ∧
      TF.Delivered (canonicalRequest state.work request)
        (continueBound calls inputs state request).state.transfer call
```

`AtOriginMetadata before request result` expands to the following complete output statement. It is proved, not stored in any machine input or external readout.

```lean
∃ slot,
  result.request = some (canonicalRequest before.work request) ∧
  result.slot = some slot ∧
  readback result.state.work slot =
    some (canonicalRequest before.work request).destination ∧
  result.state.dirty = true ∧
  result.state.work.qv = before.work.qv ∧
  result.state.work.qe = before.work.qe ∧
  result.calls.map (fun call => (call.index, call.entry)) =
    F.walk before.transfer.physical.fibers.entries
      before.transfer.valid.backward
      (before.transfer.physical.fibers.heads request.original) ∧
  ∀ call ∈ result.calls,
    call.entry.key = request.original ∧
    TF.Delivered (canonicalRequest before.work request)
      result.state.transfer call ∧
    call.parameters.readout.valueRepresentative = result.state.work.qv ∧
    call.parameters.readout.effectRepresentative = result.state.work.qe
```

The imported `TF.Delivered` supplies actual parent readback, computed `boundPair`, computed two-position scoped-root remapping, a complete `Key` whose pair is renamed by the stated representatives, `postContext` using that same raw parent, unchanged complete source set, the full remapped Flow, native admissibility, preservation of the four non-root demand fields and transformer, final native readback at `call.child`, and membership of **that same `call.child`** in the destination bound's fiber. It is not merely semantic equivalence or endpoint membership.

The proof proceeds through executable insertion stages. `insert_retains` derives that scoped Value insertion does not mutate the native relation/fiber state; `insert_ready` derives the actual physical readback and representative preservation. `continueBound` computes its own insertion result and passes its own retained `TF.State` to `TF.transferBound`. Only after destructing this whole result does `bound_at_metadata` derive normal completion of that particular transfer call and apply the frozen coverage theorem. Rewriting with insertion preservation identifies the captured list with the initial physical table. The theorem does not take transfer completion or delivery as a separate hypothesis.

## Application to the complete row producer

`Computed.rowExecution` consumes:

```lean
W.runPrefix W.funded 3 (OriginalExtrusionWork.Computed.rowInput caller)
```

`row_execution_dispatch` rewrites this actual three-step Visit/Visit/Bound run using `OriginalExtrusionWork.Computed.row_bound_produced`. It obtains the exact computed `rowBoundState` and `rowBoundRequest`. `row_execution_at_metadata` then applies the composed result theorem. The complete caller, endpoint data, and Operation remain in that request; no new caller certificate is supplied. A Function endpoint remains its actual term reference; this Value-row packet does not reconstruct its four stored ports.

```lean
theorem Computed.row_execution_at_metadata
    (calls : Calls M) (inputs : TF.Inputs) (state : State M)
    (caller : NativeValueStructure.Request)
    (normal : (Computed.rowExecution calls inputs state caller).outcome =
      .originMetadata) :
    AtOriginMetadata
      {state with work := OriginalExtrusionWork.Computed.rowBoundState caller}
      (OriginalExtrusionWork.Computed.rowBoundRequest caller)
      (Computed.rowExecution calls inputs state caller)
```

This use has an explicit initial-cut boundary. The earlier row-copy source link already changes the physical Value row and can create its own executable fiber in the full native implementation. The argument of `rowExecution` supplies the native relation/fiber state **at the selected Bound cut**. This module does not assert that the earlier complete Work prefix leaves that state unchanged, and does not extract all earlier source-link metadata operations from Rust.

The concrete example independently constructs the source fibers and a source-link fiber using `OriginalBoundFibers.publish`, which itself calls the actual native interner and linked attachment. Validity and native history are derived from the empty state and those calls. No raw relation identity or fiber membership is inserted as a proof premise.

## Computed success and retained failures

The explicit caller has nontrivial Context, sources, and all five ScopedDemand fields. The source keys also retain complete scoped demands. The following facts are kernel-proved from the executable definitions.

| Computed item | Exact result |
| --- | --- |
| Source bound | `(Value row 0, Negative, Value row 1)` |
| Copied destination | `(Value row 2, Negative, Value row 1)` |
| Original source fiber, newest first | `[1, 0]` |
| Earlier source-link bound | `(Value row 0, Positive, Value row 2)`, fiber `[2]` |
| Actual source/child calls | `[(1, 3), (0, 4)]` |
| Final destination fiber | `[4, 3]` |
| Child 3 | Source key 1 with pair changed to `row 2 < row 1` and Context changed from 1 to 0 by the readout for parent 1; full sources and Flow retained. |
| Child 4 | Source key 0 with pair changed to `row 2 < row 1`; full Context, sources, and Flow retained. |
| Physical insertion | Row 2's selected upper vector becomes `[1]`; dirty is true. |

`sources_generated`, `row_first_loop_complete`, `row_exact_children`, and `row_all_captured` provide the successful example. The first two source keys contain demands `(originalCall,useInstance,root,outputScope,inputRoute) = (3,4,700,5,6)` and `(7,8,701,9,10)`, with source sets 42 and 43. The row-only remap retains those demand records in full. The complete caller remains the caller in the generated Work request; the fixture does not claim to derive its IDs or `Operation.processing = some 52` from a whole source elaboration or to authenticate that processing ID against this small separately generated native history.

`sample_failure_keeps_append` is universally quantified over the complete caller. It supplies an error readout at the insertion's final sample, after emission. The result is `insertionFailed`, with row 2's upper vector `[1]`, dirty true, the emission receipt retained, the original native relation/fiber state retained, and no transfer calls. Its retained insertion outcome is exactly `.failed (.native .sample 17)`.

`fiber_sample_failure_keeps_partial` fails the first transfer body's sample after native interning and attachment. It returns `.fiberFailure (.transferFailure (.published (.sampleFailure 3)))`; the physical row append remains, raw child 3 has its complete `secondChild` key, and the destination fiber is `[3]`. Raw child 4 is absent. The failing body is not reported as a completed call and the next captured parent has not been transferred.

The closed computational witnesses use ordinary `decide +kernel`. The kernel checks their reductions, including well-founded cursor computations. A diagnostic `#eval` probe was used during construction to distinguish a reduction problem from a wrong branch; its results are not premises or proof evidence.

## Contribution to NQ and remaining owners

This packet directly supplies the selected copied-row edge operation needed by section 6.1 of `2026-10-26-native-copy-quiescence-obstruction.md`: physical copied-bound storage occurs first, and every captured source relation is then transported and attached to that destination before this first-loop cut is reached. It preserves raw identities and complete keys, and does not infer a fiber from the later origin table.

The following remain open at this packet's boundary:

- Native source extraction connecting the initial Work/native/fiber projections, the copied-path seed, actual call readouts, and the entire earlier source-link prefix.
- Internal origin/evidence snapshot/admission/emission, journaling and capacity owners, and their full metadata-state evolution through the imported transfer body.
- The unscoped OwnerEmission branch, Effect insertion/capture, and the later origin-metadata loop. No theorem here calls the first-loop cut full Work completion.
- All selected Bound operations along a source-specific copied path, completion of the surrounding eight-variant extrusion, four-port construction/enqueue, ordinary replay ownership, first-boundary processing, and the final anchored-successor argument as one extracted execution.
- Whole original-language inference termination, divergence/NQ for the supported source, soundness, Effect hygiene, and principality. No global source cardinality, fuel, fairness law, finite-universe assumption, source-bounded allocation theorem, or assumed successor has been introduced.

The input `TF.State` retains the already frozen owner model's native-history and linked-table validity proofs. These are formation requirements of that input representation, not output safety certificates in `Calls`. The concrete `seed` computations construct them. This module does not claim that every original Rust state has already been extracted into that representation.

## Checks and audit receipt

The authorized direct-check command was:

```text
timeout 120 /workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake env lean -j1 -M1024 YulangClosure/OriginalBoundWorkExecution.lean
```

Working directory: `notes/theory/lean`. No `-o` argument or cache/build invocation was used by this leaf. Check 11 exited 0 with no warnings or errors; its log is `/tmp/yulang-bound-work-execution/check-11.log`, SHA256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

Eleven of the 18 proof/diagnostic invocations were used. Earlier evidence remains in the same scratch directory: parsing/elaboration failures; one 1 GiB kernel-memory failure before factoring the insertion stages; a heartbeat limit in a fully expanded preservation proof, repaired by stage lemmas; reductions stuck behind imported well-founded proofs; the diagnostic evaluator probe; and the requirement to close the two computational propositions over an explicit caller. No project/global resource option was changed, and the final proof check uses the original 120-second/1 GiB envelope.

After the source hash was frozen, the root built it successfully in the shared cache: `/tmp/yulang-name-bound-work-build.log`, combined 42-job build, exit 0 with zero diagnostics. The leaf then ran one of its two permitted audit invocations, using `-j1 -M2048` solely for the full type/axiom printer census. The source hash was rechecked unchanged.

The audit selects declarations by their actual origin module index, not by a namespace prefix. It explicitly checks all 37 authored theorem roots and then every originating declaration's complete type and transitive axioms, including generated/private theorem constants. Its census is:

| Declaration kind | Count |
| --- | ---: |
| Definitions | 286 |
| Theorem constants | 196 |
| Constructors | 37 |
| Inductive declarations | 13 |
| Recursors | 13 |
| Total | 545 |

There are 545 matched begin/end audit records, 33 private declarations, no target axioms or opaque declarations, and no warning/error diagnostics. The audit rejects any transitive axiom outside `propext`, `Classical.choice`, and `Quot.sound` and exited 0.

Audit artifacts:

```text
/tmp/yulang-bound-work-execution/AuditFull.lean
SHA256 744c28aa71dceec8524cccd39b2fa6986580ef377fbf440030a471e7d07baeec

/tmp/yulang-bound-work-execution/audit-01.log
SHA256 ad338f5695de78bb29a02fbe40ee79a5f46e5230b475d503bc4b831214fd5f75

/tmp/yulang-bound-work-execution/authored-roots.txt
SHA256 42720d1fbd941fc1f78fee7ddd387af43235c7d0bed9b287b4b713c3bbc9cb01
```

## Frozen inputs and native-owner hashes

```text
OriginalExtrusionWork.lean
c419675d75a2cdf03fe5b1ba8d2eef106fea0c4f5187f9f5c06999fa734edd58
OriginalExtrusionFibers.lean
15bb4ebc67a22f4bd3af584e8377dec210963f7cbba43e6072c82b5f2d5a8800
OriginalFiberTransfer.lean
2d368cfe99240d7c4a5cb7618acd7bedd3a569978735b27a1b3b23a1626566ba
OriginalBoundFibers.lean
1a512b23a55936e30088763d46d3f71458cec953b58edbf794e28bb13eaf0ca5

crates/yu-solver/src/candidate_extrusion.rs
80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61
crates/yu-solver/src/candidate_effect.rs
70c42056a1041d54f88f16d7712875e3acf9ef7649b99a34bc990ff19f04936f
crates/yu-solver/src/candidate_context.rs
57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e
```

The only repository writes for this packet are the new Lean module and this note. There were no Rust, frozen dependency, root import, build/cache, Git, or shared-status edits, and no child agent was used. Independent review is a separate owner and is not claimed by this producer receipt.
