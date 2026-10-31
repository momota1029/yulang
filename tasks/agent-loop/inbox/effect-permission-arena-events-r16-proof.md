# R16 proof handoff — rev2

Sprint: EFFECT-PERMISSION-ARENA-EVENTS/20261029-r16. Proof owner: `/root/effect_permission_arena_events_r16_lean`. Primary/cache/audit owner: Luna. Exactly two leased writes: `notes/theory/lean/YulangClosure/FormalPermissionArenaEvents.lean` and this handoff. No descendants, Rust changes, tests, Cargo, probes, instrumentation, dependency/configuration edits or Git operations.

Status: CONSTRUCTED REV2, NOT YET CHECKED. Rev1 failed primary Audit 1; rev2 is frozen for the final permitted primary audit; no claim of kernel acceptance, independent review, native correspondence or production authority. The primary alone may run the packet's at most two audits (each ≤90 seconds, combined ≤120 seconds) in its isolated `/tmp/yulang-effect-permission-arena-events-20261029-r16/` project. No Lean/Lake/version/checker process has been run by this worker. The worker has no independent execution receipt. Primary Audit 1 has the actual version/exit/failure evidence below; no public root type or axiom reports were reached. The local files pin `leanprover/lean4:v4.35.0`, `-j1`, `-M1024`, and zero external packages; installed executable/version validation belongs to the audit owner.

## Governing sources and exact parent

Read root AGENTS.md and AGENTS.pre-sprint.md, rules/goal-driven-sprints.md, rules/design-authority.md, the Lean skill plus references/sources.md and references/execution.md, current.json/README, the fixed R16 contract/input manifest/source handoff, and actual R15 declarations. Original parent: `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §§1,3,5; current immutable-birth qualification correction: `notes/design/2026-10-24-birth-level-scc-intrusion.md` §§2–6, under the 2026-10-11 top-level principles. The original parent retains every supported original source program, every lawful finite construction history, actual occurrences, original scopes and one shared source-admissible witness/strategy. R16 does not narrow that parent. Research drafts are not semantic authority.

Actual source inspected: `term.rs` TermCapacityEvents::push/take (566–590), record_capacity_change (961 onward), BranchTermArena::push/intern (1083–1203), live_variable/positive_function/negative_function (1205–1274); `lib.rs::with_term_events` (10594 onward); `candidate_effect.rs::candidate_formal_value_pair` (1617 onward). Read `YulangClosure.Contracts.SourceProblem` and its `InferenceSoundness`, `SourceScopedCoverage`, `PrincipalCoverage`, `NativeCorrespondence`, `InferenceTermination` definitions; those are propositions, not concrete proofs. Read R15 `exact_tree_r9_from_term_control` and its explicit length/aligned/reservation/source-call premises.

## Model and scope

Namespace: `YulangClosure.FormalPermissionArenaEvents`. `Mode` has exactly liveVariable, positiveFunction, negativeFunction, the fixed packet's selected protocol; this is a scoped auxiliary model, not a restriction of supported Yulang. Function `childrenValid` is an observation of all four source checks, retaining the actual polarity-specific kind constraints as a source correspondence obligation. Cache hits and invalid function children produce no new events. Live variables do not use child validation.

`ReserveOutcome` keeps changed-capacity and reserve-success observations independent. A changed reserve emits its snapshot before success is inspected, including a failed reserve. `Publication` distinguishes allocation failure, identity-claim failure and publication; only the latter can emit PageBacking. The six ordered slots are Interner, optional InternedJournal, PageDescriptors, PagePositions, optional ClaimedPagesJournal, PageBacking. Disabled journal/page slots are identities. `run` executes the prefix through the first failure, including its own emitted event, and omits all later stages. The final list is derived from these fixed slots and observations; it is never supplied as an arbitrary final event list.

`events prefix i` keeps the arbitrary preexisting buffer prefix, appending the derived suffix. `Fits prefix i` is the exact combined-size precondition for the source buffer's len<6 assertion. The unconditional new-event bound does not establish this precondition. `each_append_has_slot` proves every intermediate append assertion under it. A prefix of length six and any nonempty appended suffix is an explicit excluded-overflow execution, not silently assumed executable. Initial-buffer provenance is not established.

Represented: both function polarities/live variables; valid/invalid function checks; cache hits/misses; journal present/absent; current-page space/new page; every reserve changed/unchanged and success/error combination; allocation/identity failure/publication; arbitrary old prefixes; either accounting flag and opaque constructor result via R15; sampler errors including partial counter effects via inherited control. Omitted: tuple/record/variant/structural-backed constructors and their events, whole caller reconstruction, actual allocator/native execution, and general source closure. Those cases remain parent obligations, not removed source cases.

## Remaining premises and parent application

1. Primitive reserve/allocator behavior: actual reserve_f5b result, whether selected lane capacity changed even on error, successful memory availability, and eventual node insertion. Owner: primary source/implementation lane.
2. Snapshot correspondence: each EventOutcome.snapshot is the full actual post-attempt capacity vector encoding; the payload Nat is opaque and supplies no authenticity. Owner: source/implementation.
3. Buffer provenance and nonoverflow: the supplied prefix is precisely the actual old ordered buffer; Fits holds on each actual execution; the drain resets storage. Owner: source/implementation. R15 supplies only abstract drain behavior.
4. Page identity/publication: native claim authenticity, fresh/nonreused identity, successful page-position insertion and page publication agree with Publication.published. No invented native identity is introduced. Owner: source/native implementation.
5. Child/cache/journal/page state: observations agree with actual constructor entry and the proper child polarity/kind checks. Owner: source/implementation.
6. Sampler: supplied observations are the outcomes of actual ordered sampler calls, including failed partial counter writes and availability; no success is inferred from the model. Owner: primary sampler/execution lane.
7. Actual execution and call correspondence: constructor outcome, arena state, buffer/event observations, source path and accounting state agree with Rust execution; positive/negative caller sequencing carries the same actual children/witnesses. Owner: primary source/native lane.

`derived_control_refines` applies R15 `control_ops_refine` directly to the prefix plus the constructed event suffix, for every constructor outcome/accounting flag/HelperState. `derived_constructor_error_preserved` applies R15's error result theorem with every sample-success premise explicit. R15 `exact_tree_r9_from_term_control` remains conditional on its SourceCalls, aligned allocator and reservations; R16 does not supply a whole SourceCalls instance because tuple cases and actual successful constructor/sampler/native execution remain open. First remaining premise for a concrete application: actual Rust constructor/event observations and buffer provenance/Fits linked to this Input at the same state/path; owner Luna's source/implementation lane. Full inference soundness/coverage/principality/termination, hygiene, consumer residual, native correspondence and production remain OPEN.

## Commands and receipts

Actual worker commands: read-only `cat`, `sed`, `rg`, Python JSON/hash inspection, `sha256sum`; leased-file construction via apply_patch and Python. All returned exit 0 except the source API search over a nonexistent `/tmp/lean*` glob returned exit 2 while finding the installed pinned list API declarations; that was read-only lookup, not a Lean execution or mathematical failure. Local pinned source consulted: `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/src/lean/Init/Data/List/{Basic,Sublist,Lemmas}.lean`. Primary Audit 1 failure is retained below. The worker did not run Lean/Lake or any diagnostic probe. Primary must preserve any audit stdout/stderr/status/resource records and inspect every printed type/axiom list for inherited 38 roots plus all new public roots below.

## Frozen dependency hashes

- `notes/theory/lean/YulangClosure/FormalPermissionArenaEvents.lean`: `02ef97716d882073ccb2e53c53bbf8046c80e82a517253898db5d1c02cd1b8b3` (10043 bytes).
- `notes/theory/lean/YulangClosure/FormalPermissionTermCallControl.lean`: `73bface0963c65eb76933ff8116594b161e78f1733b66e6be25cc174d1eb2dd7` (18303 bytes).
- `notes/theory/2026-10-13-intrusion-source-preservation-proof.md`: `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271` (34671 bytes).
- `notes/design/2026-10-24-birth-level-scc-intrusion.md`: `ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae` (7812 bytes).
- `crates/yu-solver/src/term.rs`: `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1` (82419 bytes).
- `crates/yu-solver/src/lib.rs`: `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` (1649811 bytes).
- `crates/yu-solver/src/candidate_effect.rs`: `1f64d4fec8f2abceb11a48a51f5b615aa2cf605c9586ba742f15f9024a6a2717` (342035 bytes).
- `tasks/agent-loop/sprints/effect-permission-arena-events-20261029-r16-inputs.json`: `f4174b99fe8f4c9935740cd3d0a5183cdaab601818d834a6df02370d5668aa18` (46979 bytes).

## Actual primary Audit 1 and rev2 repair

The worker read the complete primary-owned `/tmp/yulang-effect-permission-arena-events-20261029-r16/attempt-1/stdout.raw` and `stderr.raw`. Rev1 input artifact SHA-256: `55f7935cc170c87c388c202594d625c18c1744cc68b9e85211e2fe20a4a2b6e7`. Actual primary commands recorded there, cwd `attempt-1/project`:

```sh
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake --version
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake --no-cache env lean --version
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake --no-cache build +YulangClosure.FormalPermissionArenaEvents
```

Actual versions: Lake `5.0.0-src+eb6cafb` (Lean `4.35.0`), Lean `4.35.0`, x86_64-unknown-linux-gnu, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, Release. Version commands exit 0. Build exit 1. Primary reported 4.694 seconds and 754648 KiB peak RSS. Inherited dependency builds replayed; the new module failed before printed theorem/axiom queries. No axiom result is claimed.

Material diagnostics: unopened scoped `<+` notation parsed the `+` unexpectedly at lines 96/108; that cascaded into appended_bound. Reserved keyword `prefix` caused binder/parser errors from line 202 onward. In backing_requires_publication, the sixth membership branch still had `a = publicationAttempt i ∨ a ∈ []`, so `subst a` failed. Complete evidence remains in the primary-owned attempt directory and is not overwritten.

Rev2 repairs only construction syntax/proof case handling: explicitly use `List.Sublist`, rename the binder to `oldEvents`, and simplify empty-list membership before the six branch split. No conclusions, cases, reserve/event behavior or hypotheses changed. No extra Lean/Lake probe was run. Rev2 has not yet received kernel acceptance or axiom audit; Audit 2 belongs to Luna and is the final allowed run. A failed Audit 2 must remain open under the fixed budget, without a third run.

## Public theorem declarations (rev2 source types; pending printed audit)

```lean
theorem YulangClosure.FormalPermissionArenaEvents.run_order (as : List Attempt) :
    List.Sublist ((run as).map Event.lane) (as.map Attempt.lane)
```

```lean
theorem YulangClosure.FormalPermissionArenaEvents.appended_order (i : Input) :
    List.Sublist ((appended i).map Event.lane) canonical
```

```lean
theorem YulangClosure.FormalPermissionArenaEvents.appended_bound (i : Input) : (appended i).length ≤ 6
```

```lean
theorem YulangClosure.FormalPermissionArenaEvents.disabled_reserve (lane : Lane) (o : ReserveOutcome) :
    emitted (reserve lane false o) = [] ∧
    (reserve lane false o).succeeded = true
```

```lean
theorem YulangClosure.FormalPermissionArenaEvents.failed_reserve_growth_retained (lane : Lane) (o : ReserveOutcome)
    (changed : o.changed = true) (failed : o.succeeded = false)
    (rest : List Attempt) :
    run (reserve lane true o :: rest) = [⟨lane, o.observation⟩]
```

```lean
theorem YulangClosure.FormalPermissionArenaEvents.unchanged_reserve_emits_nothing (lane : Lane) (o : ReserveOutcome)
    (unchanged : o.changed = false) : emitted (reserve lane true o) = []
```

```lean
theorem YulangClosure.FormalPermissionArenaEvents.run_append_success (before after : List Attempt)
    (success : ∀ a ∈ before, a.succeeded = true) :
    run (before ++ after) = run before ++ run after
```

```lean
theorem YulangClosure.FormalPermissionArenaEvents.failure_preserves_prefix (before after : List Attempt) (a : Attempt)
    (success : ∀ b ∈ before, b.succeeded = true) (failed : a.succeeded = false) :
    run (before ++ a :: after) = run before ++ emitted a
```

```lean
theorem YulangClosure.FormalPermissionArenaEvents.cache_hit_no_events (i : Input) (hit : i.cacheHit = true) :
    appended i = []
```

```lean
theorem YulangClosure.FormalPermissionArenaEvents.invalid_function_no_events (i : Input)
    (function : i.mode = .positiveFunction ∨ i.mode = .negativeFunction)
    (invalid : i.childrenValid = false) : appended i = []
```

```lean
theorem YulangClosure.FormalPermissionArenaEvents.publication_stage (i : Input) :
    emitted (publicationAttempt i) =
      (if i.pageNeeded && published i then [⟨.pageBacking, i.backingObservation⟩] else [])
```

```lean
theorem YulangClosure.FormalPermissionArenaEvents.publication_failure_no_backing_stage (i : Input)
    (failed : i.publication ≠ .published) :
    emitted (publicationAttempt i) = []
```

```lean
theorem YulangClosure.FormalPermissionArenaEvents.backing_requires_publication (i : Input) (e : Event)
    (member : e ∈ appended i) (backing : e.lane = .pageBacking) :
    i.pageNeeded = true ∧ i.publication = .published
```

```lean
theorem YulangClosure.FormalPermissionArenaEvents.combined_prefix_bound (oldEvents : List EventOutcome) (i : Input)
    (fits : Fits oldEvents i) : (events oldEvents i).length ≤ 6
```

```lean
theorem YulangClosure.FormalPermissionArenaEvents.each_append_has_slot (oldEvents : List EventOutcome) (i : Input)
    (fits : Fits oldEvents i) (n : Nat) (pending : n < (appended i).length) :
    oldEvents.length + n < 6
```

```lean
theorem YulangClosure.FormalPermissionArenaEvents.preexisting_prefix_preserved (oldEvents : List EventOutcome) (i : Input) :
    events oldEvents i = oldEvents ++ (appended i).map Event.observation
```

```lean
theorem YulangClosure.FormalPermissionArenaEvents.derived_control_refines (oldEvents : List EventOutcome) (i : Input)
    (constructor : ConstructorOutcome) (accounting : Bool) (s : HelperState) :
    runOps (controlOps constructor (events oldEvents i) accounting s) s =
      controlState constructor (events oldEvents i) accounting s
```

```lean
theorem YulangClosure.FormalPermissionArenaEvents.derived_constructor_error_preserved (oldEvents : List EventOutcome) (i : Input)
    (constructor : ConstructorOutcome) (accounting : Bool) (errorMap : Nat → Nat)
    (error : Nat) (failed : constructor.result = .error error)
    (samplesOk : AllSamplesOk (events oldEvents i)) :
    controlResult errorMap constructor (events oldEvents i) accounting = .error (errorMap error)
```

Resource use: one proof leaf under its 600-second lease; no descendants, worker build/cache/scratch outputs or worker Lean processes. Primary owns all audit resources and the isolated generated outputs. WRITES STOPPED on both leased paths at rev2. All original parent obligations and concrete execution bridges listed above remain OPEN. Further acceptance/review/production adjudication is primary-owned.
