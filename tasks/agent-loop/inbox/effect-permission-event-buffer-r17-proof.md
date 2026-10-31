# R17 proof handoff — rev1

Sprint: EFFECT-PERMISSION-EVENT-BUFFER/20261029-r17. Assignment: bounded R17 Lean leaf; owner `/root/effect_permission_event_buffer_r17_lean`. Exactly two writes: `notes/theory/lean/YulangClosure/FormalPermissionEventBuffer.lean` and this handoff. No descendants or writes to compiler, tests, shared records, configuration, toolchain, dependencies, root imports or other workers' files. No Git actions.

Status: CONSTRUCTED, UNCHECKED, frozen for primary Audit 1. No worker Lean/Lake/version/checker/probe/test/Cargo/Rust execution. The primary owns the pinned Lean 4.35.0 isolated project/cache and at most two audits (each ≤90 seconds; combined ≤120 seconds). No printed types or axiom results exist from this worker; source declaration types below are not runtime receipts. Independent review, source/native correspondence and production authority are not established.

## Governing sources and parent

Read AGENTS.md, AGENTS.pre-sprint.md, rules/goal-driven-sprints.md, rules/design-authority.md, current.json/README, fixed R17 contract/input manifest/source handoff, yulang-lean-proofs SKILL.md and references/sources.md and execution.md. Read actual R16 definitions and the relevant inherited R15 control definitions. Pins read: `lean-toolchain` = `leanprover/lean4:v4.35.0`; lakefile uses `-j1`, `-M1024`; manifest has zero external packages. Installed version execution is reserved for Luna.

Original parent: `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §§1,3,5, under `notes/design/2026-10-11-yulang-inference-top-level-principles.md` and immutable birth qualification correction `notes/design/2026-10-24-birth-level-scc-intrusion.md` §§2–6. The original claim ranges over every supported original source program, lawful finite construction history and actual retained occurrence; it preserves original source scopes and one joint source-admissible strategy/witness. This auxiliary selected constructor model does not narrow that original language or establish the original preservation theorem. Research drafts supply no semantic authority.

Read `YulangClosure.SourceProblem.InferenceSoundness`, `SourceScopedCoverage`, `PrincipalCoverage`, `NativeCorrespondence`, `InferenceTermination` in Contracts.lean. InferenceSoundness remains the original universally quantified successful-generation/solve implication with existence of one original source judgment and sameScoped witness. These are proposition definitions, not concrete instances.

Source inspected: `term.rs` 566–590 (`TermCapacityEvents::new/push/take`), 955–981 (`take_capacity_events`, `record_capacity_change`) and production push-site search (981,1151,1371,1380); `lib.rs` 10594–10622 (`with_term_events`). Source handoff identifies both intern_structure structural writers. Four direct production append sites are preserved; no global constructor bound or structural maximum is certified.

## Representation and claims

Namespace: `YulangClosure.FormalPermissionEventBuffer`. `Buffer α` has an actual `Array (Option α)`, independent Nat `len`, and fixed array-size proof =6. `Layout b xs` records len=length xs, length≤6, and the exact whole-array list `xs.map some ++ replicate (6-length xs) none`. This expresses every occupied slot and every empty suffix slot, preserving repeated snapshot values in their original positions. It is an invariant to be proved, not the buffer's definition.

`push` writes Some x at exactly len using setIfInBounds, increments len and preserves array size. Its explicit len<6 proof represents the source assertion's successful branch; no overflow is translated into Result error. `push_writes_next` proves the physical target index receives Some x. `push_layout` derives the new layout for `xs ++ [x]`. `Appends` is the finite relation of actual bounded pushes; appends_exists constructs a normal sequence from combined size, while appends_layout proves its invariant and order. Arbitrary old prefixes are kept separately.

`take b = (b, empty)` models whole-structure mem::replace. `take_exact_reset` exposes old-buffer identity, zero len and all six slots None. `flatten` scans the entire array with filterMap id, deliberately ignoring len like Rust's iterator flatten. flatten_exact and take_events_exact derive exact ordered equality to xs, hence no omission, duplicate insertion, reorder or stale suffix. Equal values that were already duplicated in xs remain duplicated.

`appended_empty_fits` applies R16 appended_bound directly; selected_empty_execution constructs the bounded push trace for the six-stage selected live-variable/positive-function/negative-function suffix. No Fits conclusion is inferred for arbitrary prefixes. appends_exists requires their combined bound; selected_prefix_finish retains their exact events and an executed Appends trace.

`finish` begins only after the constructor closure returns normally, with either constructor Result. It takes the buffer before calling inherited controlResult/controlState. The sampler/control functions have no Buffer argument, reflecting this selected source path's separate counter writes and no arena mutation. finish_empty holds regardless of constructor/sampler Result. finish_constructor_error additionally identifies the mapped constructor error when all samples succeed; finish_sampler_error identifies an early sample error after any successful prefix, and both prove reset. No-accounting follows the inherited false branch. A constructor/sampler panic before drain has no finish call and is not claimed recoverable.

consecutive_selected_entry carries explicit equality between next entry and the returned post-wrapper buffer: exactly the no-direct/interleaved-mutation premise. It derives empty layout, R16 Fits [] and the next selected bounded execution. This is a two-call composition step, iterable for selected calls, not a proof of the complete recursive candidate caller.

## Parent application and first remaining premises

selected_control_refines applies the concrete array drain equality to R16 derived_control_refines, hence R15 control_ops_refine on events old i. selected_prefix_finish gives the exact inherited result and state together with the concrete reset. consecutive_selected_entry supplies R16's empty-entry Fits for the next selected wrapper. It does not supply R15 exact_tree_r9_from_term_control's whole SourceCalls/reservation/alignment instance.

First remaining concrete application premise: actual Rust constructor execution, observed reserve/cache/page/child outcomes, event snapshots and buffer provenance agree with this Input and Appends trace at the same selected source path. Owner: Luna's source/native implementation lane. For a next wrapper the no-direct/interleaved-mutation equality must hold for that actual path. Normal constructor return excludes pre-drain panic; overflow is not a recoverable Result branch. Sampler outcomes/availability, physical snapshot authenticity, actual allocator behavior, page identity and native decode remain separate source/native premises owned by the primary. Full recursive candidate caller (including recursive argument/result/effect routes), tuple/variant/record structural constructors and intern_structure maximum batch remain OPEN. Original shared witness/source completeness, soundness, principality, termination, effect hygiene, consumer residual and production remain OPEN.

## Commands, evidence and resources

Actual worker actions: read-only cat/sed/rg/ls, Python source/JSON/hash processing, sha256sum, and apply_patch on the two leased paths. Read commands returned exit 0 except final ls of the not-yet-created output paths returned exit 2 (both absent; no conflict). No runtime proof checker or version command was invoked. Pinned standard-library APIs consulted under `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/src/lean/Init/Data/{Array,List}/{Basic,Lemmas}.lean`. Source safety scan found no sorry/admit/project-axiom/checker-bypass declarations; the English comment containing “admitted” is not a tactic. No Lean-generated files or scratch files were written by this worker. Kernel/axiom results: NOT RUN; actual diagnostics must be supplied by primary Audit 1. There is no concrete mathematical counterexample at construction time.

Finite construction budget: 600 seconds from dispatch; no worker Lean processes, descendants or external contacts. Writes stopped on this rev1 freeze pending primary diagnostics, within the bounded packet. Primary must freeze/copy this artifact and preserve all printed theorem types, full axiom reports, build/version exits, stdout/stderr and resource evidence for 56 inherited roots plus all public R17 roots below. At most one bounded repair from actual Audit 1 diagnostics is available within the two-audit limit; no third audit/probe.

## Frozen hashes

- `notes/theory/lean/YulangClosure/FormalPermissionEventBuffer.lean`: SHA-256 `1886b763ebd493721cd6cb7d03f32ff3c43555587a53ccf4e0ee3c351c450b57`; 11038 bytes.
- `notes/theory/lean/YulangClosure/FormalPermissionArenaEvents.lean`: SHA-256 `02ef97716d882073ccb2e53c53bbf8046c80e82a517253898db5d1c02cd1b8b3`; 10043 bytes.
- `tasks/agent-loop/sprints/effect-permission-event-buffer-20261029-r17-inputs.json`: SHA-256 `53052f07b01674a05ad9c2511dbe3fb9319ee6922183baf0dd2c27bf520b40ae`; 52980 bytes.
- `tasks/agent-loop/inbox/effect-permission-event-buffer-r17-source.md`: SHA-256 `0324a286e294ce711c6f09fba0371a041032c4d25c7d66f3319d66a89a40ae08`; 5628 bytes.

## Public theorem inventory and source types

17 public theorem roots; fully qualified prefix `YulangClosure.FormalPermissionEventBuffer.`. These are source types pending the primary’s printed-type and axiom audit. Two private helper theorems set_padding and flatten_occupied are dependencies, not omitted public roots.

```lean
theorem YulangClosure.FormalPermissionEventBuffer.empty_layout (α : Type) : Layout (empty : Buffer α) []
```

```lean
theorem YulangClosure.FormalPermissionEventBuffer.push_layout {α : Type} (b : Buffer α) (xs : List α) (x : α)
    (layout : Layout b xs) (free : b.len < 6) :
    Layout (push b x free) (xs ++ [x])
```

```lean
theorem YulangClosure.FormalPermissionEventBuffer.push_writes_next {α : Type} (b : Buffer α) (x : α) (free : b.len < 6) :
    (push b x free).snapshots[b.len]? = some (some x)
```

```lean
theorem YulangClosure.FormalPermissionEventBuffer.flatten_exact {α : Type} (b : Buffer α) (xs : List α)
    (layout : Layout b xs) : flatten b = xs
```

```lean
theorem YulangClosure.FormalPermissionEventBuffer.take_exact_reset {α : Type} (b : Buffer α) :
    (take b).1 = b ∧ (take b).2 = empty ∧
    (take b).2.len = 0 ∧
    (take b).2.snapshots.toList = List.replicate 6 none
```

```lean
theorem YulangClosure.FormalPermissionEventBuffer.take_events_exact {α : Type} (b : Buffer α) (xs : List α)
    (layout : Layout b xs) : takeEvents b = (xs, empty)
```

```lean
theorem YulangClosure.FormalPermissionEventBuffer.appends_layout {α : Type} (b last : Buffer α) (xs : List α)
    (execution : Appends b xs last) (old : List α) (layout : Layout b old) :
    Layout last (old ++ xs)
```

```lean
theorem YulangClosure.FormalPermissionEventBuffer.appends_exists {α : Type} (b : Buffer α) (old xs : List α)
    (layout : Layout b old) (fits : old.length + xs.length ≤ 6) :
    ∃ last, Appends b xs last
```

```lean
theorem YulangClosure.FormalPermissionEventBuffer.appended_empty_fits (i : Input) : Fits [] i
```

```lean
theorem YulangClosure.FormalPermissionEventBuffer.selected_empty_execution (i : Input) :
    ∃ last : Buffer EventOutcome,
      Appends empty ((appended i).map Event.observation) last ∧
      Layout last ((appended i).map Event.observation)
```

```lean
theorem YulangClosure.FormalPermissionEventBuffer.finish_exact (b : Buffer EventOutcome) (xs : List EventOutcome)
    (layout : Layout b xs) (constructor : ConstructorOutcome)
    (accounting : Bool) (errorMap : Nat → Nat) (s : HelperState) :
    finish b constructor accounting errorMap s =
      ((controlResult errorMap constructor xs accounting,
        controlState constructor xs accounting s), empty)
```

```lean
theorem YulangClosure.FormalPermissionEventBuffer.finish_empty (b : Buffer EventOutcome) (constructor : ConstructorOutcome)
    (accounting : Bool) (errorMap : Nat → Nat) (s : HelperState) :
    (finish b constructor accounting errorMap s).2 = empty := rfl

theorem finish_constructor_error (b : Buffer EventOutcome) (xs : List EventOutcome)
    (layout : Layout b xs) (constructor : ConstructorOutcome)
    (accounting : Bool) (errorMap : Nat → Nat) (s : HelperState) (error : Nat)
    (failed : constructor.result = .error error) (samplesOk : AllSamplesOk xs) :
    (finish b constructor accounting errorMap s).1.1 = .error (errorMap error) ∧
    (finish b constructor accounting errorMap s).2 = empty
```

```lean
theorem YulangClosure.FormalPermissionEventBuffer.finish_sampler_error (b : Buffer EventOutcome) (before after : List EventOutcome)
    (event : EventOutcome) (layout : Layout b (before ++ event :: after))
    (constructor : ConstructorOutcome) (errorMap : Nat → Nat) (s : HelperState)
    (error : Nat) (samplesOk : AllSamplesOk before) (failed : event.result = .error error) :
    (finish b constructor true errorMap s).1.1 = .error error ∧
    (finish b constructor true errorMap s).2 = empty
```

```lean
theorem YulangClosure.FormalPermissionEventBuffer.selected_prefix_finish (b last : Buffer EventOutcome) (old : List EventOutcome)
    (i : Input) (layout : Layout b old)
    (execution : Appends b ((appended i).map Event.observation) last)
    (constructor : ConstructorOutcome) (accounting : Bool)
    (errorMap : Nat → Nat) (s : HelperState) :
    finish last constructor accounting errorMap s =
      ((controlResult errorMap constructor (events old i) accounting,
        controlState constructor (events old i) accounting s), empty)
```

```lean
theorem YulangClosure.FormalPermissionEventBuffer.consecutive_selected_entry (b : Buffer EventOutcome)
    (constructor : ConstructorOutcome) (accounting : Bool) (errorMap : Nat → Nat)
    (s : HelperState) (next : Buffer EventOutcome)
    (noInterleavedMutation : next = (finish b constructor accounting errorMap s).2)
    (i : Input) :
    Layout next [] ∧ Fits [] i ∧
    ∃ last, Appends next ((appended i).map Event.observation) last ∧
      Layout last ((appended i).map Event.observation)
```

```lean
theorem YulangClosure.FormalPermissionEventBuffer.selected_control_refines (b last : Buffer EventOutcome) (old : List EventOutcome)
    (i : Input) (layout : Layout b old)
    (execution : Appends b ((appended i).map Event.observation) last)
    (constructor : ConstructorOutcome) (accounting : Bool) (s : HelperState) :
    runOps (controlOps constructor (takeEvents last).1 accounting s) s =
      controlState constructor (events old i) accounting s
```

