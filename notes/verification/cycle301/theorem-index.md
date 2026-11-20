# Cycle 301: exact theorem signatures

## lean/Yulang/GeneralObservedLadderAdvance301.lean

```lean
theorem Yulang.GeneralObservedLadderAdvance301.reserved_exact (p : Phase n k) (hi : k ≤ n) :
    reserved (stagePlan p hi).packet =
      (allocated (stagePlan p hi).packet).map (source (n+1))
```

```lean
theorem Yulang.GeneralObservedLadderAdvance301.env_exact (p : Phase n k) (hi : k ≤ n) :
    (advanced p hi).core.erased.current.context =
      GeneralDictionaryOrdinaryTransport.extend (context n)
      ((p.keys ++ allocated (stagePlan p hi).packet).map (source (n+1)))
      (p.extraAtoms ++ atoms (stagePlan p hi).packet) (p.keys ++ allocated (stagePlan p hi).packet)
```

```lean
theorem Yulang.GeneralObservedLadderAdvance301.edge_single (p : Phase n k) (hi : k ≤ n) :
    GeneralNominalVersionedChildren232.edges (stagePlan p hi) =
      [(focus n k,focus n (k+1))]
```

```lean
theorem Yulang.GeneralObservedLadderAdvance301.new_models (p : Phase n k) (hi : k ≤ n) (m : Assignment) :
    Models (advanced p hi) m ↔ Models p.state m
```

```lean
theorem Yulang.GeneralObservedLadderAdvance301.phase_step (n k : Nat) (hi : k ≤ n) :
    (boundary roles).Step registry displayRoot (run n k (by omega)).state (run n (k+1) (by omega)).state
```

```lean
theorem Yulang.GeneralObservedLadderAdvance301.path (n k : Nat) (bound : k ≤ n+1) :
    B4Target.Steps ((boundary roles).Step registry displayRoot) (initial n) (run n k bound).state
```

```lean
theorem Yulang.GeneralObservedLadderAdvance301.terminal_reached (n : Nat) : ∃ s,
    B4Target.Steps ((boundary roles).Step registry displayRoot) (initial n) s ∧
    B4TargetV8.Reachable (boundary roles) registry displayRoot s ∧
    GeneralNominalSaturationState.Generated s.core.erased.current displayRoot (focus n (n+1)) ∧
    (∀ m, Models s m ↔ Models (initial n) m) ∧
    s.core.erased.current.edges = edges n (n+1)
```


## lean/Yulang/GeneralObservedLadderAvailability301.lean

```lean
theorem Yulang.GeneralObservedLadderAvailability301.not_recorded (p : Phase n k) (i : Nat) (future : k < i) (m : Assignment) (d : Payload) :
    ¬ (boundary roles).Evidence registry p.state m (focus n i) d
```

```lean
theorem Yulang.GeneralObservedLadderAvailability301.nonterminal_empty (n k : Nat) (below : k ≤ n) (m : Assignment)
    (i : Nat) (atPhase : i ≤ k) (d : Payload) :
    ¬ (boundary roles).Evidence registry (run n k (by omega)).state m (focus n i) d
```

```lean
theorem Yulang.GeneralObservedLadderAvailability301.exact_root_availability (n k : Nat) (hk : k ≤ n+1) (m : Assignment)
    (valid : Models (run n k hk).state m) :
    (∃ d, (boundary roles).Evidence registry (run n k hk).state m displayRoot d) ↔ k = n+1
```


## lean/Yulang/GeneralObservedLadderBudget301.lean

```lean
theorem Yulang.GeneralObservedLadderBudget301.erase {l : Nat} {before after : State roles} (path : Counted l before after) :
    B4Target.Steps RawStep before after
```

```lean
theorem Yulang.GeneralObservedLadderBudget301.count_path (n start : Nat) (startBound : start ≤ n+1) {count : Nat} {s : State roles}
    (path : Counted count (run n start startBound).state s) :
    ∃ fit : start+count ≤ n+1, s = (run n (start+count) fit).state
```

```lean
theorem Yulang.GeneralObservedLadderBudget301.path_exists (n start len : Nat) (fit : start+len ≤ n+1) :
    Counted len (run n start (by omega)).state (run n (start+len) fit).state
```

```lean
theorem Yulang.GeneralObservedLadderBudget301.exact_count (n start stop len : Nat) (left : start ≤ n+1) (right : stop ≤ n+1) :
    Counted len (run n start left).state (run n stop right).state ↔ stop = start+len
```

```lean
theorem Yulang.GeneralObservedLadderBudget301.completion (n k : Nat) (cap : k ≤ n+1) :
    Counted (n+1-k) (run n k cap).state (final n).state ∧
    (∀ last, ¬ RawStep (final n).state last) ∧
    GeneralGeneratedDictionaryRun299.run
      (GeneralObservedLadderJournalCompiler301.table (final n).state) (n+2) 0 =
      some (dictionary (n+1))
```

```lean
theorem Yulang.GeneralObservedLadderBudget301.remaining_exact (n start count : Nat) (cap : start ≤ n+1) (s : State roles)
    (path : Counted count (run n start cap).state s)
    (noMore : ∀ next, ¬ RawStep s next) : count = n+1-start
```

```lean
theorem Yulang.GeneralObservedLadderBudget301.exact_initial_budget (n count : Nat) (s : State roles)
    (path : Counted count (initial n) s)
    (noMore : ∀ next, ¬ RawStep s next) :
    count = n+1 ∧ s = (final n).state
```


## lean/Yulang/GeneralObservedLadderCompilerLaws301.lean

```lean
theorem Yulang.GeneralObservedLadderCompilerLaws301.probe_unary (c : Context) (bs : List (GeneralNominalInspection.Bounds c.state))
    (e : Entry) (found : probe c bs = some e) :
    e.children = [] ∨ ∃ child, e.children = [child]
```

```lean
theorem Yulang.GeneralObservedLadderCompilerLaws301.attached_sound (s : State roles) (i : Nat) (e : Entry) (found : table s i = some e) :
    ∃ row, rawRow s i = some row ∧
      (arguments s.core.erased.current.context row.occurrence).bind (probe s.core.erased.current.context) = some e ∧
      ∀ child ∈ e.children, attached s i child = true
```

```lean
theorem Yulang.GeneralObservedLadderCompilerLaws301.supports_actual_edge (p : Phase n k) (i : Nat) (e : Entry)
    (found : table p.state i = some e) (j : Nat) (member : j ∈ e.children) :
    i < k ∧ j = i+1
```


## lean/Yulang/GeneralObservedLadderEnabled301.lean

```lean
theorem Yulang.GeneralObservedLadderEnabled301.separates (p : Phase n k) {i j : Nat} (left : i ≤ n+1) (right : j ≤ n+1)
    (same : SameInputs (Models p.state) (site n i) (site n j)) : i = j
```

```lean
theorem Yulang.GeneralObservedLadderEnabled301.administrative (p : Phase n k) (bound : k ≤ n+1) :
    GeneralNominalVersionedDiagnostic232.AdministrativeReady p.state (focus n k)
```

```lean
theorem Yulang.GeneralObservedLadderEnabled301.safe (p : Phase n k) (hi : k ≤ n) :
    B4TargetV8.SafeKnown (GeneralNominalVersionedDiagnostic232.boundary roles) compiled p.state (focus n k)
```

```lean
theorem Yulang.GeneralObservedLadderEnabled301.positions (p : Phase n k) (hi : k ≤ n) :
    GeneralNominalVersionedCycles232.Safe p.state (stagePlan p hi)
```

```lean
theorem Yulang.GeneralObservedLadderEnabled301.alternatives (p : Phase n k) (hi : k ≤ n) : AlternativesSafe compiled p.state (stagePlan p hi).input
```

```lean
theorem Yulang.GeneralObservedLadderEnabled301.future_requests (p : Phase n k) (hi : k ≤ n) (o : Occurrence roles) :
    GeneralNominalCenteredHeadOutputs.requests
      (GeneralNominalVersionedInstall232.installCore p.state.core (stagePlan p hi)) o = []
```

```lean
theorem Yulang.GeneralObservedLadderEnabled301.ready (p : Phase n k) (hi : k ≤ n) :
    GeneralNominalCenteredHeadMatEffects.Ready p.state.core (focus n k) (stagePlan p hi)
```

```lean
theorem Yulang.GeneralObservedLadderEnabled301.installation (p : Phase n k) (hi : k ≤ n) (m : Assignment) (valid : Models p.state m) :
    InstallationModels p.state (effect p hi) m
```

```lean
theorem Yulang.GeneralObservedLadderEnabled301.enabled (p : Phase n k) (hi : k ≤ n) : Installable compiled p.state (effect p hi)
```

```lean
theorem Yulang.GeneralObservedLadderEnabled301.not_committed (p : Phase n k) (hi : k ≤ n) : ¬ Committed p.state (stagePlan p hi)
```

```lean
theorem Yulang.GeneralObservedLadderEnabled301.actual (p : Phase n k) (hi : k ≤ n) :
    (boundary roles).Step registry displayRoot p.state (install p.state (effect p hi))
```


## lean/Yulang/GeneralObservedLadderEvidence301.lean

```lean
theorem Yulang.GeneralObservedLadderEvidence301.keys_installed (n k : Nat) (cap : k ≤ n+1) (i : Nat) (past : i < k) :
    GeneralNominalVersionedAllocation231.keys compiled (invocation n i) [(0,(i+1,i+1))] ⊆ (run n k cap).keys
```

```lean
theorem Yulang.GeneralObservedLadderEvidence301.replay_held (p : Phase n k) (i : Nat) (hi : i ≤ n) (m : Assignment) (valid : Models p.state m) :
    Holds (replay p i hi) m
```

```lean
theorem Yulang.GeneralObservedLadderEvidence301.replay_children (p : Phase n k) (i : Nat) (hi : i ≤ n) :
    children (replay p i hi).packet = [focus n (i+1)]
```

```lean
theorem Yulang.GeneralObservedLadderEvidence301.replay_prepared (p : Phase n k) (i : Nat) (hi : i ≤ n)
    (owned : GeneralNominalVersionedAllocation231.keys compiled (invocation n i) [(0,(i+1,i+1))] ⊆ p.keys) :
    Prepared compiled (env p) (focus n i) display
```

```lean
theorem Yulang.GeneralObservedLadderEvidence301.replay_frame (n k : Nat) (cap : k ≤ n+1) (i : Nat) (past : i < k) :
    Frame compiled (run n k cap).state.core (focus n i) 1
      (replay (run n k cap) i (by omega))
```

```lean
theorem Yulang.GeneralObservedLadderEvidence301.list_instance (n k : Nat) (cap : k ≤ n+1) (i : Nat) (past : i < k)
    (m : Assignment) (valid : Models (run n k cap).state m) :
    Instance compiled (run n k cap).state.core m (focus n i) 1 [focus n (i+1)]
```

```lean
theorem Yulang.GeneralObservedLadderEvidence301.node (n depth : Nat) (cap : depth ≤ n+1) (m : Assignment) (valid : Models (final n).state m) :
    (boundary roles).Evidence registry (final n).state m (focus n (n+1-depth)) (dictionary depth)
```

```lean
theorem Yulang.GeneralObservedLadderEvidence301.root (n : Nat) (m : Assignment) (valid : Models (final n).state m) :
    (boundary roles).Evidence registry (final n).state m displayRoot (dictionary (n+1))
```

```lean
theorem Yulang.GeneralObservedLadderEvidence301.actual_with_dictionary (n : Nat) :
    B4Target.Steps ((boundary roles).Step registry displayRoot) (initial n) (final n).state ∧
      B4TargetV8.Reachable (boundary roles) registry displayRoot (final n).state ∧
      (∃ m, Models (final n).state m) ∧
      (∀ m, Models (final n).state m ↔ Models (initial n) m) ∧
      ∀ m, Models (final n).state m →
        (boundary roles).Evidence registry (final n).state m displayRoot (dictionary (n+1))
```


## lean/Yulang/GeneralObservedLadderExact301.lean

```lean
theorem Yulang.GeneralObservedLadderExact301.only_step (n k : Nat) (cap : k ≤ n+1) (s : State roles)
    (raw : (boundary roles).Step registry displayRoot (run n k cap).state s) :
    ∃ hi : k ≤ n, s = (run n (k+1) (by omega)).state
```

```lean
theorem Yulang.GeneralObservedLadderExact301.exact_step (n k : Nat) (cap : k ≤ n+1) (s : State roles) :
    (boundary roles).Step registry displayRoot (run n k cap).state s ↔
      ∃ hi : k ≤ n, s = (run n (k+1) (by omega)).state
```

```lean
theorem Yulang.GeneralObservedLadderExact301.halted (n : Nat) (s : State roles) :
    ¬ (boundary roles).Step registry displayRoot (run n (n+1) (Nat.le_refl _)).state s
```

```lean
theorem Yulang.GeneralObservedLadderExact301.reachable_phases (n : Nat) (s : State roles)
    (path : Steps ((boundary roles).Step registry displayRoot) (initial n) s) :
    ∃ k, ∃ cap : k ≤ n+1, s = (run n k cap).state
```

```lean
theorem Yulang.GeneralObservedLadderExact301.phases_distinct (n a b : Nat) (ha : a ≤ n+1) (hb : b ≤ n+1)
    (same : (run n a ha).state = (run n b hb).state) : a = b
```

```lean
theorem Yulang.GeneralObservedLadderExact301.rank_decreases (n a b : Nat) (ha : a ≤ n+1) (hb : b ≤ n+1)
    (step : (boundary roles).Step registry displayRoot (run n a ha).state (run n b hb).state) :
    n+1-b < n+1-a
```

```lean
theorem Yulang.GeneralObservedLadderExact301.accessible_phase (n k : Nat) (cap : k ≤ n+1) :
    Acc (fun last first => (boundary roles).Step registry displayRoot first last) (run n k cap).state
```

```lean
theorem Yulang.GeneralObservedLadderExact301.accessible_initial (n : Nat) :
    Acc (fun last first => (boundary roles).Step registry displayRoot first last) (initial n)
```


## lean/Yulang/GeneralObservedLadderInitial301.lean

```lean
theorem Yulang.GeneralObservedLadderInitial301.translated (k : Nat) :
    GeneralNominalInspection.translate constructors interpretation (normalize (pattern k)) = quote (term k)
```

```lean
theorem Yulang.GeneralObservedLadderInitial301.leafless (k : Nat) : (term k).leaves = []
```

```lean
theorem Yulang.GeneralObservedLadderInitial301.canonical (k : Nat) : GeneralNominalReadbackFunctionality.Canonical (term k)
```

```lean
theorem Yulang.GeneralObservedLadderInitial301.denotes (k : Nat) : denote (fun _ => .bottom) (term k) = tower k
```

```lean
theorem Yulang.GeneralObservedLadderInitial301.support (n i : Nat) (member : i ∈ GeneralNominalState.sources (snapshot n)) :
    i ≤ n+1
```

```lean
theorem Yulang.GeneralObservedLadderInitial301.formed (n : Nat) : GeneralNominalSourceFormation.InitialSource registry (context n) displayRoot
```

```lean
theorem Yulang.GeneralObservedLadderInitial301.ground (n : Nat) : GroundRoots (context n) displayRoot (labels n)
```

```lean
theorem Yulang.GeneralObservedLadderInitial301.actual_initial (n : Nat) : (boundary roles).Initial registry displayRoot (initial n)
```

```lean
theorem Yulang.GeneralObservedLadderInitial301.models (n : Nat) : Models (initial n) (finiteModel n)
```

```lean
theorem Yulang.GeneralObservedLadderInitial301.reached (n : Nat) :
    B4TargetV8.Reachable (boundary roles) registry displayRoot (initial n) ∧ Models (initial n) (finiteModel n)
```


## lean/Yulang/GeneralObservedLadderJournalCompiler301.lean

```lean
theorem Yulang.GeneralObservedLadderJournalCompiler301.probe_list (p : Phase n k) (i : Nat) (hi : i ≤ n) :
    probe (env p) [point n i (by omega)] = some ⟨1,[i+1]⟩
```

```lean
theorem Yulang.GeneralObservedLadderJournalCompiler301.probe_leaf (p : Phase n k) :
    probe (env p) [point n (n+1) (Nat.le_refl _)] = some ⟨3,[]⟩
```

```lean
theorem Yulang.GeneralObservedLadderJournalCompiler301.checked_list (p : Phase n k) (i : Nat) (recorded : i ≤ k) (inner : i ≤ n) :
    receipt p.state i = if i < k then .attached ⟨1,[i+1]⟩ else .awaitingChild (i+1)
```

```lean
theorem Yulang.GeneralObservedLadderJournalCompiler301.checked_leaf (p : Phase n (n+1)) : receipt p.state (n+1) = .attached ⟨3,[]⟩
```

```lean
theorem Yulang.GeneralObservedLadderJournalCompiler301.unrecorded (p : Phase n k) (i : Nat) (missing : k < i) : receipt p.state i = .absent
```

```lean
theorem Yulang.GeneralObservedLadderJournalCompiler301.exact_final (n : Nat) : table (final n).state = GeneralObservedLadderObserver301.table n
```

```lean
theorem Yulang.GeneralObservedLadderJournalCompiler301.before_no_dictionary (p : Phase n k) (before : k ≤ n) (gas i : Nat) :
    run (table p.state) gas i = none
```

```lean
theorem Yulang.GeneralObservedLadderJournalCompiler301.root_available_exact (n k : Nat) (cap : k ≤ n+1) (gas : Nat) :
    run (table (GeneralObservedLadderAdvance301.run n k cap).state) gas 0 =
      if k = n+1 ∧ n+1 < gas then some (dictionary (n+1)) else none
```

```lean
theorem Yulang.GeneralObservedLadderJournalCompiler301.semantic_at_final (n i gas : Nat) (d : Dictionary)
    (pass : run (table (final n).state) gas i = some d) (m : GeneralNominalCommonBridge.Assignment)
    (valid : Models (final n).state m) :
    (boundary roles).Evidence registry (final n).state m (focus n i) d
```


## lean/Yulang/GeneralObservedLadderJournalRows301.lean

```lean
theorem Yulang.GeneralObservedLadderJournalRows301.site_count (n k : Nat) : (sites n k).length = k+1
```

```lean
theorem Yulang.GeneralObservedLadderJournalRows301.indexed_site (n i k : Nat) : (sites n k)[i]? = if i ≤ k then some (site n i) else none
```

```lean
theorem Yulang.GeneralObservedLadderJournalRows301.raw_hit (p : Phase n k) (i : Nat) :
    rawRow p.state i = if i ≤ k then some (site n i).observed else none
```

```lean
theorem Yulang.GeneralObservedLadderJournalRows301.attached_exact (p : Phase n k) (i j : Nat) :
    attached p.state i j = true ↔ i < k ∧ j = i+1
```

```lean
theorem Yulang.GeneralObservedLadderJournalRows301.all_generated (p : Phase n k) (i : Nat) (bound : i ≤ k) :
    GeneralNominalSaturationState.Generated p.state.core.erased.current GeneralNominalExamples.displayRoot (focus n i)
```


## lean/Yulang/GeneralObservedLadderLeaf301.lean

```lean
theorem Yulang.GeneralObservedLadderLeaf301.blank_report (p : Phase n (n+1)) :
    GeneralNominalPacketSupport.report (terminalPacket p) =
      { inspected := [point n (n+1) (Nat.le_refl _)],
        checked := [point n (n+1) (Nat.le_refl _),point n (n+1) (Nat.le_refl _)] }
```

```lean
theorem Yulang.GeneralObservedLadderLeaf301.blank_bindings (p : Phase n (n+1)) : (terminalPacket p).bindings = []
```

```lean
theorem Yulang.GeneralObservedLadderLeaf301.children_empty (p : Phase n (n+1)) : children (terminalPacket p) = []
```

```lean
theorem Yulang.GeneralObservedLadderLeaf301.schema_empty (p : Phase n (n+1)) : emittedSchema (terminalPlan p) = ⟨[],false⟩
```

```lean
theorem Yulang.GeneralObservedLadderLeaf301.ordinary (p : Phase n (n+1)) (m : Assignment) : Ordinary (terminalPacket p) m
```

```lean
theorem Yulang.GeneralObservedLadderLeaf301.head_schema (p : Phase n (n+1)) :
    (terminalPlan p).headSchema = ⟨[],[(.source (n+1),.scalar .int)],false⟩
```

```lean
theorem Yulang.GeneralObservedLadderLeaf301.holds (p : Phase n (n+1)) (m : Assignment) (valid : Models p.state m) : Holds (terminalPlan p) m
```

```lean
theorem Yulang.GeneralObservedLadderLeaf301.prepared (p : Phase n (n+1)) : Prepared compiled (env p) (focus n (n+1)) intDisplay
```

```lean
theorem Yulang.GeneralObservedLadderLeaf301.frame (p : Phase n (n+1)) : Frame compiled p.state.core (focus n (n+1)) 3 (terminalPlan p)
```

```lean
theorem Yulang.GeneralObservedLadderLeaf301.terminal_instance (p : Phase n (n+1)) (m : Assignment) (valid : Models p.state m) :
    Instance compiled p.state.core m (focus n (n+1)) 3 []
```

```lean
theorem Yulang.GeneralObservedLadderLeaf301.unique (p : Phase n (n+1)) : Unique compiled (env p) (focus n (n+1)) 3 []
```


## lean/Yulang/GeneralObservedLadderLedger301.lean

```lean
theorem Yulang.GeneralObservedLadderLedger301.stage_held (p : Phase n k) (hi : k ≤ n) (m : Assignment) (held : Models p.state m) :
    Holds (stagePlan p hi) m
```

```lean
theorem Yulang.GeneralObservedLadderLedger301.stage_bindings (p : Phase n k) (hi : k ≤ n) :
    (stagePlan p hi).packet.bindings = [(0,(k+1,k+1))]
```

```lean
theorem Yulang.GeneralObservedLadderLedger301.stage_atoms (p : Phase n k) (hi : k ≤ n) :
    atoms (stagePlan p hi).packet =
      [.tyLe (.var (k+1)) (.var (k+1)),.tyLe (.var k) (.var k),
       .tyLe (.var k) (.var k),.tyLe (.var (k+1)) (.var (k+1))]
```

```lean
theorem Yulang.GeneralObservedLadderLedger301.stage_supported (p : Phase n k) (hi : k ≤ n) (a : Nat)
    (hit : a ∈ (atoms (stagePlan p hi).packet).flatMap GeneralNominalState.atomSources) :
    a ≤ n+1
```

```lean
theorem Yulang.GeneralObservedLadderLedger301.support (p : Phase n k) (a : Nat) (hit : a ∈ GeneralNominalState.sources (env p).state) :
    a ≤ n+1 ∨ a ∈ p.keys.map (source (n+1))
```

```lean
theorem Yulang.GeneralObservedLadderLedger301.fresh (p : Phase n k) (bs) :
    GeneralNominalVersionedAllocation231.Fresh (env p).state compiled (invocation n k) bs
```


## lean/Yulang/GeneralObservedLadderLocal301.lean

```lean
theorem Yulang.GeneralObservedLadderLocal301.arbitrary_fresh (p : Phase n k) (id : Nat) (bs) :
    GeneralNominalVersionedAllocation231.Fresh (env p).state compiled id bs
```

```lean
theorem Yulang.GeneralObservedLadderLocal301.administrative (n i : Nat) (bound : i ≤ n+1) :
    GeneralNominalVersionedDiagnostic232.AdministrativeReady (final n).state (focus n i)
```

```lean
theorem Yulang.GeneralObservedLadderLocal301.failed_int (n i : Nat) (hi : i ≤ n) :
    Failed compiled (final n).state.core.erased.current.context (focus n i) intDisplay
```

```lean
theorem Yulang.GeneralObservedLadderLocal301.safe (n i : Nat) (bound : i ≤ n+1) (d : Declaration)
    (right : Prepared compiled (final n).state.core.erased.current.context (focus n i) d)
    (checked : ∀ e ∈ compiled.declarations, e.role = (focus n i).demand.role →
      e = d ∨ Failed compiled (final n).state.core.erased.current.context (focus n i) e) :
    B4TargetV8.SafeKnown (GeneralNominalVersionedDiagnostic232.boundary roles) compiled (final n).state (focus n i)
```

```lean
theorem Yulang.GeneralObservedLadderLocal301.unique_list (n i : Nat) (hi : i ≤ n) :
    Unique compiled (final n).state.core.erased.current.context (focus n i) 1 [focus n (i+1)]
```

```lean
theorem Yulang.GeneralObservedLadderLocal301.not_merged (n i : Nat) :
    ¬ GeneralNominalVersionedMergedConflict232.MergedOutputConflict (final n).state (focus n i)
```

```lean
theorem Yulang.GeneralObservedLadderLocal301.local_of (n i : Nat) {key kids} (q : Plan roles)
    (frame : Frame compiled (final n).state.core (focus n i) key q)
    (holds : Holds q (finiteModel n))
    (safeHere : B4TargetV8.SafeKnown (GeneralNominalVersionedDiagnostic232.boundary roles) compiled
      (final n).state (focus n i))
    (only : Unique compiled (final n).state.core.erased.current.context (focus n i) key kids) :
    B4TargetV8.Local (boundary roles) registry (final n).state (focus n i) (.selected key kids)
```

```lean
theorem Yulang.GeneralObservedLadderLocal301.list_local (n i : Nat) (hi : i ≤ n) :
    B4TargetV8.Local (boundary roles) registry (final n).state (focus n i) (.selected 1 [focus n (i+1)])
```

```lean
theorem Yulang.GeneralObservedLadderLocal301.leaf_local (n : Nat) :
    B4TargetV8.Local (boundary roles) registry (final n).state (focus n (n+1)) (.selected 3 [])
```


## lean/Yulang/GeneralObservedLadderNoAdmin301.lean

```lean
theorem Yulang.GeneralObservedLadderNoAdmin301.fixed (n : Nat) (alter : Nat → Ty) (i : Nat) (low : i ≤ n+1) :
    padding n alter i = finiteModel n i
```

```lean
theorem Yulang.GeneralObservedLadderNoAdmin301.free (n : Nat) (alter : Nat → Ty) (i : Nat) (high : n+1 < i) :
    (padding n alter i).1 = alter i
```

```lean
theorem Yulang.GeneralObservedLadderNoAdmin301.snapshot_padded (n : Nat) (alter : Nat → Ty) :
    GeneralNominalState.Models (snapshot n) (padding n alter)
```

```lean
theorem Yulang.GeneralObservedLadderNoAdmin301.padded (p : Phase n k) (alter : Nat → Ty) : Models p.state (padding n alter)
```

```lean
theorem Yulang.GeneralObservedLadderNoAdmin301.all_known (p : Phase n k) (i : Nat) (bound : i ≤ n+1) :
    GeneralNominalState.Known p.state.core.erased.current.context.state i
```

```lean
theorem Yulang.GeneralObservedLadderNoAdmin301.headless (p : Phase n k) : HeadlessUnknown p.state
```

```lean
theorem Yulang.GeneralObservedLadderNoAdmin301.tower_not_top (d : Nat) : ¬ Equivalent .top (tower d)
```

```lean
theorem Yulang.GeneralObservedLadderNoAdmin301.isolate (n a b : Nat) (large : n+1 < a) (apart : a ≠ b) :
    ¬ Equivalent (padding n (mark n a) a).1 (padding n (mark n a) b).1
```

```lean
theorem Yulang.GeneralObservedLadderNoAdmin301.only_equal_names (p : Phase n k) (a b : Nat) (same : Equal p.state a b) : a = b
```

```lean
theorem Yulang.GeneralObservedLadderNoAdmin301.equality_closed (p : Phase n k) : EqualityClosed p.state
```

```lean
theorem Yulang.GeneralObservedLadderNoAdmin301.point_closed (p : Phase n k) :
    GeneralNominalReobservationSteps.PointClosed p.state.core.erased.current.context.state
```


## lean/Yulang/GeneralObservedLadderObserver301.lean

```lean
theorem Yulang.GeneralObservedLadderObserver301.exact_list (n i : Nat) (bound : i ≤ n) :
    lookup n i = some (.selected 1 [i+1])
```

```lean
theorem Yulang.GeneralObservedLadderObserver301.exact_scalar (n : Nat) : lookup n (n+1) = some (.selected 3 [])
```

```lean
theorem Yulang.GeneralObservedLadderObserver301.absent (n i : Nat) (outside : n+1 < i) : lookup n i = none
```

```lean
theorem Yulang.GeneralObservedLadderObserver301.observed (n i : Nat) (f : Frontier Nat) (found : lookup n i = some f) :
    Local (boundary roles) registry (final n).state (focus n i) (translate (focus n) f)
```

```lean
theorem Yulang.GeneralObservedLadderObserver301.roundtrip (n j i : Nat) (h : encode n j = some i) : focus n i = focus n j
```

```lean
theorem Yulang.GeneralObservedLadderObserver301.faithful (n : Nat) :
    Faithful (b:=boundary roles) (r:=registry) (s:=(final n).state) (table n) (focus n)
```

```lean
theorem Yulang.GeneralObservedLadderObserver301.branch (n i : Nat) (inner : i ≤ n) : table n i = some ⟨1,[i+1]⟩
```

```lean
theorem Yulang.GeneralObservedLadderObserver301.leaf (n : Nat) : table n (n+1) = some ⟨3,[]⟩
```

```lean
theorem Yulang.GeneralObservedLadderObserver301.out_of_range (n i : Nat) (outside : n+1 < i) : table n i = none
```

```lean
theorem Yulang.GeneralObservedLadderObserver301.entries (n i : Nat) (e : Entry) (hit : table n i = some e) :
    (i ≤ n ∧ e = ⟨1,[i+1]⟩) ∨ (i = n+1 ∧ e = ⟨3,[]⟩)
```

```lean
theorem Yulang.GeneralObservedLadderObserver301.closed (n : Nat) : Closed (table n)
```

```lean
theorem Yulang.GeneralObservedLadderObserver301.rank (n : Nat) : Ranked (table n) (fun i => n+1-i)
```

```lean
theorem Yulang.GeneralObservedLadderObserver301.known (n : Nat) :
    GeneralGeneratedDictionaryRankCheck299.Known (table n) (List.range (n+2))
```

```lean
theorem Yulang.GeneralObservedLadderObserver301.exact_on_present (n i : Nat) {row : Entry} (hit : table n i = some row)
    (d : Dictionary) :
    GeneralGeneratedDictionaryRun299.run (table n) (n+2) i = some d ↔
      Classify (boundary roles) registry (final n).state (focus n i) (.selected d)
```


## lean/Yulang/GeneralObservedLadderOnlyInstall301.lean

```lean
theorem Yulang.GeneralObservedLadderOnlyInstall301.raw_hit (p : Phase n k) (s : GeneralNominalDemandMerging.Site roles)
    (member : s ∈ p.state.core.erased.current.sites) : ∃ i ≤ k, s.occurrence = focus n i
```

```lean
theorem Yulang.GeneralObservedLadderOnlyInstall301.generated (p : Phase n k) {o : Occurrence roles}
    (seen : Generated p.state.core.erased.current displayRoot o) : ∃ i ≤ k, o = focus n i
```

```lean
theorem Yulang.GeneralObservedLadderOnlyInstall301.recorded (p : Phase n k) {o : Occurrence roles}
    (seen : Generated p.state.core.erased.current displayRoot o) :
    ∃ s ∈ p.state.core.erased.current.sites, s.occurrence = o
```

```lean
theorem Yulang.GeneralObservedLadderOnlyInstall301.wrong_int_at (p : Phase n k) (i : Nat) (hi : i ≤ n) :
    ¬ Prepared compiled p.state.core.erased.current.context (focus n i) intDisplay
```

```lean
theorem Yulang.GeneralObservedLadderOnlyInstall301.inner_frame (p : Phase n k) (i : Nat) (hi : i ≤ n) {q exact : Plan roles} {key chosen}
    (candidate : Frame compiled p.state.core (focus n i) key q)
    (certified : Frame compiled p.state.core (focus n i) chosen exact)
    (right : exact.packet.declaration = display)
    (raw_eq : exact.packet.site = GeneralNominalDemandMerging.pointSite (focus n i))
    (center_eq : exact.input = site n i) :
    q = exact
```

```lean
theorem Yulang.GeneralObservedLadderOnlyInstall301.past_committed (n k : Nat) (cap : k ≤ n+1) (i : Nat) (past : i < k) {q : Plan roles} {key}
    (candidate : Frame compiled (run n k cap).state.core (focus n i) key q) :
    Committed (run n k cap).state q
```

```lean
theorem Yulang.GeneralObservedLadderOnlyInstall301.leaf_frame (p : Phase n (n+1)) {q : Plan roles} {key}
    (candidate : Frame compiled p.state.core (focus n (n+1)) key q) : q = terminalPlan p
```

```lean
theorem Yulang.GeneralObservedLadderOnlyInstall301.leaf_committed (p : Phase n (n+1)) {q : Plan roles} {key}
    (candidate : Frame compiled p.state.core (focus n (n+1)) key q) : Committed p.state q
```

```lean
theorem Yulang.GeneralObservedLadderOnlyInstall301.same_effect (a b : Effect roles) (reg : a.registry = b.registry)
    (ctx : a.snapshot = b.snapshot) (plan : a.plan = b.plan) : a = b
```

```lean
theorem Yulang.GeneralObservedLadderOnlyInstall301.candidate_exact (n k : Nat) (cap : k ≤ n+1) (e : Effect roles)
    (enabled : Installable compiled (run n k cap).state e)
    (seen : Generated (run n k cap).state.core.erased.current displayRoot e.plan.packet.site.occurrence)
    (novel : ¬ Committed (run n k cap).state e.plan) :
    ∃ hi : k ≤ n, e = effect (run n k cap) hi
```


## lean/Yulang/GeneralObservedLadderPlan301.lean

```lean
theorem Yulang.GeneralObservedLadderPlan301.bindings : (packet n i id hi).bindings = [(0,(i+1,i+1))]
```

```lean
theorem Yulang.GeneralObservedLadderPlan301.captured : (capture (packet n i id hi)).inputs 0 = (i+1,i+1)
```

```lean
theorem Yulang.GeneralObservedLadderPlan301.center : binder (plan n i id hi) 0 = i+1
```

```lean
theorem Yulang.GeneralObservedLadderPlan301.head_schema : (plan n i id hi).headSchema =
    ⟨[⟨0,origin i,.actual⟩],[(.source i,.nominal 0 1)],false⟩
```

```lean
theorem Yulang.GeneralObservedLadderPlan301.emitted_schema : emittedSchema (plan n i id hi) =
    ⟨[⟨i+1,.lower,.variable 0⟩,⟨i+1,.upper,.variable 0⟩],false⟩
```

```lean
theorem Yulang.GeneralObservedLadderPlan301.emitted_sites : GeneralNominalVersionedChildren232.emitted (plan n i id hi) = [child n i id hi]
```

```lean
theorem Yulang.GeneralObservedLadderPlan301.child_args : ∀ k, (child n i id hi).occurrence.demand.arguments k = (i+1,i+1)
```

```lean
theorem Yulang.GeneralObservedLadderPlan301.child_center : ∀ k, (child n i id hi).center k = i+1
```

```lean
theorem Yulang.GeneralObservedLadderPlan301.child_schema : childSchema (plan n i id hi) displayChild
    (display_checked.signature.2.2.2 _ (by simp)) = ⟨[⟨i+1,.actual,.variable 0⟩],false⟩
```

```lean
theorem Yulang.GeneralObservedLadderPlan301.var_actual (m : Assignment) : variables (plan n i id hi) m .actual 0 = (m (i+1)).1
```

```lean
theorem Yulang.GeneralObservedLadderPlan301.var_bounds (m : Assignment) :
    variables (plan n i id hi) m .lower 0 = (m (i+1)).1 ∧
      variables (plan n i id hi) m .upper 0 = (m (i+1)).1
```


## lean/Yulang/GeneralObservedLadderReadback301.lean

```lean
theorem Yulang.GeneralObservedLadderReadback301.run_branch (n i : Nat) (hi : i ≤ n) (gas : Nat) :
    run (table n) (gas+1) i =
      (run (table n) gas (i+1)).map (fun d => .node 1 [d])
```

```lean
theorem Yulang.GeneralObservedLadderReadback301.fuel_exact (n depth : Nat) (cap : depth ≤ n+1) (gas : Nat) :
    run (table n) gas (n+1-depth) =
      if depth < gas then some (dictionary depth) else none
```

```lean
theorem Yulang.GeneralObservedLadderReadback301.first_success (n i : Nat) (cap : i ≤ n+1) (gas : Nat) :
    (∃ d, run (table n) gas i = some d) ↔ n+1-i < gas
```

```lean
theorem Yulang.GeneralObservedLadderReadback301.computed (n : Nat) : run (table n) (n+2) 0 = some (dictionary (n+1))
```

```lean
theorem Yulang.GeneralObservedLadderReadback301.nodes (n : Nat) :
    Nodes (boundary roles) registry (final n).state (table n) (focus n)
```

```lean
theorem Yulang.GeneralObservedLadderReadback301.exact_compiled_root (n : Nat) (d : Dictionary) :
    Classify (boundary roles) registry (final n).state displayRoot (.selected d) ↔ d = dictionary (n+1)
```

```lean
theorem Yulang.GeneralObservedLadderReadback301.compiler_sound (n i gas : Nat) (d : Dictionary) (pass : run (table n) gas i = some d)
    (m : Assignment) (valid : Models (final n).state m) :
    (boundary roles).Evidence registry (final n).state m (focus n i) d
```

```lean
theorem Yulang.GeneralObservedLadderReadback301.evidence_at (n : Nat) : B4SkeletonV8.EvidenceAt (boundary roles) registry (final n).state displayRoot
```

```lean
theorem Yulang.GeneralObservedLadderReadback301.selection_graph_accessible (n i : Nat) (cap : i ≤ n+1) :
    Acc (CommonRoleOutermostResolver.Child (B4TargetV8.Local (boundary roles) registry (final n).state)) (focus n i)
```


## lean/Yulang/GeneralObservedLadderRefresh301.lean

```lean
theorem Yulang.GeneralObservedLadderRefresh301.initial (n : Nat) : (boundary roles).Initial registry displayRoot (before n)
```

```lean
theorem Yulang.GeneralObservedLadderRefresh301.known_target (n a : Nat) (low : a ≤ n+1) : Known (refined n).state a
```

```lean
theorem Yulang.GeneralObservedLadderRefresh301.target_support (n a : Nat) (hit : a ∈ GeneralNominalState.sources (refined n).state) :
    a ∈ GeneralNominalState.sources (equationOnly n).state
```

```lean
theorem Yulang.GeneralObservedLadderRefresh301.target_models (n : Nat) (m : Assignment) :
    GeneralNominalState.Models (refined n).state m ↔ GeneralNominalState.Models (equationOnly n).state m
```

```lean
theorem Yulang.GeneralObservedLadderRefresh301.cache (n : Nat) : GeneralNominalVersionedMixedObservations233.CacheSound (before n) (refined n).state
```

```lean
theorem Yulang.GeneralObservedLadderRefresh301.endpoint_unknown (n : Nat) : ¬ Known (equationOnly n).state (n+1)
```

```lean
theorem Yulang.GeneralObservedLadderRefresh301.actual (n : Nat) : (boundary roles).Step registry displayRoot (before n) (after n)
```

```lean
theorem Yulang.GeneralObservedLadderRefresh301.refresh_models (n : Nat) (m : Assignment) : Models (after n) m ↔ Models (before n) m
```

```lean
theorem Yulang.GeneralObservedLadderRefresh301.receipt_changes (n : Nat) :
    GeneralObservedLadderJournalCompiler301.probe (equationOnly n) [GeneralObservedLadderSemanticGap301.terminalPoint n] = none ∧
      GeneralObservedLadderJournalCompiler301.probe (refined n)
        [GeneralObservedLadderReport301.point n (n+1) (Nat.le_refl _)] = some ⟨3,[]⟩
```


## lean/Yulang/GeneralObservedLadderRefreshChain301.lean

```lean
theorem Yulang.GeneralObservedLadderRefreshChain301.before_models (n : Nat) (m : Assignment) :
    Models (before n) m ↔ Models (initial n) m
```

```lean
theorem Yulang.GeneralObservedLadderRefreshChain301.outer_atoms (n : Nat) :
    atomTail n = [.tyLe (.var (n+1)) (.base .int),.tyLe (.base .int) (.var (n+1))]
```

```lean
theorem Yulang.GeneralObservedLadderRefreshChain301.step (n k : Nat) (hi : k ≤ n) :
    (boundary roles).Step registry displayRoot (advanceFromRefresh n k (by omega)).state
      (advanceFromRefresh n (k+1) (by omega)).state
```

```lean
theorem Yulang.GeneralObservedLadderRefreshChain301.trace (n k : Nat) (cap : k ≤ n+1) :
    Steps ((boundary roles).Step registry displayRoot) (before n) (advanceFromRefresh n k cap).state
```

```lean
theorem Yulang.GeneralObservedLadderRefreshChain301.keys_installed (n k : Nat) (cap : k ≤ n+1) (i : Nat) (past : i < k) :
    GeneralNominalVersionedAllocation231.keys compiled (invocation n i) [(0,(i+1,i+1))] ⊆
      (advanceFromRefresh n k cap).keys
```

```lean
theorem Yulang.GeneralObservedLadderRefreshChain301.list_frame (n i : Nat) (hi : i ≤ n) :
    Frame compiled (settled n).state.core (focus n i) 1 (replay (settled n) i hi)
```

```lean
theorem Yulang.GeneralObservedLadderRefreshChain301.list_instance (n i : Nat) (hi : i ≤ n) (m : Assignment) (valid : Models (settled n).state m) :
    Instance compiled (settled n).state.core m (focus n i) 1 [focus n (i+1)]
```

```lean
theorem Yulang.GeneralObservedLadderRefreshChain301.evidence (n remaining : Nat) (cap : remaining ≤ n+1) (m : Assignment)
    (valid : Models (settled n).state m) :
    (boundary roles).Evidence registry (settled n).state m (focus n (n+1-remaining)) (dictionary remaining)
```

```lean
theorem Yulang.GeneralObservedLadderRefreshChain301.completed_trace (n : Nat) :
    (boundary roles).Step registry displayRoot (before n) (after n) ∧
      Steps ((boundary roles).Step registry displayRoot) (before n) (settled n).state ∧
      GeneralNominalSaturationState.Generated (settled n).state.core.erased.current displayRoot (focus n (n+1)) ∧
      (∀ m, Models (settled n).state m ↔ Models (before n) m) ∧
      ∀ m, Models (settled n).state m →
        (boundary roles).Evidence registry (settled n).state m displayRoot (dictionary (n+1))
```


## lean/Yulang/GeneralObservedLadderRefreshProgram301.lean

```lean
theorem Yulang.GeneralObservedLadderRefreshProgram301.old_source_support (n a : Nat) (seen : a ∈ GeneralNominalState.sources (equationOnly n).state) : a ≤ n+1
```

```lean
theorem Yulang.GeneralObservedLadderRefreshProgram301.earlier_known (n a : Nat) (low : a ≤ n) : GeneralNominalState.Known (equationOnly n).state a
```

```lean
theorem Yulang.GeneralObservedLadderRefreshProgram301.strict_focus (n a : Nat) (seen : a ∈ GeneralNominalState.sources (equationOnly n).state)
    (unknown : ¬ GeneralNominalState.Known (equationOnly n).state a) : a = n+1
```

```lean
theorem Yulang.GeneralObservedLadderRefreshProgram301.not_headless (n : Nat) : ¬ HeadlessUnknown (before n)
```

```lean
theorem Yulang.GeneralObservedLadderRefreshProgram301.counted (n k : Nat) (cap : k ≤ n+1) :
    Counted (k+1) (before n) (advanceFromRefresh n k cap).state
```

```lean
theorem Yulang.GeneralObservedLadderRefreshProgram301.no_edges_at_actual_refresh (n : Nat) :
    (after n).core.erased.current.edges = (before n).core.erased.current.edges
```

```lean
theorem Yulang.GeneralObservedLadderRefreshProgram301.terminal_table (p : Phase n (n+1)) :
    table p.state = GeneralObservedLadderObserver301.table n
```

```lean
theorem Yulang.GeneralObservedLadderRefreshProgram301.computes (n : Nat) :
    run (table (settled n).state) (n+2) 0 = some (dictionary (n+1))
```

```lean
theorem Yulang.GeneralObservedLadderRefreshProgram301.nodes (n : Nat) : Nodes (boundary roles) registry (settled n).state
    (GeneralObservedLadderObserver301.table n) (focus n)
```

```lean
theorem Yulang.GeneralObservedLadderRefreshProgram301.compiler_sound (n i fuel : Nat) (d : Dictionary)
    (read : run (table (settled n).state) fuel i = some d)
    (m : Assignment) (valid : Models (settled n).state m) :
    (boundary roles).Evidence registry (settled n).state m (focus n i) d
```

```lean
theorem Yulang.GeneralObservedLadderRefreshProgram301.actual_refresh_then_compile (n : Nat) :
    Counted (n+2) (before n) (settled n).state ∧
    run (table (settled n).state) (n+2) 0 = some (dictionary (n+1)) ∧
    ∀ m, Models (settled n).state m →
      (boundary roles).Evidence registry (settled n).state m displayRoot (dictionary (n+1))
```


## lean/Yulang/GeneralObservedLadderReport301.lean

```lean
theorem Yulang.GeneralObservedLadderReport301.no_nominal (n : Nat) : (snapshot n).nominals (endpoint n) = none
```

```lean
theorem Yulang.GeneralObservedLadderReport301.display_query (n : Nat) : queries (snapshot n) interpretation display =
    [.nominal 0 [.variables [0]]]
```

```lean
theorem Yulang.GeneralObservedLadderReport301.int_query (n : Nat) : queries (snapshot n) interpretation intDisplay = [.scalar .int]
```

```lean
theorem Yulang.GeneralObservedLadderReport301.display_report (n i : Nat) (hi : i ≤ n) :
    report (context n) display [point n i (by omega)] =
      captured (snapshot n) (pos n i (by omega)) 0 0 (point n (i+1) (by omega))
```

```lean
theorem Yulang.GeneralObservedLadderReport301.list_as_int (n i : Nat) (hi : i ≤ n) :
    report (context n) intDisplay [point n i (by omega)] =
      { inspected := [point n i (by omega)], checked := [point n i (by omega),point n i (by omega)],
        conflicts := [point n i (by omega)] }
```

```lean
theorem Yulang.GeneralObservedLadderReport301.int_as_list (n : Nat) :
    report (context n) display [point n (n+1) (Nat.le_refl _)] =
      { inspected := [point n (n+1) (Nat.le_refl _)],
        checked := [point n (n+1) (Nat.le_refl _),point n (n+1) (Nat.le_refl _)],
        conflicts := [point n (n+1) (Nat.le_refl _)] }
```

```lean
theorem Yulang.GeneralObservedLadderReport301.int_report (n : Nat) :
    report (context n) intDisplay [point n (n+1) (Nat.le_refl _)] =
      { inspected := [point n (n+1) (Nat.le_refl _)],
        checked := [point n (n+1) (Nat.le_refl _),point n (n+1) (Nat.le_refl _)] }
```

```lean
theorem Yulang.GeneralObservedLadderReport301.exact_at (n i : Nat) (hi : i ≤ n+1) :
    (Finished (report (context n) display [point n i hi]) ↔ i ≤ n) ∧
    (Finished (report (context n) intDisplay [point n i hi]) ↔ i = n+1)
```


## lean/Yulang/GeneralObservedLadderRoot301.lean

```lean
theorem Yulang.GeneralObservedLadderRoot301.frame (n : Nat) : Frame compiled (initial n).core displayRoot 1 (top n)
```

```lean
theorem Yulang.GeneralObservedLadderRoot301.initial_requests (n : Nat) (focus : Occurrence roles) :
    GeneralNominalCenteredHeadOutputs.requests (initial n).core focus = []
```

```lean
theorem Yulang.GeneralObservedLadderRoot301.ready (n : Nat) :
    GeneralNominalCenteredHeadMatEffects.Ready (initial n).core displayRoot (top n)
```

```lean
theorem Yulang.GeneralObservedLadderRoot301.administrative (n : Nat) : GeneralNominalVersionedDiagnostic232.AdministrativeReady (initial n) displayRoot
```

```lean
theorem Yulang.GeneralObservedLadderRoot301.safe (n : Nat) : B4TargetV8.SafeKnown (GeneralNominalVersionedDiagnostic232.boundary roles)
    compiled (initial n) displayRoot
```

```lean
theorem Yulang.GeneralObservedLadderRoot301.positions (n : Nat) : GeneralNominalVersionedCycles232.Safe (initial n) (top n)
```

```lean
theorem Yulang.GeneralObservedLadderRoot301.alternatives (n : Nat) : AlternativesSafe compiled (initial n) (top n).input
```

```lean
theorem Yulang.GeneralObservedLadderRoot301.requests (n : Nat) (focus : Occurrence roles) :
    GeneralNominalCenteredHeadOutputs.requests (after n).core focus = []
```

```lean
theorem Yulang.GeneralObservedLadderRoot301.installation (n : Nat) (m : Assignment) (valid : Models (initial n) m) :
    InstallationModels (initial n) (effect n) m
```

```lean
theorem Yulang.GeneralObservedLadderRoot301.enabled (n : Nat) : Installable compiled (initial n) (effect n)
```

```lean
theorem Yulang.GeneralObservedLadderRoot301.not_committed (n : Nat) : ¬ Committed (initial n) (top n)
```

```lean
theorem Yulang.GeneralObservedLadderRoot301.actual (n : Nat) : (boundary roles).Step registry displayRoot (initial n) (after n)
```

```lean
theorem Yulang.GeneralObservedLadderRoot301.models (n : Nat) (m : Assignment) : Models (after n) m ↔ Models (initial n) m
```

```lean
theorem Yulang.GeneralObservedLadderRoot301.generated (n : Nat) :
    B4TargetV8.Reachable (boundary roles) registry displayRoot (after n) ∧
      GeneralNominalSaturationState.Generated (after n).core.erased.current displayRoot (next n)
```


## lean/Yulang/GeneralObservedLadderRoute301.lean

```lean
theorem Yulang.GeneralObservedLadderRoute301.climbs (n k : Nat) : invocation n k < invocation n (k+1)
```

```lean
theorem Yulang.GeneralObservedLadderRoute301.strictly_monotone (n : Nat) : ∀ {i j}, i < j → invocation n i < invocation n j
```

```lean
theorem Yulang.GeneralObservedLadderRoute301.injective (n : Nat) : Function.Injective (invocation n)
```

```lean
theorem Yulang.GeneralObservedLadderRoute301.child_id (n i : Nat) (hi : i ≤ n) :
    (child n i (invocation n i) hi).occurrence.identity = invocation n (i+1)
```

```lean
theorem Yulang.GeneralObservedLadderRoute301.child_site (n i : Nat) (hi : i ≤ n) :
    child n i (invocation n i) hi = site n (i+1)
```

```lean
theorem Yulang.GeneralObservedLadderRoute301.observed (n i : Nat) : (site n i).observed = GeneralNominalDemandMerging.pointSite (focus n i)
```

```lean
theorem Yulang.GeneralObservedLadderRoute301.inputs (n i : Nat) : (site n i).observed.inputs = [some (.source i)]
```

```lean
theorem Yulang.GeneralObservedLadderRoute301.sites_exact (n k : Nat) (s : Site roles) :
    s ∈ sites n k ↔ ∃ i, i ≤ k ∧ s = site n i
```

```lean
theorem Yulang.GeneralObservedLadderRoute301.unique_row (n k i : Nat) (s : Site roles)
    (member : s ∈ sites n k) (matchId : s.occurrence = focus n i) : s = site n i
```

```lean
theorem Yulang.GeneralObservedLadderRoute301.edge_exact (n k : Nat) (edge : Occurrence roles × Occurrence roles) :
    edge ∈ edges n k ↔ ∃ i, i < k ∧ edge = (focus n i,focus n (i+1))
```


## lean/Yulang/GeneralObservedLadderSafety301.lean

```lean
theorem Yulang.GeneralObservedLadderSafety301.towers (n id : Nat) : (finiteModel n id).1 = tower (n+1-id)
```

```lean
theorem Yulang.GeneralObservedLadderSafety301.semantic (n : Nat) {s : State roles} (valid : Models s (finiteModel n)) (origin) :
    ¬ GeneralNominalVersionedCycles232.Cyclic s origin
```

```lean
theorem Yulang.GeneralObservedLadderSafety301.raw_edge (n : Nat) (s : GeneralNominalState.State) (noShapes : s.view.kinds = 0)
    (valid : GeneralNominalState.Models s (finiteModel n))
    {a b : Fin s.base.slots} (edge : GeneralNominalMixedRecurrence.Edge s a b) :
    depth n s b < depth n s a
```

```lean
theorem Yulang.GeneralObservedLadderSafety301.raw_acyclic (n : Nat) (s : GeneralNominalState.State) (noShapes : s.view.kinds = 0)
    (valid : GeneralNominalState.Models s (finiteModel n)) (i : Fin s.base.slots) :
    ¬ GeneralNominalCycleK2.RecursAt s i
```


## lean/Yulang/GeneralObservedLadderScopedB4301.lean

```lean
theorem Yulang.GeneralObservedLadderScopedB4301.suffix_generated (p : Phase n k) (i j : Nat) (low : i ≤ j) (high : j ≤ k) :
    Generated p.state.core.erased.current (focus n i) (focus n j)
```

```lean
theorem Yulang.GeneralObservedLadderScopedB4301.not_stable_before (n k : Nat) (before : k ≤ n) (i : Nat) (hi : i ≤ k) :
    ¬ (boundary roles).Stable registry (run n k (by omega)).state (focus n i)
```

```lean
theorem Yulang.GeneralObservedLadderScopedB4301.stable_iff_final (n k : Nat) (cap : k ≤ n+1) (i : Nat) (hi : i ≤ k) :
    (boundary roles).Stable registry (run n k cap).state (focus n i) ↔ k = n+1
```

```lean
theorem Yulang.GeneralObservedLadderScopedB4301.evidence_at_phases (n k : Nat) (cap : k ≤ n+1) :
    B4SkeletonV8.EvidenceAt (boundary roles) registry (run n k cap).state displayRoot
```

```lean
theorem Yulang.GeneralObservedLadderScopedB4301.evidence_at_reachable (n : Nat) (s : State roles)
    (fromThisInitial : Steps ((boundary roles).Step registry displayRoot) (initial n) s) :
    B4SkeletonV8.EvidenceAt (boundary roles) registry s displayRoot
```

```lean
theorem Yulang.GeneralObservedLadderScopedB4301.generated_children_at_reachable (n : Nat) (s : State roles)
    (fromThisInitial : Steps ((boundary roles).Step registry displayRoot) (initial n) s)
    (o : Occurrence roles) (inScope : o = displayRoot ∨ (boundary roles).Generated registry s displayRoot o)
    (stable : (boundary roles).Stable registry s o) (key : Nat) (children : List (Occurrence roles))
    (selected : Local (boundary roles) registry s o (.selected key children)) :
    ∀ c ∈ children, (boundary roles).Generated registry s displayRoot c
```

```lean
theorem Yulang.GeneralObservedLadderScopedB4301.closure_of_any_terminal (n : Nat) (s : State roles)
    (path : Steps ((boundary roles).Step registry displayRoot) (initial n) s)
    (noMore : ∀ next, ¬ (boundary roles).Step registry displayRoot s next) :
    s = (final n).state
```

```lean
theorem Yulang.GeneralObservedLadderScopedB4301.compiled_at_terminal (n : Nat) (s : State roles)
    (path : Steps ((boundary roles).Step registry displayRoot) (initial n) s)
    (noMore : ∀ next, ¬ (boundary roles).Step registry displayRoot s next)
    (d : Dictionary) :
    (Classify (boundary roles) registry s displayRoot (.selected d) ↔ d = dictionary (n+1)) ∧
    (∀ m, Models s m → (boundary roles).Evidence registry s m displayRoot (dictionary (n+1)))
```


## lean/Yulang/GeneralObservedLadderSelection301.lean

```lean
theorem Yulang.GeneralObservedLadderSelection301.metadata (n : Nat) : Metadata compiled (context n)
```

```lean
theorem Yulang.GeneralObservedLadderSelection301.linked (n i id : Nat) (hi : i ≤ n+1) :
    GeneralNominalState.Linked (snapshot n) (inputs (occurrence i id)).demand
```

```lean
theorem Yulang.GeneralObservedLadderSelection301.known (n i id : Nat) (hi : i ≤ n+1) :
    ¬ GeneralNominalState.RootPending (snapshot n) (inputs (occurrence i id)).demand
```

```lean
theorem Yulang.GeneralObservedLadderSelection301.fresh (n id : Nat) (bs) : GeneralNominalVersionedAllocation231.Fresh (snapshot n) compiled id bs
```

```lean
theorem Yulang.GeneralObservedLadderSelection301.located (n i id : Nat) (hi : i ≤ n+1) :
    arguments (context n) (inputs (occurrence i id)) = some [point n i hi]
```

```lean
theorem Yulang.GeneralObservedLadderSelection301.prepared (n i id : Nat) (hi : i ≤ n) : Prepared compiled (context n) (occurrence i id) display
```

```lean
theorem Yulang.GeneralObservedLadderSelection301.failed_int (n i id : Nat) (hi : i ≤ n) :
    Failed compiled (context n) (occurrence i id) intDisplay
```

```lean
theorem Yulang.GeneralObservedLadderSelection301.int_not_prepared (n i id : Nat) (hi : i ≤ n) :
    ¬ Prepared compiled (context n) (occurrence i id) intDisplay
```

```lean
theorem Yulang.GeneralObservedLadderSelection301.child_occurrence (n i id : Nat) (hi : i ≤ n) :
    (child n i id hi).occurrence = occurrence (i+1) (child n i id hi).occurrence.identity
```

```lean
theorem Yulang.GeneralObservedLadderSelection301.one_child (n i id : Nat) (hi : i ≤ n) :
    children (packet n i id hi) = [(child n i id hi).occurrence]
```

```lean
theorem Yulang.GeneralObservedLadderSelection301.unique (n i id : Nat) (hi : i ≤ n) :
    Unique compiled (context n) (occurrence i id) 1 [(child n i id hi).occurrence]
```


## lean/Yulang/GeneralObservedLadderSemanticGap301.lean

```lean
theorem Yulang.GeneralObservedLadderSemanticGap301.same_models (n : Nat) (m : Assignment) :
    GeneralNominalState.Models (equationOnly n).state m ↔ GeneralNominalState.Models (snapshot n) m
```

```lean
theorem Yulang.GeneralObservedLadderSemanticGap301.unresolved (n : Nat) :
    (equationOnly n).state.nominals (endpoint n) = none ∧
      (equationOnly n).state.view.heads (endpoint n) = .deferred .unresolved
```

```lean
theorem Yulang.GeneralObservedLadderSemanticGap301.old_int_report (n : Nat) :
    report (equationOnly n) intDisplay [terminalPoint n] =
      { inspected := [terminalPoint n], checked := [terminalPoint n,terminalPoint n],
        blocked := [terminalPoint n] }
```

```lean
theorem Yulang.GeneralObservedLadderSemanticGap301.old_list_report (n : Nat) :
    report (equationOnly n) display [terminalPoint n] =
      { inspected := [terminalPoint n], checked := [terminalPoint n,terminalPoint n],
        blocked := [terminalPoint n] }
```

```lean
theorem Yulang.GeneralObservedLadderSemanticGap301.no_observation (n : Nat) : probe (equationOnly n) [terminalPoint n] = none
```

```lean
theorem Yulang.GeneralObservedLadderSemanticGap301.observed (n : Nat) : probe (context n) [point n (n+1) (Nat.le_refl _)] = some ⟨3,[]⟩
```

```lean
theorem Yulang.GeneralObservedLadderSemanticGap301.strict_gap (n : Nat) :
    (∀ m, GeneralNominalState.Models (equationOnly n).state m ↔ GeneralNominalState.Models (snapshot n) m) ∧
      probe (equationOnly n) [terminalPoint n] ≠ probe (context n) [point n (n+1) (Nat.le_refl _)]
```


## lean/Yulang/GeneralObservedLadderSemantics301.lean

```lean
theorem Yulang.GeneralObservedLadderSemantics301.update_support (m : Assignment) (valid : GeneralNominalState.Models (snapshot n) m) :
    Ordinary (packet n i id hi) m ∧
      ProjectionModels (snapshot n) (GeneralNominalPacketSupport.report (packet n i id hi)) m
```

```lean
theorem Yulang.GeneralObservedLadderSemantics301.projected (inner : i ≤ n) (m : Assignment) (valid : GeneralNominalState.Models (snapshot n) m) :
    GeneralNominalOriginTerms.Same m (origin i) (.source (i+1))
```

```lean
theorem Yulang.GeneralObservedLadderSemantics301.holds (m : Assignment) (valid : GeneralNominalState.Models (snapshot n) m) :
    Holds (plan n i id hi) m
```


## lean/Yulang/GeneralObservedLadderSource301.lean

```lean
theorem Yulang.GeneralObservedLadderSource301.nominal_at (n i : Nat) (hi : i ≤ n) :
    (snapshot n).nominals ⟨i,by change i < n+2; omega⟩ =
      some (GeneralNominalOutputGrowthModels.descriptor n ⟨i,by omega⟩ hi)
```

```lean
theorem Yulang.GeneralObservedLadderSource301.scalar_at (n : Nat) : (snapshot n).view.heads (endpoint n) = .scalar .int
```

```lean
theorem Yulang.GeneralObservedLadderSource301.scalar_model (n : Nat) (m : Assignment)
    (satisfies : GeneralNominalState.Models (snapshot n) m) :
    Equivalent (m (n+1)).1 (.base .int)
```

```lean
theorem Yulang.GeneralObservedLadderSource301.linear_model (n : Nat) (m : Assignment) (satisfies : GeneralNominalState.Models (snapshot n) m) :
    PrefixModels n m
```

```lean
theorem Yulang.GeneralObservedLadderSource301.models_exact (n : Nat) (m : Assignment) :
    GeneralNominalState.Models (snapshot n) m ↔
    PrefixModels n m ∧ Equivalent (m (n+1)).1 (.base .int)
```

```lean
theorem Yulang.GeneralObservedLadderSource301.model_exists (n : Nat) :
    GeneralNominalState.Models (snapshot n) (GeneralNominalOutputGrowth.finiteModel n)
```

```lean
theorem Yulang.GeneralObservedLadderSource301.slot_model (n : Nat) (m : Assignment)
    (satisfies : GeneralNominalState.Models (snapshot n) m) (remaining : Nat) (cap : remaining ≤ n+1) :
    Equivalent (m (n+1-remaining)).1 (tower remaining)
```


## lean/Yulang/GeneralObservedLadderStage301.lean

```lean
theorem Yulang.GeneralObservedLadderStage301.model (p : Phase n k) : GeneralNominalVersionedJournal232.Models p.state (finiteModel n)
```

```lean
theorem Yulang.GeneralObservedLadderStage301.metadata (p : Phase n k) : Metadata compiled (env p)
```

```lean
theorem Yulang.GeneralObservedLadderStage301.located (p : Phase n k) (bound : k ≤ n+1) :
    arguments (env p) (inputs (focus n k)) = some [point n k bound]
```

```lean
theorem Yulang.GeneralObservedLadderStage301.linked (p : Phase n k) (bound : k ≤ n+1) :
    GeneralNominalState.Linked (env p).state (inputs (focus n k)).demand
```

```lean
theorem Yulang.GeneralObservedLadderStage301.known (p : Phase n k) (bound : k ≤ n+1) :
    ¬ GeneralNominalState.RootPending (env p).state (inputs (focus n k)).demand
```

```lean
theorem Yulang.GeneralObservedLadderStage301.finished_iff (p : Phase n k) (d : GeneralDeclarations.Declaration) (bound : k ≤ n+1) :
    Finished (report (env p) d [point n k bound]) ↔ Finished (report (context n) d [point n k bound])
```

```lean
theorem Yulang.GeneralObservedLadderStage301.list_prepared (p : Phase n k) (hi : k ≤ n) :
    Prepared compiled (env p) (focus n k) display
```

```lean
theorem Yulang.GeneralObservedLadderStage301.wrong_list (p : Phase n (n+1)) : Failed compiled (env p) (focus n (n+1)) display
```

```lean
theorem Yulang.GeneralObservedLadderStage301.wrong_int (p : Phase n k) (hi : k ≤ n) : Failed compiled (env p) (focus n k) intDisplay
```

```lean
theorem Yulang.GeneralObservedLadderStage301.no_int (p : Phase n k) (hi : k ≤ n) : ¬ Prepared compiled (env p) (focus n k) intDisplay
```

```lean
theorem Yulang.GeneralObservedLadderStage301.no_list (p : Phase n (n+1)) : ¬ Prepared compiled (env p) (focus n (n+1)) display
```

```lean
theorem Yulang.GeneralObservedLadderStage301.stage_emits (p : Phase n k) (hi : k ≤ n) :
    GeneralNominalVersionedChildren232.emitted (stagePlan p hi) = [site n (k+1)]
```

```lean
theorem Yulang.GeneralObservedLadderStage301.stage_children (p : Phase n k) (hi : k ≤ n) :
    children (stagePlan p hi).packet = [focus n (k+1)]
```

```lean
theorem Yulang.GeneralObservedLadderStage301.unique (p : Phase n k) (hi : k ≤ n) :
    Unique compiled (env p) (focus n k) 1 [focus n (k+1)]
```

```lean
theorem Yulang.GeneralObservedLadderStage301.center_recorded (p : Phase n k) : site n k ∈ p.state.core.sites
```

```lean
theorem Yulang.GeneralObservedLadderStage301.raw_recorded (p : Phase n k) : GeneralNominalDemandMerging.pointSite (focus n k) ∈
    p.state.core.erased.current.sites
```

```lean
theorem Yulang.GeneralObservedLadderStage301.frame (p : Phase n k) (hi : k ≤ n) :
    Frame compiled p.state.core (focus n k) 1 (stagePlan p hi)
```

```lean
theorem Yulang.GeneralObservedLadderStage301.raw_is (p : Phase n k) (s : GeneralNominalDemandMerging.Site roles)
    (member : s ∈ p.state.core.erased.current.sites) (eq : s.occurrence = focus n i) :
    s = GeneralNominalDemandMerging.pointSite (focus n i)
```

```lean
theorem Yulang.GeneralObservedLadderStage301.current_requests (p : Phase n k) (focus : Occurrence roles) :
    GeneralNominalCenteredHeadOutputs.requests p.state.core focus = []
```

Indexed 273 theorem declarations. Each has one standalone audit.
