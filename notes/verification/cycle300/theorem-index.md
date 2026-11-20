# Cycle 300: exact theorem signatures

## lean/Yulang/GeneralDepthTwoCenters300.lean

```lean
theorem Yulang.GeneralDepthTwoCenters300.symbolic_exact (i : Nat) :
    (model i).1 = tower (symbolicDepth i)
```

```lean
theorem Yulang.GeneralDepthTwoCenters300.bounded_same {i j : Nat} (a : i ≤ 2) (b : j ≤ 2)
    (equal : Equivalent (model i).1 (model j).1) : i = j
```

```lean
theorem Yulang.GeneralDepthTwoCenters300.same_center {s : State roles} (held : Models s model) {a b : Site roles}
    (same : SameInputs (Models s) a b) {i j : Nat}
    (left : a.observed.inputs = [some (.source i)])
    (right : b.observed.inputs = [some (.source j)]) :
    Equivalent (model i).1 (model j).1
```

```lean
theorem Yulang.GeneralDepthTwoCenters300.distinct_center {s : State roles} (held : Models s model) {a b : Site roles} {i j : Nat}
    (left : a.observed.inputs = [some (.source i)]) (right : b.observed.inputs = [some (.source j)])
    (ai : i ≤ 2) (bj : j ≤ 2) (different : i ≠ j) :
    ¬ SameInputs (Models s) a b
```


## lean/Yulang/GeneralDepthTwoCertifiedRead300.lean

```lean
theorem Yulang.GeneralDepthTwoCertifiedRead300.providers : Providers registry final table decode
```

```lean
theorem Yulang.GeneralDepthTwoCertifiedRead300.rooted : Rooted table 0
```

```lean
theorem Yulang.GeneralDepthTwoCertifiedRead300.compiled_final :
    Classify (boundary roles) registry final root (.selected (.node 1 [.node 1 [.node 3 []]])) ∧
    ∀ m, Models final m → (boundary roles).Evidence registry final m root (.node 1 [.node 1 [.node 3 []]])
```

```lean
theorem Yulang.GeneralDepthTwoCertifiedRead300.chosen_generated (n : Node) :
    demand n = root ∨ (boundary roles).Generated registry final root (demand n)
```

```lean
theorem Yulang.GeneralDepthTwoCertifiedRead300.curr_enabled (n : Node) :
    GeneralNominalVersionedMixedKernel234.Installable compiled final (GeneralDepthTwoFinalCurrent300.certificate n)
```

```lean
theorem Yulang.GeneralDepthTwoCertifiedRead300.all_chosen_committed (n : Node) :
    GeneralNominalVersionedMixedKernel234.Committed final (plan n)
```

```lean
theorem Yulang.GeneralDepthTwoCertifiedRead300.evidence_at : B4SkeletonV8.EvidenceAt (boundary roles) registry final root
```

```lean
theorem Yulang.GeneralDepthTwoCertifiedRead300.checked_rank :
    GeneralGeneratedDictionaryRankBook299.get 0 (GeneralGeneratedDictionaryRankBook299.ranks table [0,1,2] 3) = some 3 ∧
    GeneralGeneratedDictionaryRankBook299.get 1 (GeneralGeneratedDictionaryRankBook299.ranks table [0,1,2] 3) = some 2 ∧
    GeneralGeneratedDictionaryRankBook299.get 2 (GeneralGeneratedDictionaryRankBook299.ranks table [0,1,2] 3) = some 1
```


## lean/Yulang/GeneralDepthTwoEarlyShared300.lean

```lean
theorem Yulang.GeneralDepthTwoEarlyShared300.headless_transfer (s : State roles)
    (transfer : ∀ m, Models final m → Models s m)
    (known : ∀ id, id ≤ 2 → GeneralNominalState.Known s.core.erased.current.context.state id) :
    HeadlessUnknown s
```

```lean
theorem Yulang.GeneralDepthTwoEarlyShared300.equality_transfer (s : State roles)
    (transfer : ∀ m, Models final m → Models s m) : EqualityClosed s
```

```lean
theorem Yulang.GeneralDepthTwoEarlyShared300.headless_initial : HeadlessUnknown initial
```

```lean
theorem Yulang.GeneralDepthTwoEarlyShared300.headless_after : HeadlessUnknown after
```

```lean
theorem Yulang.GeneralDepthTwoEarlyShared300.equality_initial : EqualityClosed initial
```

```lean
theorem Yulang.GeneralDepthTwoEarlyShared300.equality_after : EqualityClosed after
```

```lean
theorem Yulang.GeneralDepthTwoEarlyShared300.closed_initial : GeneralNominalReobservationSteps.PointClosed initial.core.erased.current.context.state
```

```lean
theorem Yulang.GeneralDepthTwoEarlyShared300.closed_after : GeneralNominalReobservationSteps.PointClosed after.core.erased.current.context.state
```

```lean
theorem Yulang.GeneralDepthTwoEarlyShared300.same_effect (a b : Effect roles) (reg : a.registry = b.registry)
    (ctx : a.snapshot = b.snapshot) (plan : a.plan = b.plan) : a = b
```


## lean/Yulang/GeneralDepthTwoEvidence300.lean

```lean
theorem Yulang.GeneralDepthTwoEvidence300.terminal_instance (m : Assignment) (valid : Models final m) :
    Instance compiled final.core m terminal 3 []
```

```lean
theorem Yulang.GeneralDepthTwoEvidence300.terminal_evidence (m : Assignment) (valid : Models final m) :
    (boundary roles).Evidence registry final m terminal (.node 3 [])
```

```lean
theorem Yulang.GeneralDepthTwoEvidence300.middle_evidence (m : Assignment) (valid : Models final m) :
    (boundary roles).Evidence registry final m middle (.node 1 [.node 3 []])
```

```lean
theorem Yulang.GeneralDepthTwoEvidence300.root_evidence (m : Assignment) (valid : Models final m) :
    (boundary roles).Evidence registry final m root (.node 1 [.node 1 [.node 3 []]])
```

```lean
theorem Yulang.GeneralDepthTwoEvidence300.final_models (m : Assignment) : Models final m ↔ Models initial m
```

```lean
theorem Yulang.GeneralDepthTwoEvidence300.final_edges : final.core.erased.current.edges = [(root,middle),(middle,terminal)]
```

```lean
theorem Yulang.GeneralDepthTwoEvidence300.actual_dictionary :
    (boundary roles).Step registry root initial after ∧
    (boundary roles).Step registry root after final ∧
    B4TargetV8.Reachable (boundary roles) registry root final ∧
    GeneralNominalSaturationState.Generated final.core.erased.current root terminal ∧
    (∃ m, Models final m) ∧
    (∀ m, Models final m ↔ Models initial m) ∧
    ∀ m, Models final m → (boundary roles).Evidence registry final m root (.node 1 [.node 1 [.node 3 []]])
```


## lean/Yulang/GeneralDepthTwoFinalCurrent300.lean

```lean
theorem Yulang.GeneralDepthTwoFinalCurrent300.emitted_extended (res updates owns) (p : Plan roles) :
    emitted (extendedPlan res updates owns p) = emitted p
```

```lean
theorem Yulang.GeneralDepthTwoFinalCurrent300.emitted_replay (p : Plan roles) : emitted (replayPlan p) = emitted p
```

```lean
theorem Yulang.GeneralDepthTwoFinalCurrent300.child_exact (n : Node) : children (plan n).packet = (childNodes n).map demand
```

```lean
theorem Yulang.GeneralDepthTwoFinalCurrent300.emitted_layout (n : Node) :
    emitted (plan n) = (childNodes n).map (fun j => (plan j).input)
```

```lean
theorem Yulang.GeneralDepthTwoFinalCurrent300.raw_sites_retained (n : Node) :
    (installCore final.core (plan n)).erased.current.sites ⊆ final.core.erased.current.sites
```

```lean
theorem Yulang.GeneralDepthTwoFinalCurrent300.no_additional_requests (n : Node) (focus : GeneralSourceDictionaries.Occurrence roles) :
    GeneralNominalCenteredHeadOutputs.requests (installCore final.core (plan n)) focus = []
```

```lean
theorem Yulang.GeneralDepthTwoFinalCurrent300.ready_at_site (n : Node) : GeneralNominalCenteredHeadMatEffects.Ready final.core (plan n).packet.site.occurrence (plan n)
```

```lean
theorem Yulang.GeneralDepthTwoFinalCurrent300.key_eq (n : Node) : (plan n).packet.declaration.id = code n
```

```lean
theorem Yulang.GeneralDepthTwoFinalCurrent300.installation (n : Node) (m : Assignment) (valid : Models final m) :
    InstallationModels final (certificate n) m
```

```lean
theorem Yulang.GeneralDepthTwoFinalCurrent300.safe_positions (n : Node) : GeneralNominalVersionedCycles232.Safe final (plan n)
```

```lean
theorem Yulang.GeneralDepthTwoFinalCurrent300.compatible (n : Node) :
    GeneralNominalCycleSteps.ChoiceCompatible final.core.erased.current (plan n).packet
```

```lean
theorem Yulang.GeneralDepthTwoFinalCurrent300.alternatives (n : Node) : AlternativesSafe compiled final (plan n).input
```

```lean
theorem Yulang.GeneralDepthTwoFinalCurrent300.replay_schema (p : Plan roles) :
    GeneralNominalVersionedPlans231.emittedSchema (replayPlan p) =
    GeneralNominalVersionedPlans231.emittedSchema p
```

```lean
theorem Yulang.GeneralDepthTwoFinalCurrent300.current (n : Node) : Current compiled final (demand n) (certificate n)
```


## lean/Yulang/GeneralDepthTwoFinalHalt300.lean

```lean
theorem Yulang.GeneralDepthTwoFinalHalt300.recorded (focus : Occurrence roles) (reachable : Generated final.core.erased.current root focus) :
    ∃ s ∈ final.core.erased.current.sites, s.occurrence = focus
```

```lean
theorem Yulang.GeneralDepthTwoFinalHalt300.halted (next : State roles) : ¬ Step compiled root final next
```

```lean
theorem Yulang.GeneralDepthTwoFinalHalt300.source_halted (next : State roles) : ¬ (boundary roles).Step registry root final next
```

```lean
theorem Yulang.GeneralDepthTwoFinalHalt300.stable (n : Node) : (boundary roles).Stable registry final (demand n)
```


## lean/Yulang/GeneralDepthTwoFinalNodes300.lean

```lean
theorem Yulang.GeneralDepthTwoFinalNodes300.frame (n : Node) (m : Assignment) (valid : Models final m) :
    Frame compiled final.core (demand n) (code n) (plan n)
```

```lean
theorem Yulang.GeneralDepthTwoFinalNodes300.plan_holds (n : Node) (m : Assignment) (valid : Models final m) : Holds (plan n) m
```

```lean
theorem Yulang.GeneralDepthTwoFinalNodes300.declaration (n : Node) : (plan n).packet.declaration = family n
```

```lean
theorem Yulang.GeneralDepthTwoFinalNodes300.exact_code (n : Node) : (family n).id = code n
```

```lean
theorem Yulang.GeneralDepthTwoFinalNodes300.role (n : Node) : (demand n).demand.role = 0
```

```lean
theorem Yulang.GeneralDepthTwoFinalNodes300.args (n : Node) : ∀ i, (inputs (demand n)).demand.arguments i =
    ((source n).val,(source n).val)
```

```lean
theorem Yulang.GeneralDepthTwoFinalNodes300.located (n : Node) : GeneralNominalRecursiveCandidates.arguments env (inputs (demand n)) =
    some [(source n,source n)]
```

```lean
theorem Yulang.GeneralDepthTwoFinalNodes300.known_slots (n : Node) : GeneralNominalState.Known env.state (source n).val
```

```lean
theorem Yulang.GeneralDepthTwoFinalNodes300.not_pending (n : Node) : ¬ GeneralNominalState.RootPending env.state (inputs (demand n)).demand
```

```lean
theorem Yulang.GeneralDepthTwoFinalNodes300.observed_inputs (n : Node) :
    (plan n).input.observed.inputs = [some (.source (source n).val)]
```

```lean
theorem Yulang.GeneralDepthTwoFinalNodes300.center_enum : final.core.sites = [(plan .outer).input,(plan .inner).input,(plan .leaf).input]
```

```lean
theorem Yulang.GeneralDepthTwoFinalNodes300.center_hit (s : Site roles) (present : s ∈ final.core.sites) : ∃ n : Node, s = (plan n).input
```

```lean
theorem Yulang.GeneralDepthTwoFinalNodes300.centers_equal (a b : Node) (same : GeneralNominalCenters.SameInputs (Models final)
    (plan a).input (plan b).input) : a = b
```

```lean
theorem Yulang.GeneralDepthTwoFinalNodes300.administrative (n : Node) :
    GeneralNominalVersionedDiagnostic232.AdministrativeReady final (demand n)
```


## lean/Yulang/GeneralDepthTwoFinalParents300.lean

```lean
theorem Yulang.GeneralDepthTwoFinalParents300.owns_previous_root :
    GeneralNominalVersionedAllocation231.keys compiled root.identity oldRoot.packet.bindings ⊆
      oldRoot.packet.context.state.allocated ++ allocated middleCommit.packet
```

```lean
theorem Yulang.GeneralDepthTwoFinalParents300.new_atoms (m : Assignment) (valid : Models final m) :
    PresenceNormalForm.All CommonNominalFullCarrier.model m (atoms middleCommit.packet)
```

```lean
theorem Yulang.GeneralDepthTwoFinalParents300.root_holds (m : Assignment) (valid : Models final m) : Holds rootNow m
```

```lean
theorem Yulang.GeneralDepthTwoFinalParents300.root_frame (m : Assignment) (valid : Models final m) :
    Frame compiled final.core root 1 rootNow
```

```lean
theorem Yulang.GeneralDepthTwoFinalParents300.root_children : children rootNow.packet = [middle]
```

```lean
theorem Yulang.GeneralDepthTwoFinalParents300.root_instance (m : Assignment) (valid : Models final m) :
    Instance compiled final.core m root 1 [middle]
```

```lean
theorem Yulang.GeneralDepthTwoFinalParents300.middle_frame (m : Assignment) (valid : Models final m) :
    Frame compiled final.core middle 1 middleNow
```

```lean
theorem Yulang.GeneralDepthTwoFinalParents300.middle_holds (m : Assignment) (valid : Models final m) : Holds middleNow m
```

```lean
theorem Yulang.GeneralDepthTwoFinalParents300.middle_children : children middleNow.packet = [terminal]
```

```lean
theorem Yulang.GeneralDepthTwoFinalParents300.middle_instance (m : Assignment) (valid : Models final m) :
    Instance compiled final.core m middle 1 [terminal]
```


## lean/Yulang/GeneralDepthTwoFinalScope300.lean

```lean
theorem Yulang.GeneralDepthTwoFinalScope300.id_injective (a b : Node) (eq : (demand a).identity = (demand b).identity) : a = b
```

```lean
theorem Yulang.GeneralDepthTwoFinalScope300.demand_injective (a b : Node) (eq : demand a = demand b) : a = b
```

```lean
theorem Yulang.GeneralDepthTwoFinalScope300.alias_identity {a b : Nat} (same : Alias final.core.erased.current a b) : a = b
```

```lean
theorem Yulang.GeneralDepthTwoFinalScope300.raw_enum : final.core.erased.current.sites =
    [(plan .outer).packet.site,(plan .inner).packet.site,(plan .leaf).packet.site]
```

```lean
theorem Yulang.GeneralDepthTwoFinalScope300.raw_hit (s : GeneralNominalDemandMerging.Site roles) (present : s ∈ final.core.erased.current.sites) :
    ∃ n : Node, s = (plan n).packet.site
```

```lean
theorem Yulang.GeneralDepthTwoFinalScope300.site_focus (n : Node) : (plan n).packet.site.occurrence = demand n
```

```lean
theorem Yulang.GeneralDepthTwoFinalScope300.generated_only (d : Occurrence roles) (p : Generated final.core.erased.current root d) :
    ∃ n : Node, d = demand n
```

```lean
theorem Yulang.GeneralDepthTwoFinalScope300.paired_frame (n : Node) (p : Plan roles) (key : Nat)
    (candidate : Frame compiled final.core (demand n) key p) : p = plan n
```

```lean
theorem Yulang.GeneralDepthTwoFinalScope300.no_raw_install (e : Effect roles) (enabled : Installable compiled final e)
    (there : Generated final.core.erased.current root e.plan.packet.site.occurrence) :
    Committed final e.plan
```

```lean
theorem Yulang.GeneralDepthTwoFinalScope300.point_closed : GeneralNominalReobservationSteps.PointClosed final.core.erased.current.context.state
```


## lean/Yulang/GeneralDepthTwoFinalSelection300.lean

```lean
theorem Yulang.GeneralDepthTwoFinalSelection300.fresh_at_final (owner : Nat) (bs) :
    GeneralNominalVersionedAllocation231.Fresh env.state compiled owner bs
```

```lean
theorem Yulang.GeneralDepthTwoFinalSelection300.options (n : Node) {d : Declaration} (visible : d ∈ compiled.declarations)
    (atRole : d.role = (demand n).demand.role) : d = family n ∨ d = other n
```

```lean
theorem Yulang.GeneralDepthTwoFinalSelection300.wrong_failed (n : Node) : Failed compiled env (demand n) (other n)
```

```lean
theorem Yulang.GeneralDepthTwoFinalSelection300.wrong_unprepared (n : Node) : ¬ Prepared compiled env (demand n) (other n)
```

```lean
theorem Yulang.GeneralDepthTwoFinalSelection300.own_prepared (n : Node) : Prepared compiled env (demand n) (family n)
```

```lean
theorem Yulang.GeneralDepthTwoFinalSelection300.safe (n : Node) :
    B4TargetV8.SafeKnown (GeneralNominalVersionedDiagnostic232.boundary roles) compiled final (demand n)
```

```lean
theorem Yulang.GeneralDepthTwoFinalSelection300.root_candidates :
    children compiled env root display display_checked [((0 : Fin 3),(0 : Fin 3))] = [middle]
```

```lean
theorem Yulang.GeneralDepthTwoFinalSelection300.middle_candidates :
    children compiled env middle display display_checked [((1 : Fin 3),(1 : Fin 3))] = [terminal]
```

```lean
theorem Yulang.GeneralDepthTwoFinalSelection300.leaf_candidates :
    children compiled env terminal intDisplay int_display_checked [((2 : Fin 3),(2 : Fin 3))] = []
```

```lean
theorem Yulang.GeneralDepthTwoFinalSelection300.survivor (n : Node) : Survivor compiled env (demand n) (code n) ((childNodes n).map demand)
```

```lean
theorem Yulang.GeneralDepthTwoFinalSelection300.unique (n : Node) : Unique compiled env (demand n) (code n) ((childNodes n).map demand)
```

```lean
theorem Yulang.GeneralDepthTwoFinalSelection300.ready (n : Node) : GeneralNominalCenteredHeadMatEffects.Ready final.core (demand n) (plan n)
```

```lean
theorem Yulang.GeneralDepthTwoFinalSelection300.not_merged (n : Node) :
    ¬ GeneralNominalVersionedMergedConflict232.MergedOutputConflict final (demand n)
```

```lean
theorem Yulang.GeneralDepthTwoFinalSelection300.selected (n : Node) :
    GeneralNominalVersionedMixedSourceBoundary234.Local registry final (demand n)
      (.selected (code n) ((childNodes n).map demand))
```


## lean/Yulang/GeneralDepthTwoFinalSeparators300.lean

```lean
theorem Yulang.GeneralDepthTwoFinalSeparators300.fixed (outside : Nat → Ty) (i : Nat) (small : i ≤ 2) : patch outside i = model i
```

```lean
theorem Yulang.GeneralDepthTwoFinalSeparators300.free (outside : Nat → Ty) (i : Nat) (large : 2 < i) :
    (patch outside i).1 = outside i
```

```lean
theorem Yulang.GeneralDepthTwoFinalSeparators300.snapshot_patched (outside : Nat → Ty) : GeneralNominalState.Models snapshot (patch outside)
```

```lean
theorem Yulang.GeneralDepthTwoFinalSeparators300.patched (outside : Nat → Ty) : Models final (patch outside)
```

```lean
theorem Yulang.GeneralDepthTwoFinalSeparators300.all_known (i : Nat) (small : i ≤ 2) :
    GeneralNominalState.Known GeneralDepthTwoTerminalPlan300.env.state i
```

```lean
theorem Yulang.GeneralDepthTwoFinalSeparators300.headless : HeadlessUnknown final
```

```lean
theorem Yulang.GeneralDepthTwoFinalSeparators300.not_top (i : Nat) : ¬ Equivalent .top (model i).1
```

```lean
theorem Yulang.GeneralDepthTwoFinalSeparators300.isolate (a b : Nat) (large : 2 < a) (apart : a ≠ b) :
    ¬ Equivalent (patch (mark a) a).1 (patch (mark a) b).1
```

```lean
theorem Yulang.GeneralDepthTwoFinalSeparators300.equality_names (a b : Nat) (same : Equal final a b) : a = b
```

```lean
theorem Yulang.GeneralDepthTwoFinalSeparators300.equality_closed : EqualityClosed final
```


## lean/Yulang/GeneralDepthTwoFirstInstall300.lean

```lean
theorem Yulang.GeneralDepthTwoFirstInstall300.administration : GeneralNominalVersionedDiagnostic232.AdministrativeReady initial root
```

```lean
theorem Yulang.GeneralDepthTwoFirstInstall300.safe : B4TargetV8.SafeKnown (GeneralNominalVersionedDiagnostic232.boundary roles)
    compiled initial root
```

```lean
theorem Yulang.GeneralDepthTwoFirstInstall300.positions : GeneralNominalVersionedCycles232.Safe initial plan
```

```lean
theorem Yulang.GeneralDepthTwoFirstInstall300.alternatives : AlternativesSafe compiled initial plan.input
```

```lean
theorem Yulang.GeneralDepthTwoFirstInstall300.requests (focus : Occurrence roles) :
    GeneralNominalCenteredHeadOutputs.requests after.core focus = []
```

```lean
theorem Yulang.GeneralDepthTwoFirstInstall300.installation (m : Assignment) (valid : Models initial m) :
    InstallationModels initial effect m
```

```lean
theorem Yulang.GeneralDepthTwoFirstInstall300.enabled : Installable compiled initial effect
```

```lean
theorem Yulang.GeneralDepthTwoFirstInstall300.actual : (boundary roles).Step registry root initial after
```

```lean
theorem Yulang.GeneralDepthTwoFirstInstall300.models (m : Assignment) : Models after m ↔ Models initial m
```

```lean
theorem Yulang.GeneralDepthTwoFirstInstall300.actual_middle :
    B4TargetV8.Reachable (boundary roles) registry root after ∧
      GeneralNominalSaturationState.Generated after.core.erased.current root middle
```


## lean/Yulang/GeneralDepthTwoFrameCarry300.lean

```lean
theorem Yulang.GeneralDepthTwoFrameCarry300.prepared_carried (context : Context) (registry : Registry) (root : Occurrence roles)
    (declaration : Declaration) (bounds : List (GeneralNominalInspection.Bounds context.state))
    (old : Prepared registry context root declaration)
    (located : arguments context (inputs root) = some bounds)
    (owned : GeneralNominalVersionedAllocation231.keys registry root.identity
      (bindings context.state (report context declaration bounds)) ⊆ context.state.allocated ++ allocated)
    (common : ∃ model, HeadModels registry (extend context reserved atoms allocated) root declaration bounds model) :
    Prepared registry (extend context reserved atoms allocated) root declaration
```

```lean
theorem Yulang.GeneralDepthTwoFrameCarry300.frame_carried (registry : Registry) (state : GeneralNominalCenteredSteps.State roles)
    (root : Occurrence roles) (key : Nat) (plan : Plan roles)
    (frame : GeneralNominalVersionedEvidence231.Frame registry state root key plan)
    (owned : GeneralNominalVersionedAllocation231.keys registry root.identity plan.packet.bindings ⊆
      plan.packet.context.state.allocated ++ allocated)
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalVersionedPlans231.Holds (extendedPlan reserved atoms allocated plan) model) :
    GeneralNominalVersionedEvidence231.Frame registry
      (GeneralNominalCenteredSteps.refresh state (extend state.erased.current.context reserved atoms allocated))
      root key (extendedPlan reserved atoms allocated plan)
```


## lean/Yulang/GeneralDepthTwoMachine300.lean

```lean
theorem Yulang.GeneralDepthTwoMachine300.distinct (a b : Phase) (same : raw a = raw b) : a = b
```

```lean
theorem Yulang.GeneralDepthTwoMachine300.exact_step (a b : Phase) :
    (boundary roles).Step registry root (raw a) (raw b) ↔ next a = some b
```

```lean
theorem Yulang.GeneralDepthTwoMachine300.generate_next (a : Phase) (s : State roles)
    (step : (boundary roles).Step registry root (raw a) s) :
    ∃ b, next a = some b ∧ raw b = s
```

```lean
theorem Yulang.GeneralDepthTwoMachine300.phases_complete (s : State roles) (path : Steps ((boundary roles).Step registry root) initial s) :
    ∃ p, raw p = s
```

```lean
theorem Yulang.GeneralDepthTwoMachine300.remaining_decreases (a b : Phase) (step : (boundary roles).Step registry root (raw a) (raw b)) :
    remaining b < remaining a
```

```lean
theorem Yulang.GeneralDepthTwoMachine300.source_accessible :
    Acc (fun next prev => (boundary roles).Step registry root prev next) initial
```


## lean/Yulang/GeneralDepthTwoMiddleContext300.lean

```lean
theorem Yulang.GeneralDepthTwoMiddleContext300.real_context : plan.packet.context = env
```

```lean
theorem Yulang.GeneralDepthTwoMiddleContext300.same_base : env.state.base = snapshot.base
```

```lean
theorem Yulang.GeneralDepthTwoMiddleContext300.seed_exact : env.state.seed = snapshot.seed
```

```lean
theorem Yulang.GeneralDepthTwoMiddleContext300.prior_updates (m : Assignment) (held : Models after m) :
    PresenceNormalForm.All CommonNominalFullCarrier.model m updates
```

```lean
theorem Yulang.GeneralDepthTwoMiddleContext300.holds (m : Assignment) (held : Models after m) : Holds plan m
```

```lean
theorem Yulang.GeneralDepthTwoMiddleContext300.same_children : children plan.packet = [terminal]
```

```lean
theorem Yulang.GeneralDepthTwoMiddleContext300.middle_raw_site : GeneralNominalDemandMerging.pointSite middle = child.observed
```

```lean
theorem Yulang.GeneralDepthTwoMiddleContext300.after_raw_sites : after.core.erased.current.sites =
    [GeneralNominalDemandMerging.pointSite root,child.observed]
```

```lean
theorem Yulang.GeneralDepthTwoMiddleContext300.after_center_sites : after.core.sites = [GeneralDepthTwoRootPlan300.plan.input,child]
```

```lean
theorem Yulang.GeneralDepthTwoMiddleContext300.source_support (n : Nat) (hit : n ∈ sources env.state) : n ≤ 2 ∨ n ∈ res
```

```lean
theorem Yulang.GeneralDepthTwoMiddleContext300.fresh (bs) : GeneralNominalVersionedAllocation231.Fresh env.state compiled middle.identity bs
```


## lean/Yulang/GeneralDepthTwoMiddleFrame300.lean

```lean
theorem Yulang.GeneralDepthTwoMiddleFrame300.after_model : Models after model := (models model).mpr initial_model

theorem metadata : GeneralNominalRecursiveCandidates.Metadata compiled env
```

```lean
theorem Yulang.GeneralDepthTwoMiddleFrame300.located : GeneralNominalRecursiveCandidates.arguments env (inputs middle) = some [((1 : Fin 3),(1 : Fin 3))]
```

```lean
theorem Yulang.GeneralDepthTwoMiddleFrame300.middle_role : middle.demand.role = 0
```

```lean
theorem Yulang.GeneralDepthTwoMiddleFrame300.input_bounds : ∀ i, (inputs middle).demand.arguments i = (1,1)
```

```lean
theorem Yulang.GeneralDepthTwoMiddleFrame300.known : ¬ GeneralNominalState.RootPending env.state (inputs middle).demand
```

```lean
theorem Yulang.GeneralDepthTwoMiddleFrame300.linked : GeneralNominalState.Linked env.state (inputs middle).demand
```

```lean
theorem Yulang.GeneralDepthTwoMiddleFrame300.prepared : Prepared compiled env middle display
```

```lean
theorem Yulang.GeneralDepthTwoMiddleFrame300.wrong_failed : Failed compiled env middle intDisplay
```

```lean
theorem Yulang.GeneralDepthTwoMiddleFrame300.wrong_not_prepared : ¬ Prepared compiled env middle intDisplay
```

```lean
theorem Yulang.GeneralDepthTwoMiddleFrame300.outputs_empty : middle.demand.outputs = []
```

```lean
theorem Yulang.GeneralDepthTwoMiddleFrame300.inputs_eq_when_blank (o : GeneralSourceDictionaries.Occurrence roles) (empty : o.demand.outputs = []) :
    inputs o = o
```

```lean
theorem Yulang.GeneralDepthTwoMiddleFrame300.point_inputs : GeneralNominalDemandMerging.pointSite (inputs middle) =
    GeneralNominalDemandMerging.pointSite middle
```

```lean
theorem Yulang.GeneralDepthTwoMiddleFrame300.frame : GeneralNominalVersionedEvidence231.Frame compiled after.core middle 1 plan
```

```lean
theorem Yulang.GeneralDepthTwoMiddleFrame300.survivor : Survivor compiled env middle 1 [terminal]
```

```lean
theorem Yulang.GeneralDepthTwoMiddleFrame300.unique : Unique compiled env middle 1 [terminal]
```

```lean
theorem Yulang.GeneralDepthTwoMiddleFrame300.ready : GeneralNominalCenteredHeadMatEffects.Ready after.core middle plan
```


## lean/Yulang/GeneralDepthTwoMiddlePlan300.lean

```lean
theorem Yulang.GeneralDepthTwoMiddlePlan300.bindings : middlePacket.bindings = [(0,(2,2))]
```

```lean
theorem Yulang.GeneralDepthTwoMiddlePlan300.center : binder plan 0 = 2
```

```lean
theorem Yulang.GeneralDepthTwoMiddlePlan300.captured : (capture middlePacket).inputs 0 = (2,2)
```

```lean
theorem Yulang.GeneralDepthTwoMiddlePlan300.head_schema : plan.headSchema =
    ⟨[⟨0,origin,.actual⟩],[(.source 1,.nominal 0 1)],false⟩
```

```lean
theorem Yulang.GeneralDepthTwoMiddlePlan300.emitted_schema : emittedSchema plan =
    ⟨[⟨2,.lower,.variable 0⟩,⟨2,.upper,.variable 0⟩],false⟩
```

```lean
theorem Yulang.GeneralDepthTwoMiddlePlan300.emitted_sites : GeneralNominalVersionedChildren232.emitted plan = [child]
```

```lean
theorem Yulang.GeneralDepthTwoMiddlePlan300.child_args : ∀ i, child.occurrence.demand.arguments i = (2,2)
```

```lean
theorem Yulang.GeneralDepthTwoMiddlePlan300.child_data : child.occurrence = terminal ∧
    ∀ i, child.center i = 2
```

```lean
theorem Yulang.GeneralDepthTwoMiddlePlan300.child_schema : childSchema plan GeneralDeclarationExamples.displayChild
    (display_checked.signature.2.2.2 _ (by simp)) = ⟨[⟨2,.actual,.variable 0⟩],false⟩
```

```lean
theorem Yulang.GeneralDepthTwoMiddlePlan300.var_actual (m : Assignment) : variables plan m .actual 0 = (m 2).1
```

```lean
theorem Yulang.GeneralDepthTwoMiddlePlan300.var_bounds (m : Assignment) :
    variables plan m .lower 0 = (m 2).1 ∧ variables plan m .upper 0 = (m 2).1
```

```lean
theorem Yulang.GeneralDepthTwoMiddlePlan300.update_support (m : Assignment) (valid : GeneralNominalState.Models snapshot m) :
    Ordinary middlePacket m ∧ ProjectionModels snapshot (GeneralNominalPacketSupport.report middlePacket) m
```

```lean
theorem Yulang.GeneralDepthTwoMiddlePlan300.input_holds (m : Assignment) : plan.input.Holds m
```

```lean
theorem Yulang.GeneralDepthTwoMiddlePlan300.holds (m : Assignment) (valid : GeneralNominalState.Models snapshot m) : Holds plan m
```


## lean/Yulang/GeneralDepthTwoObserved300.lean

```lean
theorem Yulang.GeneralDepthTwoObserved300.roundtrip (n : Node) (i : Nat) (ok : encode n = some i) :
    decode i = demand n
```

```lean
theorem Yulang.GeneralDepthTwoObserved300.observed (i : Nat) (f : Frontier Node) (hit : lookup i = some f) :
    Local (boundary roles) registry final (decode i) (translate demand f)
```

```lean
theorem Yulang.GeneralDepthTwoObserved300.faithful : Faithful (b:=boundary roles) (r:=registry) (s:=final) table decode
```

```lean
theorem Yulang.GeneralDepthTwoObserved300.entries (i : Nat) (e : Entry) (hit : table i = some e) :
    (i = 0 ∧ e = ⟨1,[1]⟩) ∨ (i = 1 ∧ e = ⟨1,[2]⟩) ∨ (i = 2 ∧ e = ⟨3,[]⟩)
```

```lean
theorem Yulang.GeneralDepthTwoObserved300.known : GeneralGeneratedDictionaryRankCheck299.Known table [0,1,2]
```

```lean
theorem Yulang.GeneralDepthTwoObserved300.closed : Closed table
```

```lean
theorem Yulang.GeneralDepthTwoObserved300.nodes : Nodes (boundary roles) registry final table decode
```

```lean
theorem Yulang.GeneralDepthTwoObserved300.computed : run table 3 0 = some (.node 1 [.node 1 [.node 3 []]])
```

```lean
theorem Yulang.GeneralDepthTwoObserved300.exact_on_actual (i : Nat) (e : Entry) (hit : table i = some e) (d : Dictionary) :
    run table 3 i = some d ↔ Classify (boundary roles) registry final (decode i) (.selected d)
```

```lean
theorem Yulang.GeneralDepthTwoObserved300.real_terminal_graph : Acc (Child (Local (boundary roles) registry final)) root
```

```lean
theorem Yulang.GeneralDepthTwoObserved300.readback (m : Assignment) (valid : Models final m) :
    (boundary roles).Evidence registry final m root (.node 1 [.node 1 [.node 3 []]])
```


## lean/Yulang/GeneralDepthTwoOnlyFirst300.lean

```lean
theorem Yulang.GeneralDepthTwoOnlyFirst300.phase_frame {p : GeneralNominalCenters.Plan roles} {key}
    (held : Frame compiled initial.core root key p) : p = plan
```

```lean
theorem Yulang.GeneralDepthTwoOnlyFirst300.only_effect (candidate : Effect roles) (enabled : Installable compiled initial candidate)
    (here : candidate.plan.packet.site.occurrence = root) : candidate = effect
```

```lean
theorem Yulang.GeneralDepthTwoOnlyFirst300.generated_initial {d : Occurrence roles}
    (given : GeneralNominalSaturationState.Generated initial.core.erased.current root d) : d = root
```

```lean
theorem Yulang.GeneralDepthTwoOnlyFirst300.only_step (next : State roles) (given : Step compiled root initial next) : next = after
```

```lean
theorem Yulang.GeneralDepthTwoOnlyFirst300.exact_first (next : State roles) :
    (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Step registry root initial next ↔ next = after
```


## lean/Yulang/GeneralDepthTwoOnlySecond300.lean

```lean
theorem Yulang.GeneralDepthTwoOnlySecond300.after_scope (d : Occurrence roles) (known : Generated after.core.erased.current root d) :
    d = root ∨ d = middle
```

```lean
theorem Yulang.GeneralDepthTwoOnlySecond300.recorded (d : Occurrence roles) (scope : d = root ∨ d = middle) :
    ∃ site ∈ after.core.erased.current.sites, site.occurrence = d
```

```lean
theorem Yulang.GeneralDepthTwoOnlySecond300.wrong_root : ¬ Prepared compiled env root intDisplay
```

```lean
theorem Yulang.GeneralDepthTwoOnlySecond300.root_frame {p : GeneralNominalCenters.Plan roles} {key}
    (frame : Frame compiled after.core root key p) : p = oldRoot
```

```lean
theorem Yulang.GeneralDepthTwoOnlySecond300.only_step (next : State roles) (given : Step compiled root after next) : next = final
```

```lean
theorem Yulang.GeneralDepthTwoOnlySecond300.exact_second (next : State roles) :
    (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Step registry root after next ↔ next = final
```


## lean/Yulang/GeneralDepthTwoPhaseCut300.lean

```lean
theorem Yulang.GeneralDepthTwoPhaseCut300.after_edges : after.core.erased.current.edges = [(root,middle)]
```

```lean
theorem Yulang.GeneralDepthTwoPhaseCut300.different_phases : initial ≠ after ∧ after ≠ final ∧ initial ≠ final
```

```lean
theorem Yulang.GeneralDepthTwoPhaseCut300.no_refresh_in_place (ctx : GeneralNominalCandidates.Context) :
    GeneralNominalVersionedRefresh232.refresh initial ctx ≠ after ∧
      GeneralNominalVersionedRefresh232.refresh after ctx ≠ final
```

```lean
theorem Yulang.GeneralDepthTwoPhaseCut300.after_terminal_frame_absent (p : GeneralNominalCenters.Plan roles) (k : Nat) :
    ¬ Frame compiled after.core terminal k p
```

```lean
theorem Yulang.GeneralDepthTwoPhaseCut300.no_terminal_evidence (m : Assignment) (d : Payload) :
    ¬ (boundary roles).Evidence registry after m terminal d
```

```lean
theorem Yulang.GeneralDepthTwoPhaseCut300.no_middle_evidence (m : Assignment) (d : Payload) :
    ¬ (boundary roles).Evidence registry after m middle d
```

```lean
theorem Yulang.GeneralDepthTwoPhaseCut300.second_closes_evidence :
    (boundary roles).Step registry root after final ∧
      (∀ m d, ¬ (boundary roles).Evidence registry after m middle d) ∧
      ∀ m, Models after m →
        Models final m ∧
        (boundary roles).Evidence registry final m root (.node 1 [.node 1 [.node 3 []]])
```


## lean/Yulang/GeneralDepthTwoRootAvailability300.lean

```lean
theorem Yulang.GeneralDepthTwoRootAvailability300.initial_middle_absent (m : Assignment) (d : Payload) :
    ¬ (boundary roles).Evidence registry initial m middle d
```

```lean
theorem Yulang.GeneralDepthTwoRootAvailability300.initial_root_absent (m : Assignment) (d : Payload) :
    ¬ (boundary roles).Evidence registry initial m root d
```

```lean
theorem Yulang.GeneralDepthTwoRootAvailability300.after_root_absent (m : Assignment) (d : Payload) :
    ¬ (boundary roles).Evidence registry after m root d
```

```lean
theorem Yulang.GeneralDepthTwoRootAvailability300.exact_availability (p : Phase) (m : Assignment) (valid : Models (raw p) m) :
    (∃ d, (boundary roles).Evidence registry (raw p) m root d) ↔ p = .done
```


## lean/Yulang/GeneralDepthTwoRootFrame300.lean

```lean
theorem Yulang.GeneralDepthTwoRootFrame300.metadata : GeneralNominalRecursiveCandidates.Metadata compiled context
```

```lean
theorem Yulang.GeneralDepthTwoRootFrame300.root_known : ¬ GeneralNominalState.RootPending snapshot (inputs root).demand
```

```lean
theorem Yulang.GeneralDepthTwoRootFrame300.root_fresh (bs) : GeneralNominalVersionedAllocation231.Fresh snapshot compiled root.identity bs
```

```lean
theorem Yulang.GeneralDepthTwoRootFrame300.root_located : GeneralNominalRecursiveCandidates.arguments context (inputs root) = some [(0,0)]
```

```lean
theorem Yulang.GeneralDepthTwoRootFrame300.prepared : Prepared compiled context root display
```

```lean
theorem Yulang.GeneralDepthTwoRootFrame300.wrong_failed : Failed compiled context root intDisplay
```

```lean
theorem Yulang.GeneralDepthTwoRootFrame300.wrong_not_prepared : ¬ Prepared compiled context root intDisplay
```

```lean
theorem Yulang.GeneralDepthTwoRootFrame300.frame : GeneralNominalVersionedEvidence231.Frame compiled initial.core root 1 plan
```

```lean
theorem Yulang.GeneralDepthTwoRootFrame300.survivor : Survivor compiled context root 1 [middle]
```

```lean
theorem Yulang.GeneralDepthTwoRootFrame300.unique : Unique compiled context root 1 [middle]
```

```lean
theorem Yulang.GeneralDepthTwoRootFrame300.initial_requests (focus : Occurrence roles) :
    GeneralNominalCenteredHeadOutputs.requests initial.core focus = []
```

```lean
theorem Yulang.GeneralDepthTwoRootFrame300.ready : GeneralNominalCenteredHeadMatEffects.Ready initial.core root plan
```


## lean/Yulang/GeneralDepthTwoRootPlan300.lean

```lean
theorem Yulang.GeneralDepthTwoRootPlan300.bindings : parentPacket.bindings = [(0,(1,1))]
```

```lean
theorem Yulang.GeneralDepthTwoRootPlan300.center : binder plan 0 = 1
```

```lean
theorem Yulang.GeneralDepthTwoRootPlan300.captured : (capture parentPacket).inputs 0 = (1,1)
```

```lean
theorem Yulang.GeneralDepthTwoRootPlan300.head_schema : plan.headSchema =
    ⟨[⟨0,origin,.actual⟩],[(.source 0,.nominal 0 1)],false⟩
```

```lean
theorem Yulang.GeneralDepthTwoRootPlan300.emitted_schema : emittedSchema plan =
    ⟨[⟨1,.lower,.variable 0⟩,⟨1,.upper,.variable 0⟩],false⟩
```

```lean
theorem Yulang.GeneralDepthTwoRootPlan300.emitted_sites : GeneralNominalVersionedChildren232.emitted plan = [child]
```

```lean
theorem Yulang.GeneralDepthTwoRootPlan300.child_args : ∀ i, child.occurrence.demand.arguments i = (1,1)
```

```lean
theorem Yulang.GeneralDepthTwoRootPlan300.child_data : child.occurrence = middle ∧
    ∀ i, child.center i = 1
```

```lean
theorem Yulang.GeneralDepthTwoRootPlan300.child_schema : childSchema plan GeneralDeclarationExamples.displayChild
    (display_checked.signature.2.2.2 _ (by simp)) = ⟨[⟨1,.actual,.variable 0⟩],false⟩
```

```lean
theorem Yulang.GeneralDepthTwoRootPlan300.var_actual (m : Assignment) : variables plan m .actual 0 = (m 1).1
```

```lean
theorem Yulang.GeneralDepthTwoRootPlan300.var_bounds (m : Assignment) :
    variables plan m .lower 0 = (m 1).1 ∧ variables plan m .upper 0 = (m 1).1
```

```lean
theorem Yulang.GeneralDepthTwoRootPlan300.update_support (m : Assignment) (valid : GeneralNominalState.Models snapshot m) :
    Ordinary parentPacket m ∧ ProjectionModels snapshot (GeneralNominalPacketSupport.report parentPacket) m
```

```lean
theorem Yulang.GeneralDepthTwoRootPlan300.holds (m : Assignment) (valid : GeneralNominalState.Models snapshot m) : Holds plan m
```


## lean/Yulang/GeneralDepthTwoSafety300.lean

```lean
theorem Yulang.GeneralDepthTwoSafety300.towers (id : Nat) : ∃ n, (model id).1 = tower n
```

```lean
theorem Yulang.GeneralDepthTwoSafety300.semantic {s : State roles} (valid : Models s model) (origin) :
    ¬ GeneralNominalVersionedCycles232.Cyclic s origin
```

```lean
theorem Yulang.GeneralDepthTwoSafety300.depth_exact (s : GeneralNominalState.State) (slot : Fin s.base.slots) :
    (model (s.base.source slot)).1 = tower (depth s slot)
```

```lean
theorem Yulang.GeneralDepthTwoSafety300.raw_edge (s : GeneralNominalState.State) (noShapes : s.view.kinds = 0)
    (valid : GeneralNominalState.Models s model)
    {a b : Fin s.base.slots} (edge : GeneralNominalMixedRecurrence.Edge s a b) :
    depth s b < depth s a
```

```lean
theorem Yulang.GeneralDepthTwoSafety300.raw_acyclic (s : GeneralNominalState.State) (noShapes : s.view.kinds = 0)
    (valid : GeneralNominalState.Models s model) (i : Fin s.base.slots) :
    ¬ GeneralNominalCycleK2.RecursAt s i
```


## lean/Yulang/GeneralDepthTwoSecondInstall300.lean

```lean
theorem Yulang.GeneralDepthTwoSecondInstall300.root_observed : rootSite.observed.inputs = [some (.source 0)]
```

```lean
theorem Yulang.GeneralDepthTwoSecondInstall300.middle_observed : middleSite.observed.inputs = [some (.source 1)]
```

```lean
theorem Yulang.GeneralDepthTwoSecondInstall300.middle_site : middleSite.occurrence = middle := GeneralDepthTwoRootPlan300.child_data.1

theorem administrative : GeneralNominalVersionedDiagnostic232.AdministrativeReady after middle
```

```lean
theorem Yulang.GeneralDepthTwoSecondInstall300.safe : B4TargetV8.SafeKnown (GeneralNominalVersionedDiagnostic232.boundary roles)
    compiled after middle
```

```lean
theorem Yulang.GeneralDepthTwoSecondInstall300.positions : GeneralNominalVersionedCycles232.Safe after plan
```

```lean
theorem Yulang.GeneralDepthTwoSecondInstall300.frame_unique {p : GeneralNominalCenters.Plan roles} {key}
    (given : Frame compiled after.core middle key p) : p = plan
```

```lean
theorem Yulang.GeneralDepthTwoSecondInstall300.alternatives : AlternativesSafe compiled after plan.input
```

```lean
theorem Yulang.GeneralDepthTwoSecondInstall300.emitted_sites : GeneralNominalVersionedChildren232.emitted plan = [leafSite]
```

```lean
theorem Yulang.GeneralDepthTwoSecondInstall300.terminal_site : leafSite.occurrence = terminal
```

```lean
theorem Yulang.GeneralDepthTwoSecondInstall300.final_requests (focus : Occurrence roles) :
    GeneralNominalCenteredHeadOutputs.requests final.core focus = []
```

```lean
theorem Yulang.GeneralDepthTwoSecondInstall300.installation (m : Assignment) (valid : Models after m) :
    InstallationModels after effect m
```

```lean
theorem Yulang.GeneralDepthTwoSecondInstall300.enabled : Installable compiled after effect
```

```lean
theorem Yulang.GeneralDepthTwoSecondInstall300.actual : (boundary roles).Step registry root after final
```

```lean
theorem Yulang.GeneralDepthTwoSecondInstall300.actual_terminal :
    Steps ((boundary roles).Step registry root) initial final ∧
      B4TargetV8.Reachable (boundary roles) registry root final ∧
      GeneralNominalSaturationState.Generated final.core.erased.current root terminal
```

```lean
theorem Yulang.GeneralDepthTwoSecondInstall300.models (m : Assignment) : Models final m ↔ Models after m
```


## lean/Yulang/GeneralDepthTwoTerminalFrame300.lean

```lean
theorem Yulang.GeneralDepthTwoTerminalFrame300.final_model : Models final model
```

```lean
theorem Yulang.GeneralDepthTwoTerminalFrame300.no_alias_terminal_root : terminal.identity ≠ root.identity
```

```lean
theorem Yulang.GeneralDepthTwoTerminalFrame300.source_support (i : Nat) (hit : i ∈ sources env.state) :
    i ≤ 2 ∨ i ∈ res1 ∨ i ∈ res2
```

```lean
theorem Yulang.GeneralDepthTwoTerminalFrame300.terminal_fresh (bs) : GeneralNominalVersionedAllocation231.Fresh env.state compiled terminal.identity bs
```

```lean
theorem Yulang.GeneralDepthTwoTerminalFrame300.located : GeneralNominalRecursiveCandidates.arguments env (inputs terminal) =
    some [((2 : Fin 3),(2 : Fin 3))]
```

```lean
theorem Yulang.GeneralDepthTwoTerminalFrame300.terminal_role : terminal.demand.role = 0
```

```lean
theorem Yulang.GeneralDepthTwoTerminalFrame300.point_bounds : ∀ i, (inputs terminal).demand.arguments i = (2,2)
```

```lean
theorem Yulang.GeneralDepthTwoTerminalFrame300.linked : GeneralNominalState.Linked env.state (inputs terminal).demand
```

```lean
theorem Yulang.GeneralDepthTwoTerminalFrame300.prepared : Prepared compiled env terminal intDisplay
```

```lean
theorem Yulang.GeneralDepthTwoTerminalFrame300.raw_sites : final.core.erased.current.sites =
    [GeneralNominalDemandMerging.pointSite root,GeneralDepthTwoRootPlan300.child.observed,leafSite.observed]
```

```lean
theorem Yulang.GeneralDepthTwoTerminalFrame300.center_sites : final.core.sites =
    [GeneralDepthTwoRootPlan300.plan.input,GeneralDepthTwoRootPlan300.child,leafSite]
```

```lean
theorem Yulang.GeneralDepthTwoTerminalFrame300.frame : Frame compiled final.core terminal 3 plan
```


## lean/Yulang/GeneralDepthTwoTerminalPlan300.lean

```lean
theorem Yulang.GeneralDepthTwoTerminalPlan300.leaf_exact : leafSite = GeneralDepthTwoMiddlePlan300.child
```

```lean
theorem Yulang.GeneralDepthTwoTerminalPlan300.leaf_center : ∀ i, leafSite.center i = 2
```

```lean
theorem Yulang.GeneralDepthTwoTerminalPlan300.leaf_args : ∀ i, leafSite.occurrence.demand.arguments i = (2,2)
```

```lean
theorem Yulang.GeneralDepthTwoTerminalPlan300.leaf_input (m : Assignment) : leafSite.Holds m
```

```lean
theorem Yulang.GeneralDepthTwoTerminalPlan300.query : GeneralNominalInspection.queries env.state env.interpretation intDisplay = [.scalar .int]
```

```lean
theorem Yulang.GeneralDepthTwoTerminalPlan300.report_exact : GeneralNominalPacketSupport.report packet =
    { inspected := [((2 : Fin 3),(2 : Fin 3))],
      checked := [((2 : Fin 3),(2 : Fin 3)),((2 : Fin 3),(2 : Fin 3))] }
```

```lean
theorem Yulang.GeneralDepthTwoTerminalPlan300.bindings_empty : packet.bindings = []
```

```lean
theorem Yulang.GeneralDepthTwoTerminalPlan300.children_empty : GeneralNominalVersionedFrame231.children packet = []
```

```lean
theorem Yulang.GeneralDepthTwoTerminalPlan300.schema_empty : emittedSchema plan = ⟨[],false⟩
```

```lean
theorem Yulang.GeneralDepthTwoTerminalPlan300.ordinary (m : Assignment) : Ordinary packet m
```

```lean
theorem Yulang.GeneralDepthTwoTerminalPlan300.head_schema : plan.headSchema = ⟨[],[(.source 2,.scalar .int)],false⟩
```

```lean
theorem Yulang.GeneralDepthTwoTerminalPlan300.holds (m : Assignment) (valid : Models final m) : Holds plan m
```

Indexed 265 theorem declarations. Each has one standalone audit.
