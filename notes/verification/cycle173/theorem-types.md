# Cycle173 public declaration type index

量化子と前提は以下の Lean 宣言に保持する。各モジュールの implicit parameters / namespace は元ファイルを参照。SelectedPackets・Remaining は未証明の条件であり、ground 初期状態制限を省略しない。


## GeneralDictionaryActualEdge173.lean

暗黙の変数宣言:
```lean
variable {roles : Roles.RoleDecls} {registry : Registry} {state : Tracked roles}
variable {parent child : Occurrence roles} {key : Nat} {children : List (Occurrence roles)}
```

```lean
theorem selected_child_schema
    (selected : GeneralNominalActualBoundary.Local registry state parent (.selected key children))
    (member : child ∈ children) :
    ∃ packet : Packet roles, ∃ clause : Clause, ∃ signature : clause.Signature roles,
      packet.registry = registry ∧ packet.context = state.current.context ∧
      packet.site.occurrence = parent ∧ packet.declaration.id = key ∧
      child = clauseChild packet clause signature ∧
      clause ∈ packet.declaration.requirements ∧
      ∀ capture : Nat → Pattern,
        mass (substArgs capture clause.arguments) < mass (substArgs capture packet.declaration.head)
```


## GeneralDictionaryActualExample173.lean

暗黙の変数宣言:
```lean

```

```lean
theorem display_not_stable :
    ¬ GeneralNominalActualBoundary.Stable registry start displayRoot
```

```lean
theorem actual_inhabited_child :
    GeneralNominalActualInspectionSteps.Step registry displayRoot start after ∧
    ∃ model, Models after.current model ∧ Generated after.current displayRoot displayChild
```

```lean
theorem current_instance (model : GeneralNominalCommonBridge.Assignment)
    (valid : Models after.current model) :
    Instance registry after.current.context model displayRoot
      GeneralDeclarationExamples.display.id (packet false).children
```

```lean
theorem current_node (model : GeneralNominalCommonBridge.Assignment)
    (valid : Models after.current model) (dictionaries : List GeneralDictionaryReadback.Payload)
    (children : CommonRoleOutermostResolver.All₂
      (Evidence registry after.current.context model) (packet false).children dictionaries) :
    Evidence registry after.current.context model displayRoot
      (.node GeneralDeclarationExamples.display.id dictionaries)
```


## GeneralDictionaryActualGroundComposition173.lean

暗黙の変数宣言:
```lean
variable {roles : Roles.RoleDecls}
```

```lean
theorem initial_reorders (registry other : Registry)
    (order : (groundBoundary roles).Reorders registry other) (state : Tracked roles) (root : Occurrence roles)
    (given : (groundBoundary roles).Initial registry root state) :
    (groundBoundary roles).Initial other root state
```

```lean
structure Remaining (roles : Roles.RoleDecls) : Prop where
  packets : SelectedPackets roles
  whereAccessible : ∀ registry, (groundBoundary roles).Checked registry → ∀ state root,
    Reachable (groundBoundary roles) registry root state →
      Acc (Child (B4TargetV3.Local (groundBoundary roles).toSourceBoundary registry state)) root
  canonicalLocalOrder : ∀ registry other, (groundBoundary roles).Checked registry →
    (groundBoundary roles).Checked other → (groundBoundary roles).Reorders registry other → ∀ state root,
    Reachable (groundBoundary roles) registry root state → Reachable (groundBoundary roles) other root state →
    ∀ focus frontier,
      B4TargetV3.Local (groundBoundary roles).toSourceBoundary registry
        ((executor roles).run registry state root).1 focus frontier ↔
      B4TargetV3.Local (groundBoundary roles).toSourceBoundary other
        ((executor roles).run other state root).1 focus frontier
```

```lean
theorem bridges (roles : Roles.RoleDecls) (rest : Remaining roles) :
    B4SkeletonV5.B4Bridges (groundBoundary roles) (executor roles) (frontiers roles) where
  progress
```

```lean
theorem statement (roles : Roles.RoleDecls) (rest : Remaining roles) :
    B4TargetV5.Statement (groundBoundary roles) (executor roles)
```


## GeneralDictionaryActualGroundExample173.lean

暗黙の変数宣言:
```lean

```

```lean
abbrev roles
```

```lean
abbrev start
```

```lean
noncomputable def final
```

```lean
theorem source_initial : (groundBoundary roles).Initial registry root start
```

```lean
theorem actual_run :
    B4Target.Steps (Step registry root) start final ∧
    (∀ next, ¬ Step registry root final next) ∧
    Stable registry final root ∧
    (∀ child, Generated final.current root child → Stable registry final child) ∧
    ∀ model, Models final.current model → Models start.current model
```


## GeneralDictionaryActualGroundExecutor173.lean

暗黙の変数宣言:
```lean

```

```lean
noncomputable def finalState (roles : Roles.RoleDecls)
    (registry : Registry) (state : Tracked roles) (root : Occurrence roles) : Tracked roles
```

```lean
theorem final_spec (roles : Roles.RoleDecls)
    (registry : Registry) (checked : (groundBoundary roles).Checked registry)
    (state : Tracked roles) (root : Occurrence roles)
    (reachable : Reachable (groundBoundary roles) registry root state) :
    B4Target.Steps ((groundBoundary roles).Step registry root) state (finalState roles registry state root) ∧
      ∀ next, ¬ (groundBoundary roles).Step registry root (finalState roles registry state root) next
```

```lean
noncomputable def diagnostic (roles : Roles.RoleDecls) (registry : Registry)
    (state : Tracked roles) (root : Occurrence roles) : Tree
```

```lean
theorem diagnostic_eq_resolve (roles : Roles.RoleDecls) (registry : Registry)
    (state : Tracked roles) (root : Occurrence roles)
    (exact : FrontierExact (frontiers roles registry state))
    (accessible : Acc (Child (frontiers roles registry state).Local) root) :
    diagnostic roles registry state root = resolve (frontiers roles registry state) exact root accessible
```

```lean
noncomputable def executor (roles : Roles.RoleDecls) :
    Executor (GeneralNominalActualBoundary.vocabulary roles) where
  run registry state root
```

```lean
theorem execution (roles : Roles.RoleDecls) :
    ∀ r, (groundBoundary roles).Checked r → ∀ s d, Reachable (groundBoundary roles) r d s →
      B4Target.Steps ((groundBoundary roles).Step r d) s ((executor roles).run r s d).1
```

```lean
theorem halted (roles : Roles.RoleDecls) :
    ∀ r, (groundBoundary roles).Checked r → ∀ s d, Reachable (groundBoundary roles) r d s →
      ∀ next, ¬ (groundBoundary roles).Step r d ((executor roles).run r s d).1 next
```

```lean
theorem treeExecution (roles : Roles.RoleDecls) :
    ∀ r (_checked : (groundBoundary roles).Checked r) s d, Reachable (groundBoundary roles) r d s →
      ∀ (exact : FrontierExact (frontiers roles r ((executor roles).run r s d).1))
      (accessible : Acc (Child (frontiers roles r ((executor roles).run r s d).1).Local) d),
      ((executor roles).run r s d).2 =
        resolve (frontiers roles r ((executor roles).run r s d).1) exact d accessible
```

```lean
theorem final_reachable (roles : Roles.RoleDecls)
    (registry : Registry) (checked : (groundBoundary roles).Checked registry)
    (state : Tracked roles) (root : Occurrence roles)
    (reachable : Reachable (groundBoundary roles) registry root state) :
    Reachable (groundBoundary roles) registry root ((executor roles).run registry state root).1
```

```lean
theorem final_stable (roles : Roles.RoleDecls)
    (registry : Registry) (checked : (groundBoundary roles).Checked registry)
    (state : Tracked roles) (root : Occurrence roles)
    (reachable : Reachable (groundBoundary roles) registry root state) :
    (groundBoundary roles).Stable registry ((executor roles).run registry state root).1 root ∧
      ∀ child, (groundBoundary roles).Generated registry ((executor roles).run registry state root).1 root child →
        (groundBoundary roles).Stable registry ((executor roles).run registry state root).1 child
```

```lean
theorem final_models (roles : Roles.RoleDecls)
    (registry : Registry) (checked : (groundBoundary roles).Checked registry)
    (state : Tracked roles) (root : Occurrence roles)
    (reachable : Reachable (groundBoundary roles) registry root state) :
    ∀ model, (groundBoundary roles).Models ((executor roles).run registry state root).1 model →
      (groundBoundary roles).Models state model
```

```lean
theorem saturationTotal (roles : Roles.RoleDecls) :
    B4TargetV5.SaturationTotal (groundBoundary roles) (executor roles)
```


## GeneralDictionaryActualRecorded173.lean

暗黙の変数宣言:
```lean
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}
```

```lean
theorem recorded_metadata {state : Tracked roles}
    (formed : SourceFormed registry root state) (packet : Packet roles)
    (member : packet ∈ state.current.packets) :
    GeneralDictionarySharedRecordedEvidence.Metadata registry packet
```

```lean
theorem recorded_committed {state : Tracked roles}
    (formed : SourceFormed registry root state) (packet : Packet roles)
    (member : packet ∈ state.current.packets) :
    GeneralNominalFeedbackSteps.Committed state.current packet
```

```lean
theorem stored_instance {state : Tracked roles}
    (formed : SourceFormed registry root state) (packet : Packet roles)
    (member : packet ∈ state.current.packets) (model : Assignment)
    (valid : Models state.current model) :
    Instance registry packet.context model packet.site.occurrence packet.declaration.id packet.children
```

```lean
theorem recorded_children {state : Tracked roles}
    (formed : SourceFormed registry root state) (packet : Packet roles)
    (member : packet ∈ state.current.packets) :
    ∀ child ∈ packet.children, Generated state.current packet.site.occurrence child
```

```lean
theorem current_evidence {state : Tracked roles}
    (formed : SourceFormed registry root state) (packet : Packet roles)
    (member : packet ∈ state.current.packets)
    (extension : GeneralDictionaryOrdinaryTrace.Extension packet.context state.current.context)
    (model : Assignment) (valid : Models state.current model) (dictionaries : List Payload)
    (children : All₂ (Evidence registry state.current.context model) packet.children dictionaries) :
    Evidence registry state.current.context model packet.site.occurrence (.node packet.declaration.id dictionaries)
```


## GeneralDictionaryActualStable173.lean

暗黙の変数宣言:
```lean
variable {roles : Roles.RoleDecls} {registry : Registry} {state : Tracked roles}
```

```lean
theorem stable_committed (packet : Packet roles) (support : List (Occurrence roles))
    (stable : GeneralNominalActualBoundary.Stable registry state packet.site.occurrence)
    (enabled : GeneralNominalFeedbackSteps.Installable registry state.current packet)
    (guard : PacketGuard state packet support) :
    GeneralNominalFeedbackSteps.Committed state.current packet
```

```lean
theorem stable_site (root : Occurrence roles)
    (stable : GeneralNominalActualBoundary.Stable registry state root)
    (linked : GeneralNominalState.Linked state.current.context.state root.demand) :
    ∃ site ∈ state.current.sites, site.occurrence = root
```

```lean
theorem uncommitted_not_guarded (packet : Packet roles) (support : List (Occurrence roles))
    (stable : GeneralNominalActualBoundary.Stable registry state packet.site.occurrence)
    (enabled : GeneralNominalFeedbackSteps.Installable registry state.current packet)
    (novel : ¬ GeneralNominalFeedbackSteps.Committed state.current packet) :
    ¬ PacketGuard state packet support
```

```lean
theorem stable_instance (packet : Packet roles) (support : List (Occurrence roles))
    (stable : GeneralNominalActualBoundary.Stable registry state packet.site.occurrence)
    (enabled : GeneralNominalFeedbackSteps.Installable registry state.current packet)
    (guard : PacketGuard state packet support) (model : Assignment)
    (valid : Models state.current model) :
    Instance registry state.current.context model packet.site.occurrence packet.declaration.id packet.children
```

```lean
theorem stable_children (packet : Packet roles) (support : List (Occurrence roles))
    (stable : GeneralNominalActualBoundary.Stable registry state packet.site.occurrence)
    (enabled : GeneralNominalFeedbackSteps.Installable registry state.current packet)
    (guard : PacketGuard state packet support) :
    ∀ child ∈ packet.children, Generated state.current packet.site.occurrence child
```

```lean
theorem stable_evidence (packet : Packet roles) (support : List (Occurrence roles))
    (stable : GeneralNominalActualBoundary.Stable registry state packet.site.occurrence)
    (enabled : GeneralNominalFeedbackSteps.Installable registry state.current packet)
    (guard : PacketGuard state packet support) (model : Assignment)
    (valid : Models state.current model) (dictionaries : List Payload)
    (children : All₂ (Evidence registry state.current.context model) packet.children dictionaries) :
    Evidence registry state.current.context model packet.site.occurrence (.node packet.declaration.id dictionaries)
```

```lean
def SelectedPackets (roles : Roles.RoleDecls) : Prop
```

```lean
theorem evidenceNode (packets : SelectedPackets roles) :
    B4SkeletonV5.EvidenceNode (GeneralNominalActualBoundary.boundary roles)
```

```lean
theorem generatedChildren (packets : SelectedPackets roles) :
    B4SkeletonV5.GeneratedChildren (GeneralNominalActualBoundary.boundary roles)
```


## GeneralDictionaryActualV5173.lean

暗黙の変数宣言:
```lean
variable {roles : Roles.RoleDecls}
```

```lean
theorem ground_reachable
    (reachable : Reachable (groundBoundary roles) registry root state) :
    Reachable (boundary roles) registry root state
```

```lean
theorem phase_reachable
    (reachable : Reachable (GeneralNominalActualPhaseBoundary.boundary roles) registry root state) :
    Reachable (boundary roles) registry root state
```

```lean
theorem ground_evidenceNode (packets : SelectedPackets roles) :
    B4SkeletonV5.EvidenceNode (groundBoundary roles)
```

```lean
theorem ground_generatedChildren (packets : SelectedPackets roles) :
    B4SkeletonV5.GeneratedChildren (groundBoundary roles)
```

```lean
theorem phase_evidenceNode (packets : SelectedPackets roles) :
    B4SkeletonV5.EvidenceNode (GeneralNominalActualPhaseBoundary.boundary roles)
```

```lean
theorem phase_generatedChildren (packets : SelectedPackets roles) :
    B4SkeletonV5.GeneratedChildren (GeneralNominalActualPhaseBoundary.boundary roles)
```

```lean
theorem halted_classified_evidence (packets : SelectedPackets roles)
    (registry : Registry) (checked : (boundary roles).Checked registry)
    (state : Tracked roles) (root : Occurrence roles)
    (reachable : Reachable (boundary roles) registry root state)
    (halted : ∀ next, ¬ Step registry root state next)
    (model : GeneralNominalCommonBridge.Assignment) (valid : (boundary roles).Models state model)
    (dictionary : CommonRoleOutermostResolver.Dictionary)
    (classified : B4TargetV3.Classify (boundary roles).toSourceBoundary registry state root (.selected dictionary)) :
    (boundary roles).Evidence registry state model root dictionary
```

```lean
theorem ground_terminal_evidence (packets : SelectedPackets roles)
    (registry : Registry) (checked : (groundBoundary roles).Checked registry)
    (state : Tracked roles) (root : Occurrence roles)
    (reachable : Reachable (groundBoundary roles) registry root state) :
    ∃ final, B4Target.Steps (Step registry root) state final ∧
      (∀ next, ¬ Step registry root final next) ∧
      ∀ model, (groundBoundary roles).Models final model →
        ∀ dictionary, B4TargetV3.Classify (groundBoundary roles).toSourceBoundary registry final root (.selected dictionary) →
          (groundBoundary roles).Evidence registry final model root dictionary
```


## GeneralDictionary172CoverageSyntax.lean

暗黙の変数宣言:
```lean

```

```lean
def leafArguments : List Query → List Nat → Bool
  | [], [] => true
  | .variables actual :: queries, name :: names =>
      (actual == [name]) && leafArguments queries names
  | _, _ => false
```

```lean
theorem leafArguments_exact (queries : List Query) (names : List Nat) :
    leafArguments queries names = true ↔ queries = names.map (fun name => .variables [name])
```

```lean
def recognize (names : Fin n → Nat) (query : Query) : Bool
```

```lean
theorem recognize_nominal (names : Fin n → Nat) (tag : Nat) (children : List Query) :
    recognize names (.nominal tag children) =
      (if leafArguments children (List.ofFn names) then true
       else match children with | [child] => recognize names child | _ => false)
```

```lean
theorem recognize_sound (names : Fin n → Nat) (query : Query)
    (accepted : recognize names query = true) : Syntax names query
```

```lean
theorem recognize_complete (names : Fin n → Nat) (form : Syntax names query) :
    recognize names query = true
```

```lean
theorem recognize_exact (names : Fin n → Nat) (query : Query) :
    recognize names query = true ↔ Syntax names query
```

```lean
theorem recognize_false (names : Fin n → Nat) (query : Query) :
    recognize names query = false ↔ ¬ Syntax names query
```

```lean
theorem recognized_spine (state : GeneralNominalState.State) (names : Fin n → Nat)
    (accepted : recognize names query = true) (slot : Fin state.base.slots)
    (origin : Option GeneralNominalRecursiveInspection.Origin)
    (finished : GeneralNominalRecursiveInspection.Finished
      (GeneralNominalRecursiveInspection.inspect state query (slot,slot) origin))
    (points : GeneralDictionary171LocalInspectionObservation.PointInspection state
      (GeneralNominalRecursiveInspection.inspect state query (slot,slot) origin)) :
    ∃ bounds : Fin n → GeneralNominalInspection.Bounds state,
      ∃ spine : GeneralNominalSpineFacts.Spine state names bounds slot, spine.query = query
```

```lean
theorem nested_recognized : recognize (fun _ : Fin 1 => 7)
    GeneralDictionaryNestedRefinementExamples.query = true
```

```lean
theorem computed_nested :
    ∃ bounds : Fin 1 → GeneralNominalInspection.Bounds GeneralNominalProvenanceSource.state,
      ∃ spine : GeneralNominalSpineFacts.Spine GeneralNominalProvenanceSource.state (fun _ => 7) bounds 0,
        spine.query = GeneralDictionaryNestedRefinementExamples.query
```


Named declarations listed: 59. Generated constants are counted separately by namespace axiom gates.
