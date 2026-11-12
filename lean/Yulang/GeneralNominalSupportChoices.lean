import Yulang.GeneralNominalSupport

/-! Retain every finite support alternative at installation. The resulting
ledger is independent of the particular witness supplied to the transition.
Unused producer identities can be erased without changing a semantic slice. -/
namespace Yulang.GeneralNominalSupportChoices
open GeneralNominalSupport GeneralSourceDictionaries GeneralNominalSaturationState

abbrev PacketGuard (state : Tracked roles) (packet : Packet roles) (support : List (Occurrence roles)) :=
  Guard {state with current := {state.current with context := packet.context}}
    packet.site.occurrence packet.declaration packet.bounds support ∧
  DecisionGuard {state with current := {state.current with context := packet.context}}
    packet.registry packet.site.occurrence support

def subsets : List α → List (List α)
  | [] => [[]]
  | head :: tail => subsets tail ++ (subsets tail).map (head :: ·)

theorem filter_subset (list : List α) (test : α → Bool) : list.filter test ∈ subsets list := by
  induction list with
  | nil => simp [subsets]
  | cons head tail ih =>
    by_cases yes : test head = true
    · simp only [List.filter_cons,yes,ite_true,subsets]
      exact List.mem_append_right _ (List.mem_map.mpr ⟨_,ih,rfl⟩)
    · simp only [List.filter_cons,yes,subsets]
      exact List.mem_append_left _ ih

def dependencyPool (state : Tracked roles) : List (Occurrence roles) := state.facts.flatMap Fact.dependencies

noncomputable def restrict (state : Tracked roles) (support : List (Occurrence roles)) : List (Occurrence roles) := by
  classical
  exact (dependencyPool state).filter (fun producer => decide (producer ∈ support))

theorem restrict_mem (state : Tracked roles) (support : List (Occurrence roles)) (producer : Occurrence roles) :
    producer ∈ restrict state support ↔ producer ∈ dependencyPool state ∧ producer ∈ support := by
  classical
  simp [restrict]

theorem slice_restrict (state : Tracked roles) (support : List (Occurrence roles))
    (model : GeneralNominalCommonBridge.Assignment) : Slice state (restrict state support) model ↔ Slice state support model := by
  constructor
  · intro valid
    refine ⟨valid.1,?_⟩
    intro fact member included
    apply valid.2 fact member
    intro producer dependency
    exact (restrict_mem state support producer).mpr
      ⟨List.mem_flatMap.mpr ⟨fact,member,dependency⟩,included producer dependency⟩
  · intro valid
    refine ⟨valid.1,?_⟩
    intro fact member included
    exact valid.2 fact member (fun producer dependency =>
      ((restrict_mem state support producer).mp (included producer dependency)).2)

theorem ready_restrict (state : Tracked roles) (support : List (Occurrence roles)) (identity : Nat)
    (ready : ReadyAt state support identity) : ReadyAt state (restrict state support) identity := by
  obtain ⟨test,observation,head,snapshot,witness,recorded,entailed⟩ := ready
  exact ⟨test,observation,head,snapshot,witness,recorded,fun model valid =>
    entailed model ((slice_restrict state support model).mp valid)⟩

theorem guard_restrict (state : Tracked roles) (root : Occurrence roles) (declaration : GeneralDeclarations.Declaration)
    (bounds : List (GeneralNominalInspection.Bounds state.current.context.state)) (support : List (Occurrence roles))
    (guard : Guard state root declaration bounds support) : Guard state root declaration bounds (restrict state support) := by
  refine ⟨fun producer member => guard.1 producer ((restrict_mem state support producer).mp member).2,
    fun index => ready_restrict state support _ (guard.2.1 index),?_⟩
  intro slot member
  exact ready_restrict state support _ (guard.2.2 slot member)

theorem decision_restrict (state : Tracked roles) (registry : GeneralDeclarations.Registry) (root : Occurrence roles)
    (support : List (Occurrence roles)) (guard : DecisionGuard state registry root support) :
    DecisionGuard state registry root (restrict state support) := by
  refine ⟨fun producer member => guard.1 producer ((restrict_mem state support producer).mp member).2,
    fun index => ready_restrict state support _ (guard.2.1 index),?_⟩
  intro declaration visible role bounds located slot member
  exact ready_restrict state support _ (guard.2.2 declaration visible role bounds located slot member)

noncomputable def alternatives (state : Tracked roles) (packet : Packet roles) : List (List (Occurrence roles)) := by
  classical
  exact (subsets (dependencyPool state)).filter (fun support => decide (PacketGuard state packet support))

theorem alternative_guard (member : support ∈ alternatives state packet) : PacketGuard state packet support := by
  classical
  exact of_decide_eq_true (List.mem_filter.mp member).2

theorem alternatives_exists (state : Tracked roles) (packet : Packet roles) (support : List (Occurrence roles))
    (guard : PacketGuard state packet support) : ∃ selected, selected ∈ alternatives state packet := by
  classical
  refine ⟨restrict state support,List.mem_filter.mpr ⟨filter_subset _ _,?_⟩⟩
  exact decide_eq_true ⟨guard_restrict _ _ _ _ _ guard.1,decision_restrict _ _ _ _ guard.2⟩

noncomputable def installedFacts (state : Tracked roles) (packet : Packet roles) : List (Fact roles) :=
  (alternatives state packet).flatMap fun support => [.inputs packet support,.outputs packet support]

theorem facts_exact (state : Tracked roles) (packet : Packet roles) (support : List (Occurrence roles))
    (guard : PacketGuard state packet support) (model : GeneralNominalCommonBridge.Assignment) :
    (∀ fact ∈ installedFacts state packet, fact.Holds model) ↔
      GeneralNominalPacketSupport.Inputs packet model ∧ GeneralNominalPacketSupport.Outputs packet model := by
  constructor
  · intro valid
    obtain ⟨chosen,member⟩ := alternatives_exists state packet support guard
    exact ⟨valid (.inputs packet chosen) (List.mem_flatMap.mpr ⟨chosen,member,by simp⟩),
      valid (.outputs packet chosen) (List.mem_flatMap.mpr ⟨chosen,member,by simp⟩)⟩
  · rintro ⟨inputs,outputs⟩ fact member
    obtain ⟨chosen,_,member⟩ := List.mem_flatMap.mp member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact inputs
    · exact outputs

theorem empty_alternatives (state : Tracked roles) (packet : Packet roles) (empty : state.facts = [])
    (guard : PacketGuard state packet []) : installedFacts state packet = [.inputs packet [],.outputs packet []] := by
  classical
  have pool : dependencyPool state = [] := by simp [dependencyPool,empty]
  simp only [installedFacts,alternatives,pool,subsets,List.filter_cons,decide_eq_true guard,
    ite_true,List.filter_nil,List.flatMap_cons,List.flatMap_nil,List.append_nil]

def RecoverySupported (state : Tracked roles) (site : GeneralNominalDemandMerging.Site roles)
    (support : List (Occurrence roles)) : Prop :=
  ∀ index : Fin (roles site.occurrence.demand.role).arity, site.inputs[index.val]? = some none →
    ∀ model, Slice state support model →
      CommonNominalFullCarrier.Equivalent (model (site.occurrence.demand.arguments index).1).1
        (model (site.occurrence.demand.arguments index).2).1

abbrev MergeGuard (state : Tracked roles) (first last : GeneralNominalDemandMerging.Site roles)
    (support : List (Occurrence roles)) :=
  GeneralNominalDemandMerging.SameInputs (Slice state support)
    (GeneralNominalFeedbackSites.recover state.current first) (GeneralNominalFeedbackSites.recover state.current last) ∧
      RecoverySupported state first support ∧ RecoverySupported state last support

noncomputable def mergeAlternatives (state : Tracked roles) (first last : GeneralNominalDemandMerging.Site roles) :
    List (List (Occurrence roles)) := by
  classical
  exact (subsets (dependencyPool state)).filter (fun support => decide (MergeGuard state first last support))

theorem merge_alternatives_exists (state : Tracked roles) (first last : GeneralNominalDemandMerging.Site roles)
    (support : List (Occurrence roles)) (guard : MergeGuard state first last support) :
    ∃ selected, selected ∈ mergeAlternatives state first last := by
  classical
  refine ⟨restrict state support,List.mem_filter.mpr ⟨filter_subset _ _,?_⟩⟩
  apply decide_eq_true
  have same : Slice state (restrict state support) = Slice state support :=
    funext (fun model => propext (slice_restrict state support model))
  refine ⟨?_,?_,?_⟩
  · change GeneralNominalDemandMerging.SameInputs (Slice state (restrict state support)) _ _
    rw [same]
    exact guard.1
  · intro index absent model valid
    exact guard.2.1 index absent model ((slice_restrict state support model).mp valid)
  · intro index absent model valid
    exact guard.2.2 index absent model ((slice_restrict state support model).mp valid)

noncomputable def mergedFacts (state : Tracked roles) (first last : GeneralNominalDemandMerging.Site roles) : List (Fact roles) :=
  (mergeAlternatives state first last).map (Fact.merge first last)

theorem merged_facts_exact (state : Tracked roles) (first last : GeneralNominalDemandMerging.Site roles)
    (support : List (Occurrence roles)) (guard : MergeGuard state first last support)
    (model : GeneralNominalCommonBridge.Assignment) :
    (∀ fact ∈ mergedFacts state first last, fact.Holds model) ↔
      PresenceNormalForm.All CommonNominalFullCarrier.model model (GeneralNominalDemandMerging.outputAtoms first last) := by
  constructor
  · intro valid
    obtain ⟨chosen,member⟩ := merge_alternatives_exists state first last support guard
    exact valid (.merge first last chosen) (List.mem_map.mpr ⟨chosen,member,rfl⟩)
  · intro valid fact member
    obtain ⟨chosen,_,rfl⟩ := List.mem_map.mp member
    exact valid

end Yulang.GeneralNominalSupportChoices
