import Yulang.GeneralDictionarySupportTree

/-! Successful finite classification from local where-closure alone.
Neither execution, stability, semantic Joint nor Evidence is used to construct
the dictionary. The operational hypotheses enter only its semantic soundness. -/
namespace Yulang.GeneralDictionaryLocalReadback
open CommonRoleOutermostResolver

inductive Reach (localRule : Request → Frontier Request → Prop) (root : Request) : Request → Prop
  | root : Reach localRule root root
  | child : Reach localRule root parent → Child localRule child parent → Reach localRule root child

private theorem list_witnesses (children : List Request) (P : Request → Dictionary → Prop)
    (existsEach : ∀ child ∈ children, ∃ dictionary, P child dictionary) :
    ∃ dictionaries, All₂ P children dictionaries := by
  induction children with
  | nil => exact ⟨[],.nil⟩
  | cons child rest ih =>
    obtain ⟨first,valid⟩ := existsEach child (List.mem_cons_self)
    obtain ⟨remaining,all⟩ := ih (fun child member => existsEach child (List.mem_cons_of_mem _ member))
    exact ⟨first :: remaining,.cons valid all⟩

/-- Quantified over any B4 source boundary. Only successful local decisions on
the independent selected-child closure are required, not all generated nodes. -/
theorem classified_exists {v : B4Target.Vocabulary} (b : B4Target.SourceBoundary v)
    (registry : v.Registry) (state : v.State) (root : v.Demand)
    (selected : ∀ focus, Reach (B4TargetV3.Local b registry state) root focus →
      ∃ key children, B4TargetV3.Local b registry state focus (.selected key children))
    (accessible : Acc (Child (B4TargetV3.Local b registry state)) root) :
    ∃ dictionary, B4TargetV3.Classify b registry state root (.selected dictionary) := by
  have construct : ∀ focus, Acc (Child (B4TargetV3.Local b registry state)) focus →
      Reach (B4TargetV3.Local b registry state) root focus →
      ∃ dictionary, B4TargetV3.Classify b registry state focus (.selected dictionary) := by
    intro focus accessible
    induction accessible with
    | intro focus below ih =>
      intro reached
      obtain ⟨key,children,rule⟩ := selected focus reached
      obtain ⟨dictionaries,all⟩ := list_witnesses children
        (fun child dictionary => B4TargetV3.Classify b registry state child (.selected dictionary))
        (fun child member => ih child ⟨key,children,rule,member⟩
          (.child reached ⟨key,children,rule,member⟩))
      cases rule with
      | selected safe unique => exact ⟨.node key dictionaries,.selected safe unique all⟩
  exact construct root accessible .root

/-- Specialization to the actual support boundary. Readback only needs selected
where-closure; source reachability, stability and explicit Joint give semantic
soundness afterwards. There is no assumption of a completed output. -/
theorem support_dictionary {roles : Roles.RoleDecls} (registry : GeneralDeclarations.Registry)
    (state : GeneralNominalSupport.Tracked roles) (root : GeneralSourceDictionaries.Occurrence roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root state)
    (stable : GeneralNominalSupportSteps.Stable registry state root)
    (selected : ∀ focus,
      Reach (B4TargetV3.Local (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary registry state) root focus →
      ∃ key children, GeneralNominalSupportBoundary.Local registry state focus (.selected key children))
    (joint : (∃ model, GeneralNominalSaturationState.Models state.current model) →
      ∀ focus, GeneralNominalSaturationState.Generated state.current root focus → ∀ key children,
      GeneralNominalSupportBoundary.Local registry state focus (.selected key children) →
      GeneralNominalJointCandidates.Joint registry state.current focus key)
    (accessible : Acc (Child (B4TargetV3.Local
      (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary registry state)) root) :
    ∃ dictionary, B4TargetV3.Classify (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary
        registry state root (.selected dictionary) ∧
      ∀ model, GeneralNominalSaturationState.Models state.current model →
        GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context model root dictionary := by
  have localSelected : ∀ focus,
      Reach (B4TargetV3.Local (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary registry state) root focus →
      ∃ key children, B4TargetV3.Local (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary
        registry state focus (.selected key children) := by
    intro focus reached
    obtain ⟨key,children,rule⟩ := selected focus reached
    exact ⟨key,children,(GeneralNominalSupportBoundary.local_correspondence registry state focus _).mpr rule⟩
  obtain ⟨dictionary,classified⟩ := classified_exists (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary registry state root localSelected accessible
  exact ⟨dictionary,classified,GeneralDictionarySupportTree.snapshot_dictionary_sound
    registry state root reachable stable joint dictionary classified⟩
end Yulang.GeneralDictionaryLocalReadback
