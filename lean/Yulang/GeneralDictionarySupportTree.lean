import Yulang.GeneralDictionarySupportEvidence

/-! Finite classified dictionaries at one actual reachable support snapshot.
Joint is required only when this snapshot has a model, and only for its
selected generated occurrences.
No global EvidenceNode, executor totality, or unconditioned V5 claim is made. -/
namespace Yulang.GeneralDictionarySupportTree
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalSupportBoundary
open GeneralDictionaryRecursiveEvidence (Evidence)
open GeneralDictionarySupportEvidence
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (Dictionary All₂)
variable {roles : Roles.RoleDecls}

private theorem selected_inv {v : B4Target.Vocabulary} (b : B4Target.SourceBoundary v)
    (r : v.Registry) (s : v.State) (focus : v.Demand) (key : Nat) (dictionaries : List Dictionary)
    (classified : B4TargetV3.Classify b r s focus (.selected (.node key dictionaries))) :
    ∃ children, B4Target.SafeKnown b r s focus ∧ B4Target.Unique b r s focus key children ∧
      All₂ (fun child dictionary => B4TargetV3.Classify b r s child (.selected dictionary)) children dictionaries := by
  cases classified with
  | selected safe unique all => exact ⟨_,safe,unique,all⟩

mutual
 theorem classified_evidence (registry : Registry) (state : Tracked roles) (root : Occurrence roles)
    (reachable : B4TargetV5.Reachable (boundary roles) registry root state)
    (stable : GeneralNominalSupportSteps.Stable registry state root)
    (joint : (∃ model, Models state.current model) →
      ∀ focus, Generated state.current root focus → ∀ key children,
      Local registry state focus (.selected key children) →
      GeneralNominalJointCandidates.Joint registry state.current focus key)
    (model : Assignment) (valid : Models state.current model)
    (dictionary : Dictionary) (focus : Occurrence roles)
    (reached : Generated state.current root focus)
    (classified : B4TargetV3.Classify (boundary roles).toSourceBoundary registry state focus (.selected dictionary)) :
    Evidence registry state.current.context model focus dictionary := by
  cases dictionary with
  | node key dictionaries =>
    obtain ⟨children,safe,unique,classifiedChildren⟩ := selected_inv _ _ _ _ _ _ classified
    have localRule : Local registry state focus (.selected key children) :=
      (local_correspondence registry state focus _).mp (.selected safe unique)
    have stableFocus : GeneralNominalSupportSteps.Stable registry state focus :=
      fun target generated => stable target (generated_trans reached generated)
    have applicable := joint ⟨model,valid⟩ focus reached key children localRule
    have edges := (reachable_joint_instance registry state root focus reachable key children
      stableFocus localRule applicable).2
    exact reachable_joint_evidence registry state root focus reachable key children
      stableFocus localRule applicable model valid dictionaries
      (classified_children_evidence registry state root reachable stable joint model valid dictionaries children
        (fun child member => generated_trans reached (edges child member)) classifiedChildren)
 termination_by sizeOf dictionary

 theorem classified_children_evidence (registry : Registry) (state : Tracked roles) (root : Occurrence roles)
    (reachable : B4TargetV5.Reachable (boundary roles) registry root state)
    (stable : GeneralNominalSupportSteps.Stable registry state root)
    (joint : (∃ model, Models state.current model) →
      ∀ focus, Generated state.current root focus → ∀ key children,
      Local registry state focus (.selected key children) →
      GeneralNominalJointCandidates.Joint registry state.current focus key)
    (model : Assignment) (valid : Models state.current model)
    (dictionaries : List Dictionary) (children : List (Occurrence roles))
    (reached : ∀ child ∈ children, Generated state.current root child)
    (classified : All₂ (fun child dictionary => B4TargetV3.Classify (boundary roles).toSourceBoundary
      registry state child (.selected dictionary)) children dictionaries) :
    All₂ (Evidence registry state.current.context model) children dictionaries := by
  cases classified with
  | nil => exact .nil
  | cons first rest =>
    exact .cons
      (classified_evidence registry state root reachable stable joint model valid _ _
        (reached _ (List.mem_cons_self)) first)
      (classified_children_evidence registry state root reachable stable joint model valid _ _
        (fun child member => reached child (List.mem_cons_of_mem _ member)) rest)
 termination_by sizeOf dictionaries
end

/-- Snapshot-scoped dictionary soundness for the real boundary Evidence field. -/
theorem snapshot_dictionary_sound (registry : Registry) (state : Tracked roles) (root : Occurrence roles)
    (reachable : B4TargetV5.Reachable (boundary roles) registry root state)
    (stable : GeneralNominalSupportSteps.Stable registry state root)
    (joint : (∃ model, Models state.current model) →
      ∀ focus, Generated state.current root focus → ∀ key children,
      Local registry state focus (.selected key children) →
      GeneralNominalJointCandidates.Joint registry state.current focus key)
    (dictionary : Dictionary)
    (classified : B4TargetV3.Classify (boundary roles).toSourceBoundary registry state root (.selected dictionary)) :
    ∀ model, (boundary roles).Models state model →
      (boundary roles).Evidence registry state model root dictionary :=
  fun model valid => classified_evidence registry state root reachable stable joint model valid dictionary root .root classified

/-- Empty reachable journals eliminate the Joint residual entirely. -/
theorem packetFree_dictionary_sound (registry : Registry) (state : Tracked roles) (root : Occurrence roles)
    (reachable : B4TargetV5.Reachable (boundary roles) registry root state)
    (empty : state.current.packets = [])
    (stable : GeneralNominalSupportSteps.Stable registry state root)
    (dictionary : Dictionary)
    (classified : B4TargetV3.Classify (boundary roles).toSourceBoundary registry state root (.selected dictionary)) :
    ∀ model, (boundary roles).Models state model →
      (boundary roles).Evidence registry state model root dictionary := by
  apply snapshot_dictionary_sound registry state root reachable stable _ dictionary classified
  intro _ focus reached key children selected
  exact reachable_packetFree_joint registry root focus state reachable empty (Or.inr reached) key children selected

/-- A completed selected dictionary in the packet-free case is a single node. -/
theorem packetFree_classified_terminal (registry : Registry) (state : Tracked roles) (root : Occurrence roles)
    (reachable : B4TargetV5.Reachable (boundary roles) registry root state)
    (empty : state.current.packets = [])
    (stable : GeneralNominalSupportSteps.Stable registry state root)
    (dictionary : Dictionary)
    (classified : B4TargetV3.Classify (boundary roles).toSourceBoundary registry state root (.selected dictionary)) :
    ∃ key, dictionary = .node key [] ∧ ∀ model, Models state.current model →
      Evidence registry state.current.context model root (.node key []) := by
  cases dictionary with
  | node key dictionaries =>
    obtain ⟨children,safe,unique,all⟩ := selected_inv _ _ _ _ _ _ classified
    have selected : Local registry state root (.selected key children) :=
      (local_correspondence registry state root _).mp (.selected safe unique)
    have terminal := reachable_packetFree_terminal registry root root state reachable empty (Or.inl rfl)
      key children stable selected
    rw [terminal.1] at all
    cases all
    exact ⟨key,rfl,terminal.2⟩

end Yulang.GeneralDictionarySupportTree
