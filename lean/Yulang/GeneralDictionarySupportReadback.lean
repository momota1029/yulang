import Yulang.GeneralDictionarySupportTree

/-! Model-independent finite readback at an actual support snapshot.
Local selection, Joint and accessibility remain explicit premises. -/
namespace Yulang.GeneralDictionarySupportReadback
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalSupportBoundary
open CommonRoleOutermostResolver
variable {roles : Roles.RoleDecls}

private theorem selected_children (children : List (Occurrence roles))
    (P : Occurrence roles → Dictionary → Prop)
    (existsEach : ∀ child ∈ children, ∃ dictionary, P child dictionary) :
    ∃ dictionaries, All₂ P children dictionaries := by
  induction children with
  | nil => exact ⟨[],.nil⟩
  | cons child rest ih =>
    obtain ⟨first,valid⟩ := existsEach child (List.mem_cons_self)
    obtain ⟨remaining,all⟩ := ih (fun child member => existsEach child (List.mem_cons_of_mem _ member))
    exact ⟨first :: remaining,.cons valid all⟩

/-- Construct Classify rather than assuming a completed dictionary. -/
theorem classified_exists (registry : Registry) (state : Tracked roles) (root : Occurrence roles)
    (reachable : B4TargetV5.Reachable (boundary roles) registry root state)
    (stable : GeneralNominalSupportSteps.Stable registry state root)
    (selected : ∀ focus, Generated state.current root focus →
      ∃ key children, Local registry state focus (.selected key children))
    (joint : ∀ focus, Generated state.current root focus → ∀ key children,
      Local registry state focus (.selected key children) →
      GeneralNominalJointCandidates.Joint registry state.current focus key)
    (accessible : Acc (Child (B4TargetV3.Local (boundary roles).toSourceBoundary registry state)) root) :
    ∃ dictionary, B4TargetV3.Classify (boundary roles).toSourceBoundary registry state root (.selected dictionary) := by
  have construct : ∀ focus,
      Acc (Child (B4TargetV3.Local (boundary roles).toSourceBoundary registry state)) focus →
      Generated state.current root focus →
      ∃ dictionary, B4TargetV3.Classify (boundary roles).toSourceBoundary registry state focus (.selected dictionary) := by
    intro focus accessible
    induction accessible with
    | intro focus below ih =>
      intro reached
      obtain ⟨key,children,localRule⟩ := selected focus reached
      have localV3 := (local_correspondence registry state focus _).mpr localRule
      have stableFocus : GeneralNominalSupportSteps.Stable registry state focus :=
        fun target generated => stable target (generated_trans reached generated)
      have edges := (GeneralDictionarySupportEvidence.reachable_joint_instance registry state root focus
        reachable key children stableFocus localRule (joint focus reached key children localRule)).2
      obtain ⟨dictionaries,all⟩ := selected_children children
        (fun child dictionary => B4TargetV3.Classify (boundary roles).toSourceBoundary registry state child (.selected dictionary))
        (fun child member => ih child ⟨key,children,localV3,member⟩
          (generated_trans reached (edges child member)))
      cases localV3 with
      | selected safe unique => exact ⟨.node key dictionaries,.selected safe unique all⟩
  exact construct root accessible .root

/-- A single constructed payload is sound for all final journal models. -/
theorem uniform_dictionary (registry : Registry) (state : Tracked roles) (root : Occurrence roles)
    (reachable : B4TargetV5.Reachable (boundary roles) registry root state)
    (stable : GeneralNominalSupportSteps.Stable registry state root)
    (selected : ∀ focus, Generated state.current root focus →
      ∃ key children, Local registry state focus (.selected key children))
    (joint : ∀ focus, Generated state.current root focus → ∀ key children,
      Local registry state focus (.selected key children) →
      GeneralNominalJointCandidates.Joint registry state.current focus key)
    (accessible : Acc (Child (B4TargetV3.Local (boundary roles).toSourceBoundary registry state)) root) :
    ∃ dictionary, B4TargetV3.Classify (boundary roles).toSourceBoundary registry state root (.selected dictionary) ∧
      ∀ model, Models state.current model →
        GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context model root dictionary := by
  obtain ⟨dictionary,classified⟩ := classified_exists registry state root reachable stable selected joint accessible
  exact ⟨dictionary,classified,GeneralDictionarySupportTree.snapshot_dictionary_sound registry state root
    reachable stable (fun _ => joint) dictionary classified⟩
/-- The extraction premises are not discharged by an empty model class:
root selection and Joint supply a genuine final journal model. -/
theorem premises_inhabited (registry : Registry) (state : Tracked roles) (root : Occurrence roles)
    (selected : ∀ focus, Generated state.current root focus →
      ∃ key children, Local registry state focus (.selected key children))
    (joint : ∀ focus, Generated state.current root focus → ∀ key children,
      Local registry state focus (.selected key children) →
      GeneralNominalJointCandidates.Joint registry state.current focus key) :
    ∃ model, Models state.current model := by
  obtain ⟨key,children,localRule⟩ := selected root .root
  obtain ⟨model,valid,rest⟩ := (joint root .root key children localRule).2
  exact ⟨model,valid⟩

end Yulang.GeneralDictionarySupportReadback
