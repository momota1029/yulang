import Yulang.GeneralDictionaryFeedbackEvidence

/-! I-25: the draft's Sigma embeds as a real InitialSource with empty journal.
No model, successful classification, or termination premise is hidden here. -/
namespace Yulang.GeneralDictionaryInitialSource
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
variable {roles : Roles.RoleDecls}

def Initial (registry : Registry) (root : Occurrence roles) (state : State roles) : Prop :=
  ∃ context, GeneralNominalSourceFormation.InitialSource registry context root ∧
    state = initial context root

theorem initial_empty (registry : Registry) (root : Occurrence roles) (state : State roles)
    (given : Initial registry root state) :
    state.packets = [] ∧ state.edges = [] ∧ state.aliases = [] := by
  obtain ⟨context,_,rfl⟩ := given
  exact ⟨rfl,rfl,rfl⟩

theorem initial_formed (registry : Registry) (root : Occurrence roles) (state : State roles)
    (given : Initial registry root state) :
    GeneralNominalFeedbackSteps.SourceFormed registry root state := by
  obtain ⟨context,source,rfl⟩ := given
  exact .initial context source

/-- Reordering preserves InitialSource, including its registry metadata. -/
theorem source_reorders (registry other : Registry)
    (order : GeneralRegistryReordering.Reorders registry other)
    (context : GeneralNominalCandidates.Context) (root : Occurrence roles)
    (source : GeneralNominalSourceFormation.InitialSource registry context root) :
    GeneralNominalSourceFormation.InitialSource other context root := by
  refine ⟨order.2.1.symm.trans source.roles_agree,?_,source.linked,
    source.intervals,source.below_seed,source.unallocated⟩
  exact ⟨order.1.symm.trans source.metadata.1,order.1 ▸ source.metadata.2⟩

theorem initial_reorders (registry other : Registry)
    (order : GeneralRegistryReordering.Reorders registry other)
    (root : Occurrence roles) (state : State roles) (given : Initial registry root state) :
    Initial other root state := by
  obtain ⟨context,source,same⟩ := given
  exact ⟨context,source_reorders registry other order context root source,same⟩

/-- All actual feedback steps are admitted; no fixed-view restriction. -/
theorem formed_iff_initial_trace (registry : Registry) (root : Occurrence roles) (state : State roles) :
    GeneralNominalFeedbackSteps.SourceFormed registry root state ↔
      ∃ start, Initial registry root start ∧
        B4Target.Steps (GeneralNominalFeedbackSteps.Step registry root) start state := by
  constructor
  · intro formed
    induction formed with
    | initial context source => exact ⟨_,⟨context,source,rfl⟩,.refl⟩
    | update _ step ih =>
      obtain ⟨start,initial,path⟩ := ih
      exact ⟨start,initial,.tail path step⟩
  · rintro ⟨start,initial,path⟩
    induction path with
    | refl => exact initial_formed registry root start initial
    | tail _ step ih => exact .update ih step
end Yulang.GeneralDictionaryInitialSource
