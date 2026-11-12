import Yulang.GeneralDictionaryReachableEvidenceRecorded
import Yulang.GeneralDictionaryOrdinaryTransport

/-! Actual equality feedback cannot destroy Joint. Unlike a general constraint
extension, both endpoints already occur and the added equality holds in every
journal model. The common witness for all aliases is preserved. -/
namespace Yulang.GeneralDictionaryJointEquality
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalFeedbackSteps GeneralNominalJointCandidates
open GeneralNominalRecursiveCandidates

variable {roles : Roles.RoleDecls}

theorem sources_equate (state : State roles) (first last source : Nat)
    (one : first ∈ GeneralNominalState.sources state.context.state)
    (two : last ∈ GeneralNominalState.sources state.context.state) :
    source ∈ GeneralNominalState.sources (equate state first last).context.state ↔
      source ∈ GeneralNominalState.sources state.context.state := by
  simp only [equate,GeneralNominalState.extend,GeneralNominalState.sources,
    List.flatMap_append,List.mem_append] at *
  simp only [GeneralNominalAllocation.equations,GeneralNominalState.atomSources,
    List.flatMap_cons,List.flatMap_nil,List.mem_cons,List.not_mem_nil,List.mem_append,GeneralNominalState.typeSources]
  constructor
  · intro h
    rcases h with ((h | h) | h | (h | h) | (h | h) | h)
    · exact Or.inl (Or.inl h)
    · rcases h with h | h
      · exact Or.inl (Or.inr h)
      · cases h
    · exact Or.inr h
    · rcases h with rfl | h
      · exact one
      · cases h
    · rcases h with rfl | h
      · exact two
      · cases h
    · rcases h with rfl | h
      · exact two
      · cases h
    · rcases h with rfl | h
      · exact one
      · cases h
    · cases h
  · rintro ((h | h) | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr (Or.inl h))
    · exact Or.inr (Or.inl h)

theorem equate_context (state : State roles) (first last : Nat) :
    (equate state first last).context = GeneralDictionaryOrdinaryTransport.extend state.context []
      (GeneralNominalAllocation.equations first (.var last)) [] := by
  cases state with | mk context packets aliases sites edges =>
    cases context with | mk state interpretation =>
      cases state
      simp [equate,GeneralNominalState.extend,GeneralDictionaryOrdinaryTransport.extend,
        GeneralDictionaryOrdinaryTransport.extendState]

theorem branch_equate_forward (registry : Registry) (state : State roles)
    (root : Occurrence roles) (key first last : Nat)
    (one : first ∈ GeneralNominalState.sources state.context.state)
    (two : last ∈ GeneralNominalState.sources state.context.state)
    (equal : GeneralNominalFeedbackK2.Equal state first last)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model)
    (given : BranchAt registry state root key model) :
    BranchAt registry (equate state first last) root key model := by
  obtain ⟨d,visible,checked,identity,role,prepared,bounds,located,branch⟩ := given
  obtain ⟨metadata,linked,fresh,old,found,finished,ready,consistent⟩ := prepared
  have same := Option.some.inj (located.symm.trans found)
  subst old
  have extended := (GeneralDictionaryOrdinaryTransport.branch_extended_iff [] []
    (GeneralNominalAllocation.equations first (.var last)) state.context registry root d checked bounds model).mpr
      ⟨branch,(GeneralNominalCaptureMerges.equations_exact model first (.var last)).mpr (equal model valid)⟩
  have newbranch : BranchModels registry (equate state first last).context root d checked bounds model := by
    have transport : ∀ bs, arguments (equate state first last).context root = some bs →
        BranchModels registry (equate state first last).context root d checked bs model := by
      rw [equate_context]
      intro bs hb
      have hb' : arguments state.context root = some bs := hb
      have same := Option.some.inj (located.symm.trans hb')
      subst bs
      exact extended
    exact transport bounds located
  refine ⟨d,visible,checked,identity,role,?_,bounds,located,newbranch⟩
  refine ⟨metadata,?_,?_,bounds,located,?_,?_,model,newbranch⟩
  · constructor
    · intro i; exact ⟨(sources_equate state first last _ one two).mpr (linked.1 i).1,
        (sources_equate state first last _ one two).mpr (linked.1 i).2⟩
    · intro output member
      exact (sources_equate state first last _ one two).mpr (linked.2 output member)
  · intro origin member collision
    exact fresh origin member ((sources_equate state first last _ one two).mp collision)
  · have transport : ∀ bs, arguments (equate state first last).context root = some bs →
        GeneralNominalRecursiveInspection.Finished (report (equate state first last).context d bs) := by
      rw [equate_context]
      intro bs hb
      have hb' : arguments state.context root = some bs := hb
      have same := Option.some.inj (located.symm.trans hb')
      subst bs
      simpa only [GeneralDictionaryOrdinaryTransport.candidate_report_extended, GeneralDictionaryOrdinaryTransport.finished_report] using finished
    exact transport bounds located
  · have transport : ∀ bs, arguments (equate state first last).context root = some bs →
        RequestReady registry (equate state first last).context root d checked bs := by
      rw [equate_context]
      intro bs hb
      have hb' : arguments state.context root = some bs := hb
      have same := Option.some.inj (located.symm.trans hb')
      subst bs
      simpa only [RequestReady,GeneralDictionaryOrdinaryTransport.generated_extended] using ready
    exact transport bounds located

/-- Alias reachability depends only on the alias-edge list, not the context. -/
theorem alias_same {before after : State roles} (same : before.aliases = after.aliases)
    {first last : Nat} (given : Alias before first last) : Alias after first last := by
  induction given with
  | refl x => exact .refl x
  | edge h => exact .edge (same ▸ h)
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

/-- The actual equality-feedback operation preserves the common model for all
related sites. No exact-occurrence alias restriction is imposed. -/
theorem joint_equate (registry : Registry) (state : State roles)
    (root : Occurrence roles) (key first last : Nat)
    (one : first ∈ GeneralNominalState.sources state.context.state)
    (two : last ∈ GeneralNominalState.sources state.context.state)
    (equal : GeneralNominalFeedbackK2.Equal state first last)
    (given : Joint registry state root key) :
    Joint registry (equate state first last) root key := by
  obtain ⟨packets, model, valid, branch, related⟩ := given
  refine ⟨?_,model,(equate_models state first last equal model).mpr valid,
    branch_equate_forward registry state root key first last one two equal model valid branch,?_⟩
  · intro packet member alias
    exact packets packet member (alias_same (before := equate state first last) (after := state) rfl alias)
  · intro site rel
    apply branch_equate_forward registry state site.occurrence key first last one two equal model valid
    exact related site ⟨rel.1,alias_same (before := equate state first last) (after := state) rfl rel.2⟩


end Yulang.GeneralDictionaryJointEquality
