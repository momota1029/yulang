import Yulang.GeneralNominalViewRefresh196
import Yulang.GeneralNominalVariableView196
import Yulang.GeneralNominalRefreshFork

set_option backward.isDefEq.respectTransparency false
/-! A descriptor insertion whose exactness follows from the actual source alias
constraints, lifted to the unchanged WF head-step relation. Not an Initial or
Reachable proof, and not a claim that an arbitrary registry has evidence. -/
namespace Yulang.GeneralNominalExecutableView196
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalViewTransport196
open GeneralNominalCenteredHeadStepEffects (Models)
open GeneralNominalCenteredHeadStepKernel (refresh)
open GeneralNominalRefreshFork (context state root)

abbrev start := GeneralNominalCenteredHeadStepEffects.initial (context none) root

def next (wide : Bool) : View (state none) :=
  ⟨(state (some wide)).view,(state (some wide)).nominals,
    (state (some wide)).catalogue,(state (some wide)).bodies_opaque⟩

theorem replaced (wide : Bool) : GeneralNominalViewTransport196.context (context none) (next wide) =
    context (some wide) := rfl

abbrev finish (wide : Bool) := refresh start (context (some wide))

noncomputable def certificate (wide : Bool) : GeneralNominalCenteredSteps.Refresh start.core
    (context (some wide)) where
  refines := GeneralNominalRefreshFork.refinement wide
  interpretation := rfl
  exact := fun model valid => GeneralNominalRefreshFork.refresh_models_forward wide model valid.1.1
  support := fun _ member => member

theorem actual_step (registry : Registry) (wide : Bool) :
    (GeneralNominalCenteredHeadWFBoundary.boundary GeneralDeclarationExamples.roles).Step
      registry root start (finish wide) := by
  refine ⟨root,.root,.refresh root (context (some wide)) (certificate wide) 0 ?_ ?_ ?_⟩
  · change 0 ∈ GeneralNominalState.sources (state none)
    simp only [GeneralNominalState.sources,List.mem_append,List.mem_ofFn]
    exact Or.inl (Or.inl (Or.inl ⟨⟨0,by decide +kernel⟩,rfl⟩))
  · exact fun known => GeneralNominalRefreshFork.initial_pending.choose_spec known
  · exact GeneralNominalRefreshFork.zero_known wide

theorem same_models (wide : Bool) (model : GeneralNominalCommonBridge.Assignment) :
    Models (finish wide) model ↔ Models start model :=
  GeneralNominalCenteredHeadStepKernel.refresh_models (certificate wide) model

theorem inhabited (wide : Bool) : Models start GeneralNominalRefreshFork.model ∧
    Models (finish wide) GeneralNominalRefreshFork.model := by
  have valid : Models start GeneralNominalRefreshFork.model := by
    apply GeneralNominalCenteredHeadStepEffects.initial_models.mpr
    apply (GeneralNominalCenteredSteps.point_initial_models (context none) root
      (by intro index; rfl) _).mpr
    exact GeneralNominalRefreshFork.initial_models.1
  exact ⟨valid,(same_models wide _).mpr valid⟩

theorem descriptor_changed (wide : Bool) :
    start.core.erased.current.context.state.nominals ⟨0,by change 0 < 5; decide⟩ = none ∧
    (finish wide).core.erased.current.context.state.nominals ⟨0,by change 0 < 5; decide⟩ =
      some (GeneralNominalRefreshFork.descriptor (2,if wide then 4 else 2)) := ⟨rfl,rfl⟩

/-- No registry-wide report-equality premise: the syntactic variable query
restriction suffices, including after this executable descriptor-changing step. -/
theorem preserve_variable_evidence (registry : Registry) (wide : Bool)
    (shape : ∀ declaration ∈ registry.declarations, ∃ names : List (List Nat),
      GeneralNominalInspection.queries (state none) (context none).interpretation declaration =
        names.map GeneralNominalInspection.Query.variables)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models start model)
    (focus : Occurrence GeneralDeclarationExamples.roles) (payload : GeneralDictionaryReadback.Payload)
    (evidence : (GeneralNominalCenteredHeadWFBoundary.boundary GeneralDeclarationExamples.roles).Evidence
      registry start model focus payload) :
    (GeneralNominalCenteredHeadWFBoundary.boundary GeneralDeclarationExamples.roles).Evidence
      registry (finish wide) model focus payload := by
  have rechecked := GeneralNominalVariableView196.rechecks_variables registry (context none) (next wide) shape
  have transported := GeneralNominalViewRefresh196.evidence_refresh (state := start) rechecked model
    ((same_models wide model).mpr valid) focus payload evidence
  exact transported
end Yulang.GeneralNominalExecutableView196
