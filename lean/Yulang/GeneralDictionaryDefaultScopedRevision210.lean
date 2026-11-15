import Yulang.GeneralDictionaryDefaultRevisionEquivalence210

/-! The structural restriction need only cover declaration keys actually used
by the witness tree. Unrelated visible declarations may have nominal heads.
All descendants keep their original source occurrences and payload order. -/
namespace Yulang.GeneralDictionaryDefaultScopedRevision210
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal
variable {roles : Roles.RoleDecls} {state : State roles}

 def StructuralKey (registry : Registry) (context : GeneralNominalCandidates.Context) (key : Nat) : Prop :=
  ∀ declaration ∈ registry.declarations, declaration.id = key →
    ∀ query ∈ GeneralNominalInspection.queries context.state context.interpretation declaration,
      GeneralDictionaryDefaultStructuralReobserve210.Syntax query

inductive Shaped (registry : Registry) (context : GeneralNominalCandidates.Context) : Dictionary roles → Prop where
  | node (head : StructuralKey registry context key)
      (children : ∀ child ∈ trees, Shaped registry context child) :
      Shaped registry context (.node occurrence key trees)

 theorem key_iff (revision : GeneralNominalReobservationSteps.Revision state.core.erased.current) :
    StructuralKey registry (change state revision.result).core.erased.current.context key ↔
      StructuralKey registry state.core.erased.current.context key := Iff.rfl

 theorem shaped_forward (revision : GeneralNominalReobservationSteps.Revision state.core.erased.current)
    (shape : Shaped registry state.core.erased.current.context tree) :
    Shaped registry (change state revision.result).core.erased.current.context tree := by
  induction shape with
  | node head children ih => exact .node ((key_iff revision).mpr head) ih

 theorem local_instance
    (revision : GeneralNominalReobservationSteps.Revision state.core.erased.current)
    (shape : StructuralKey registry state.core.erased.current.context key)
    (valid : Models (change state revision.result) model)
    (old : GeneralDictionaryTotalEvidence206.Instance registry state.core model focus key children) :
    GeneralDictionaryTotalEvidence206.Instance registry (change state revision.result).core model focus key children := by
  obtain ⟨plan,source⟩ := old
  have shaped := shape plan.packet.declaration source.frame.visible source.frame.key_eq
  have queries : ∀ query ∈ GeneralNominalInspection.queries plan.packet.context.state
      plan.packet.context.interpretation plan.packet.declaration,
      GeneralDictionaryDefaultStructuralReobserve210.Syntax query := by
    simpa only [source.frame.context_eq] using shaped
  obtain ⟨witness,certificate,_⟩ := GeneralDictionaryDefaultRevisionEvidence210.certificate revision source queries valid
  exact ⟨witness,certificate⟩

 theorem indexed
    (revision : GeneralNominalReobservationSteps.Revision state.core.erased.current)
    (valid : Models (change state revision.result) model)
    (old : Evidence (GeneralDictionaryTotalEvidence206.Instance registry state.core model) tree)
    (shape : Shaped registry state.core.erased.current.context tree) :
    Evidence (GeneralDictionaryTotalEvidence206.Instance registry (change state revision.result).core model) tree := by
  induction old with
  | node source children ih =>
    cases shape with
    | node head descendants =>
      exact .node (local_instance revision head valid source) (fun child member => ih child member (descendants child member))

 theorem erased
    (revision : GeneralNominalReobservationSteps.Revision state.core.erased.current)
    (valid : Models (change state revision.result) model)
    (old : Evidence (GeneralDictionaryTotalEvidence206.Instance registry state.core model) tree)
    (shape : Shaped registry state.core.erased.current.context tree)
    (readback : Readback focus payload tree) :
    GeneralDictionaryTotalEvidence206.Evidence registry (change state revision.result).core model focus payload :=
  ⟨tree,readback,indexed revision valid old shape⟩

 theorem indexed_iff
    (revision : GeneralNominalReobservationSteps.Revision state.core.erased.current)
    (before : Models state model) (after : Models (change state revision.result) model)
    (shape : Shaped registry state.core.erased.current.context tree) :
    Evidence (GeneralDictionaryTotalEvidence206.Instance registry (change state revision.result).core model) tree ↔
      Evidence (GeneralDictionaryTotalEvidence206.Instance registry state.core model) tree := by
  constructor
  · intro source
    have result := indexed (GeneralDictionaryDefaultRevisionEquivalence210.inverse revision)
      ((GeneralDictionaryDefaultRevisionEquivalence210.inverse_result revision).symm ▸ before) source (shaped_forward revision shape)
    exact GeneralDictionaryDefaultRevisionEquivalence210.inverse_result revision ▸ result
  · exact fun source => indexed revision after source shape

 theorem certified_indexed_iff
    (revision : GeneralNominalReobservationSteps.Revision state.core.erased.current)
    (certificate : GeneralNominalCenteredHeadMatStepRefresh.Reobserve state revision)
    (valid : Models state model)
    (shape : Shaped registry state.core.erased.current.context tree) :
    Evidence (GeneralDictionaryTotalEvidence206.Instance registry (change state revision.result).core model) tree ↔
      Evidence (GeneralDictionaryTotalEvidence206.Instance registry state.core model) tree :=
  indexed_iff revision valid ((GeneralNominalCenteredHeadMatStepRefresh.reobserve_models certificate).mpr valid) shape
end Yulang.GeneralDictionaryDefaultScopedRevision210
