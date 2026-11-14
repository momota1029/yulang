import Yulang.GeneralDictionaryCenteredPointCandidate179
import Yulang.GeneralNominalCenteredJournalExtension179

/-! Actual linear nominal candidate readback over an existing centered journal.
Only non-point generated binders must avoid its concrete finite footprint. -/
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryCenteredJournalPoint180
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalRecursiveInspection GeneralNominalRecursiveCandidates
open GeneralNominalCenteredSteps GeneralDictionaryLinearLeaf GeneralNominalLinearMaterializationFacts
open GeneralDictionaryCenteredPointReadback179 GeneralDictionaryCenteredPointJoint179
open GeneralNominalRawFrame179 (fullSources)
open CommonNominalFullCarrier GeneralNominalCenteredModelExtension
variable {roles : Roles.RoleDecls} (journal : State roles) (plan : Plan roles)
  (shape : LinearLeafShape plan.packet.context plan.packet.site.occurrence plan.packet.declaration)

 theorem readback_extension
    (contextEq : plan.packet.context = journal.erased.current.context)
    (located : plan.packet.bounds = [(shape.slot,shape.slot)])
    (outside : ∀ i : Fin shape.arity,
      plan.packet.context.state.base.source (shape.bounds i).1 ≠
        plan.packet.context.state.base.source (shape.bounds i).2 →
      plan.binder (shape.names i) ∉ fullSources journal)
    (previous : GeneralNominalCommonBridge.Assignment)
    (journalValid : Models journal previous) :
    ∃ extended, Models journal extended ∧
      (∀ name ∈ fullSources journal, extended name = previous name) ∧
      Readback plan shape extended := by
  classical
  have valid : GeneralNominalState.Models plan.packet.context.state previous := by
    rw [contextEq]; exact journalValid.1.1
  have full_member (slot : Fin plan.packet.context.state.base.slots) :
      plan.packet.context.state.base.source slot ∈ fullSources journal := by
    have member := source_member slot
    have sources : GeneralNominalState.sources plan.packet.context.state =
        GeneralNominalState.sources journal.erased.current.context.state := by rw [contextEq]
    rw [sources] at member
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ member))
  let state := plan.packet.context.state
  let lower := fun i : Fin shape.arity => state.base.source (shape.bounds i).1
  let upper := fun i : Fin shape.arity => state.base.source (shape.bounds i).2
  let origin := fun i : Fin shape.arity => Origin.nominal (.source (state.base.source shape.slot))
    shape.descriptor.declaration.name i.val
  have observed (i : Fin shape.arity) := nominal_argument_bounds
    state previous valid shape.slot shape.descriptor shape.recorded i.val (shape.bounds i)
    (by rw [shape.parameters]; simp [i.isLt])
  let actual := fun i : Fin shape.arity => Classical.choose (observed i).1
  have actual_seen (i : Fin shape.arity) : Observes previous (origin i) (actual i) :=
    Classical.choose_spec (observed i).1
  let values := fun i : Fin shape.arity => if lower i = upper i then (previous (lower i)).1 else actual i
  have center (i : Fin shape.arity) : plan.binder (shape.names i) =
      if lower i = upper i then lower i else
        fresh state.seed plan.packet.site.occurrence.identity plan.packet.declaration.id 8 (shape.names i) 0 :=
    binder_exact plan shape located i
  have bounds (i : Fin shape.arity) : GeneralNominalCaptureMerges.Fits previous (lower i,upper i) (values i) := by
    dsimp only [values]
    split
    · rename_i point
      rw [point]
      exact ⟨subtype_refl _,subtype_refl _⟩
    · exact (observed i).2 _ (actual_seen i)
  have readback (i : Fin shape.arity) : (∃ a, Observes previous (origin i) a) ∧
      ∀ a, Observes previous (origin i) a → Equivalent a (values i) := by
    refine ⟨⟨actual i,actual_seen i⟩,?_⟩
    intro a seen
    dsimp only [values]
    split
    · rename_i point
      have fit := (observed i).2 a seen
      change Subtype (previous (lower i)).1 a ∧ Subtype a (previous (upper i)).1 at fit
      rw [← point] at fit
      exact ⟨fit.2,fit.1⟩
    · exact nominal_observation_unique previous
        (.argument (.source (state.base.source shape.slot)) shape.descriptor.declaration.name i.val)
        a (actual i) seen (actual_seen i)
  have coherent (i j : Fin shape.arity) (same : plan.binder (shape.names i) = plan.binder (shape.names j)) :
      values i = values j := by
    rw [center i,center j] at same
    by_cases one : lower i = upper i <;> by_cases two : lower j = upper j
    · simpa only [values,one,two,ite_true] using congrArg (fun name => (previous name).1)
        (by simpa only [one,two,ite_true] using same : lower i = lower j)
    · apply False.elim
      apply outside j two
      have member := full_member (shape.bounds i).1
      have eq : plan.binder (shape.names j) = lower i := by
        rw [center j]
        simpa only [one,two,ite_true,ite_false] using same.symm
      rw [eq]
      exact member
    · apply False.elim
      apply outside i one
      have member := full_member (shape.bounds j).1
      have eq : plan.binder (shape.names i) = lower j := by
        rw [center i]
        simpa only [one,two,ite_true,ite_false] using same
      rw [eq]
      exact member
    · simp only [one,two,ite_false] at same
      have keys := (GeneralNominalIdentities.source_identity state.seed _ _).mp same
      have names := congrArg (fun key : GeneralNominalIdentities.Origin => key.2.2.2.1) keys
      have equal := shape.distinct names
      rw [equal]
  let arguments := fun i : Fin shape.arity =>
    (⟨⟨(lower i,upper i),plan.binder (shape.names i)⟩,origin i⟩ : NominalArgument)
  obtain ⟨extended,models,kept,_values,holds⟩ :=
    GeneralNominalCenteredJournalExtension179.nominal_extension journal arguments previous journalValid values
      (fun i => ⟨full_member _,full_member _,full_member _⟩) bounds readback coherent
      (by
        intro i member
        change values i = (previous (plan.binder (shape.names i))).1
        rw [center i]
        by_cases point : lower i = upper i
        · simp [values,point]
        · exact False.elim (outside i point member))
  exact ⟨extended,models,kept,fun i => (holds i).2⟩

/-- A complete new plan model and the unchanged existing journal model. -/
 theorem joint_model
    (contextEq : plan.packet.context = journal.erased.current.context)
    (located : plan.packet.bounds = [(shape.slot,shape.slot)])
    (named : plan.input.PointNames)
    (outside : ∀ i : Fin shape.arity,
      plan.packet.context.state.base.source (shape.bounds i).1 ≠
        plan.packet.context.state.base.source (shape.bounds i).2 →
      plan.binder (shape.names i) ∉ fullSources journal)
    (previous : GeneralNominalCommonBridge.Assignment)
    (valid : Models journal previous) :
    ∃ extended, Models journal extended ∧ plan.Holds extended ∧
      ∀ name ∈ fullSources journal, extended name = previous name := by
  obtain ⟨extended,models,kept,readback⟩ :=
    readback_extension journal plan shape contextEq located outside previous valid
  have source : GeneralNominalState.Models plan.packet.context.state extended := by
    rw [contextEq]; exact models.1.1
  have input := point_input plan shape named extended
  exact ⟨extended,models,
    (holds_iff_readback plan shape located (centers_exact plan shape named) extended source input).mpr readback,kept⟩

end Yulang.GeneralDictionaryCenteredJournalPoint180
