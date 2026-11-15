import Yulang.GeneralDictionaryDefaultRevisionFrames210

set_option backward.isDefEq.respectTransparency false

/-! Existing nonnominal evidence survives an actual descriptor revision without
assuming that a current frame or selected classification has already been built. -/
namespace Yulang.GeneralDictionaryDefaultRevisionEvidence210
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal
open GeneralNominalCenteredHeadOutputs (Frame)
variable {roles : Roles.RoleDecls} {state : State roles} {historical : Plan roles}

 theorem certificate
    (revision : GeneralNominalReobservationSteps.Revision state.core.erased.current)
    (old : GeneralDictionaryTotalEvidence206.Certificate registry state.core model focus key children historical)
    (shape : ∀ query ∈ GeneralNominalInspection.queries historical.packet.context.state
      historical.packet.context.interpretation historical.packet.declaration,
      GeneralDictionaryDefaultStructuralReobserve210.Syntax query)
    (valid : Models (change state revision.result) model) :
    ∃ witness, GeneralDictionaryTotalEvidence206.Certificate registry (change state revision.result).core
      model focus key children witness ∧ witness.input = historical.input := by
  have oldCtx := old.frame.context_eq
  rcases historical with ⟨packet,input,inputExact⟩
  rcases packet with ⟨reg,ctx,site,decl,checked,bounds⟩
  dsimp at oldCtx
  subst ctx
  let nextPacket : GeneralNominalSaturationState.Packet roles :=
    ⟨reg,⟨revision.snapshot,state.core.erased.current.context.interpretation⟩,site,decl,checked,bounds⟩
  let witness : Plan roles := ⟨nextPacket,input,inputExact⟩
  have data : GeneralNominalCenteredHeadMatPlanData.Same witness
      ⟨⟨reg,state.core.erased.current.context,site,decl,checked,bounds⟩,input,inputExact⟩ :=
    ⟨rfl,rfl,rfl,rfl,rfl,rfl,
      GeneralDictionaryDefaultStructuralReobserve210.candidate_report revision shape
        (GeneralDictionaryTotalEvidence206.finished old)⟩
  have held : GeneralNominalCenteredHeadMatStepPackets.Holds witness model :=
    ⟨valid.1,(GeneralNominalCenteredHeadMatPlanData.delta data model).mpr old.packet.2⟩
  have prepared := old.frame.prepared
  obtain ⟨metadata,linked,fresh,oldBounds,located,finished,headModel⟩ := prepared
  have boundsEq : oldBounds = bounds := Option.some.inj (located.symm.trans old.frame.located)
  subst oldBounds
  have newFinished := (GeneralNominalViewTransport196.finished_report _
    (GeneralDictionaryDefaultStructuralReobserve210.view revision) _).mpr finished
  have checkedReport := GeneralDictionaryDefaultStructuralReobserve210.candidate_rechecked revision shape finished
  have frame : Frame registry (change state revision.result).core focus key witness := by
    refine ⟨old.frame.registry_eq,rfl,old.frame.occurrence_eq,old.frame.key_eq,
      old.frame.raw_recorded,old.frame.center_recorded,old.frame.visible,old.frame.role_eq,
      old.frame.located,metadata,linked,fresh,bounds,old.frame.located,?_,model,?_⟩
    · change GeneralNominalRecursiveInspection.Finished
        (GeneralNominalRecursiveCandidates.report
          (GeneralNominalViewTransport196.context _ (GeneralDictionaryDefaultStructuralReobserve210.view revision)) decl bounds)
      rw [checkedReport]
      exact newFinished
    · have head := (GeneralNominalCenteredHeadMatStepPackets.models_iff.mpr held).1
      have regEq : reg = registry := old.frame.registry_eq
      have occEq : site.occurrence = focus := old.frame.occurrence_eq
      change GeneralNominalCenteredHeadCandidates.HeadModels reg
        ⟨revision.snapshot,state.core.erased.current.context.interpretation⟩ site.occurrence decl bounds model at head
      rw [regEq,occEq] at head
      exact head
  refine ⟨witness,⟨frame,old.children_eq.trans (GeneralNominalCenteredHeadMatPlanData.children data).symm,held,?_⟩,rfl⟩
  intro output member
  obtain ⟨body,supplied,⟨expression,compiled⟩,heldBody⟩ := old.outputs output member
  exact ⟨body,supplied,⟨expression,compiled⟩,(GeneralDictionaryDefaultReinspection209.body_same data).mpr heldBody⟩

/-- Registry-local syntax restriction. Output expressions are unrestricted. -/
def Structural (registry : Registry) (context : GeneralNominalCandidates.Context) : Prop :=
  ∀ declaration ∈ registry.declarations,
    ∀ query ∈ GeneralNominalInspection.queries context.state context.interpretation declaration,
      GeneralDictionaryDefaultStructuralReobserve210.Syntax query

 theorem evidence_instance
    (revision : GeneralNominalReobservationSteps.Revision state.core.erased.current)
    (shape : Structural registry state.core.erased.current.context)
    (valid : Models (change state revision.result) model)
    (old : GeneralDictionaryTotalEvidence206.Instance registry state.core model focus key children) :
    GeneralDictionaryTotalEvidence206.Instance registry (change state revision.result).core model focus key children := by
  obtain ⟨historical,source⟩ := old
  have shaped := shape historical.packet.declaration source.frame.visible
  have queriesShape : ∀ query ∈ GeneralNominalInspection.queries historical.packet.context.state
      historical.packet.context.interpretation historical.packet.declaration,
      GeneralDictionaryDefaultStructuralReobserve210.Syntax query := by
    simpa only [source.frame.context_eq] using shaped
  obtain ⟨witness,certificate,_⟩ := certificate revision source queriesShape valid
  exact ⟨witness,certificate⟩

/-- Preserve the whole source-indexed dictionary and its exact erased payload.
Unlike node assembly, this transports every descendant, not assumed new children. -/
 theorem evidence
    (revision : GeneralNominalReobservationSteps.Revision state.core.erased.current)
    (shape : Structural registry state.core.erased.current.context)
    (valid : Models (change state revision.result) model)
    (old : GeneralDictionaryTotalEvidence206.Evidence registry state.core model focus payload) :
    GeneralDictionaryTotalEvidence206.Evidence registry (change state revision.result).core model focus payload := by
  obtain ⟨tree,readback,derived⟩ := old
  refine ⟨tree,readback,?_⟩
  clear readback
  induction derived with
  | node source children ih =>
    exact .node (evidence_instance revision shape valid source) ih

end Yulang.GeneralDictionaryDefaultRevisionEvidence210
