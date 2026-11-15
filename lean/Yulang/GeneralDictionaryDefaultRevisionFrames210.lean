import Yulang.GeneralDictionaryDefaultStructuralReobserve210
import Yulang.GeneralDictionaryDefaultRetainedCenter210

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralDictionaryDefaultRevisionFrames210
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal
open GeneralNominalCenteredHeadOutputs (Frame)
open GeneralDictionaryDefaultSemanticReplay209 (recenter)
variable {roles : Roles.RoleDecls} {state : State roles} {current historical : Plan roles}

 theorem frame_finished (frame : Frame registry core focus key plan) :
    GeneralNominalRecursiveInspection.Finished
      (GeneralNominalRecursiveCandidates.report plan.packet.context plan.packet.declaration plan.packet.bounds) := by
  have prepared : GeneralNominalCenteredHeadCandidates.Prepared registry plan.packet.context focus plan.packet.declaration :=
    frame.context_eq.symm ▸ frame.prepared
  obtain ⟨_,_,_,bounds,located,done,_⟩ := prepared
  have same : bounds = plan.packet.bounds := Option.some.inj (located.symm.trans frame.located)
  subst bounds
  exact done
 theorem report (checked : Checked registry)
    (revision : GeneralNominalReobservationSteps.Revision state.core.erased.current)
    (oldFrame : Frame registry state.core focus key historical)
    (newFrame : Frame registry (change state revision.result).core focus key current)
    (shape : ∀ query ∈ GeneralNominalInspection.queries historical.packet.context.state
      historical.packet.context.interpretation historical.packet.declaration,
      GeneralDictionaryDefaultStructuralReobserve210.Syntax query) :
    GeneralNominalReportErasure.erase current.packet.context.state
      (GeneralNominalPacketSupport.report current.packet) =
    GeneralNominalReportErasure.erase historical.packet.context.state
      (GeneralNominalPacketSupport.report historical.packet) := by
  have declaration := GeneralDictionaryEmissionPlans.declaration_key_unique registry checked _ _
    newFrame.visible oldFrame.visible (newFrame.key_eq.trans oldFrame.key_eq.symm)
  have finished := frame_finished oldFrame
  have oldCtx := oldFrame.context_eq
  have newCtx := newFrame.context_eq
  rcases historical with ⟨oldPacket,oldInput,oldExact⟩
  rcases current with ⟨newPacket,newInput,newExact⟩
  rcases oldPacket with ⟨oldReg,oldContext,oldSite,oldDeclaration,oldChecked,oldBounds⟩
  rcases newPacket with ⟨newReg,newContext,newSite,newDeclaration,newChecked,newBounds⟩
  dsimp at oldCtx newCtx declaration
  subst oldContext
  subst newContext
  subst newDeclaration
  have bounds : newBounds = oldBounds := Option.some.inj (newFrame.located.symm.trans oldFrame.located)
  subst newBounds
  exact GeneralDictionaryDefaultStructuralReobserve210.candidate_report revision shape finished

 theorem retained_data (checked : Checked registry)
    (revision : GeneralNominalReobservationSteps.Revision state.core.erased.current)
    (oldFrame : Frame registry state.core focus key historical)
    (newFrame : Frame registry (change state revision.result).core focus key current)
    (shape : ∀ query ∈ GeneralNominalInspection.queries historical.packet.context.state
      historical.packet.context.interpretation historical.packet.declaration,
      GeneralDictionaryDefaultStructuralReobserve210.Syntax query)
    (same : historical.input.occurrence = current.packet.site.occurrence) :
    GeneralNominalCenteredHeadMatPlanData.Same (recenter current historical.input same) historical := by
  refine ⟨newFrame.registry_eq.trans oldFrame.registry_eq.symm,
    GeneralDictionaryEmissionPlans.declaration_key_unique registry checked _ _
      newFrame.visible oldFrame.visible (newFrame.key_eq.trans oldFrame.key_eq.symm),rfl,?_,?_,?_,
    report (current := current) checked revision oldFrame newFrame shape⟩
  · change current.packet.context.state.seed = historical.packet.context.state.seed
    rw [newFrame.context_eq,oldFrame.context_eq]; rfl
  · change current.packet.context.state.constructors = historical.packet.context.state.constructors
    rw [newFrame.context_eq,oldFrame.context_eq]; rfl
  · change current.packet.context.interpretation = historical.packet.context.interpretation
    rw [newFrame.context_eq,oldFrame.context_eq]; rfl

 theorem certificate (checked : Checked registry)
    (revision : GeneralNominalReobservationSteps.Revision state.core.erased.current)
    (newFrame : Frame registry (change state revision.result).core focus key current)
    (old : GeneralDictionaryTotalEvidence206.Certificate registry state.core model focus key children historical)
    (shape : ∀ query ∈ GeneralNominalInspection.queries historical.packet.context.state
      historical.packet.context.interpretation historical.packet.declaration,
      GeneralDictionaryDefaultStructuralReobserve210.Syntax query)
    (valid : Models (change state revision.result) model) :
    ∃ witness, GeneralDictionaryTotalEvidence206.Certificate registry (change state revision.result).core
      model focus key children witness ∧ witness.input = historical.input := by
  have same := historical.input_exact.trans (old.frame.occurrence_eq.trans newFrame.occurrence_eq.symm)
  let witness := recenter current historical.input same
  have currentFrame := GeneralDictionaryDefaultRetainedCenter210.recenter_frame newFrame historical.input
    old.frame.center_recorded same
  have data := retained_data checked revision old.frame newFrame shape same
  refine ⟨witness,⟨currentFrame,old.children_eq.trans (GeneralNominalCenteredHeadMatPlanData.children data).symm,
    GeneralDictionaryDefaultReinspection209.packet_reinspect data currentFrame valid old.packet,?_⟩,rfl⟩
  intro output member
  obtain ⟨body,supplied,⟨expression,compiled⟩,held⟩ := old.outputs output member
  refine ⟨body,data.declaration.symm ▸ supplied,⟨expression,?_⟩,
    (GeneralDictionaryDefaultReinspection209.body_same data).mpr held⟩
  exact (GeneralDictionaryDefaultBodyTransport209.compile_equal
    (congrArg Registry.constructors data.registry) data.interpretation body).trans compiled

 theorem children (checked : Checked registry)
    (revision : GeneralNominalReobservationSteps.Revision state.core.erased.current)
    (oldFrame : Frame registry state.core focus key historical)
    (newFrame : Frame registry (change state revision.result).core focus key current)
    (shape : ∀ query ∈ GeneralNominalInspection.queries historical.packet.context.state
      historical.packet.context.interpretation historical.packet.declaration,
      GeneralDictionaryDefaultStructuralReobserve210.Syntax query) :
    current.packet.children = historical.packet.children := by
  have same := historical.input_exact.trans (oldFrame.occurrence_eq.trans newFrame.occurrence_eq.symm)
  have equal := GeneralNominalCenteredHeadMatPlanData.children (retained_data checked revision oldFrame newFrame shape same)
  exact equal

end Yulang.GeneralDictionaryDefaultRevisionFrames210
