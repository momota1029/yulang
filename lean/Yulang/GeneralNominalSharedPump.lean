import Yulang.GeneralNominalSharedSteps
import Yulang.GeneralNominalSettledIntervalObstruction

/-! The checked interval example fails generation at its first P packet.
The leaf W still passes generation; its unshared output cannot be promoted. -/
set_option linter.unusedSimpArgs false
namespace Yulang.GeneralNominalSharedPump
open GeneralNominalSettledIntervalDeclarations GeneralNominalSettledIntervalSource
open GeneralNominalSaturationState GeneralNominalRecursiveInspection
open GeneralNominalSharedCaptures GeneralNominalOriginTerms

abbrev pPacket : Packet roles :=
  ⟨registry,context,GeneralNominalDemandMerging.pointSite root,p,p_checked,[(0,0),(3,5)]⟩
abbrev aOrigin : Origin := .structural (.structural (.source 0) (.variant 0) 0) (.variant 0) 0

theorem p_queries : GeneralNominalInspection.queries source interpretation p =
    [.node (.variant 0) [.node (.variant 0) [.variables [0]]],.variables [1]] := by
  simp [GeneralNominalInspection.queries,GeneralDeclarations.Declaration.normalHead,p,tick,
    GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
    GeneralNominalInspection.translate,GeneralCandidateInspection.plainNames]

theorem p_captures : (inheritedReport pPacket).captures =
    [⟨0,(2,2),some aOrigin⟩,⟨1,(3,5),none⟩] := by
  unfold inheritedReport
  rw [p_queries]
  simp [inspectMany,inspect,Report.visit,Report.append,pPacket,
    GeneralNominalDemandMerging.pointSite,root,roles,bareRole,GeneralNominalProvenanceDeclarations.bareRole,
    source,view,views,aOrigin,List.ofFn_succ]
  repeat first
    | rw [inspectMany.eq_def]
    | rw [inspect.eq_def]
    | simp [Report.visit,Report.append,GeneralNormalizedObservation.Shape.arity,source,view,views]

theorem b_needed : Needed pPacket 1 := by
  refine ⟨wrapChild,by simp [pPacket,p],?_⟩
  simp [wrapChild,tick,GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
    GeneralDeclarationPatterns.variablesArgs,GeneralDeclarationPatterns.Pattern.variables]

theorem p_first_round_blocked (state : GeneralNominalSupport.Tracked roles) : ¬ GenerationGuard state pPacket := by
  apply missing_capture_blocks b_needed
  intro captured member same
  rw [p_captures] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · cases same
  · rfl

theorem p_not_installable (state : GeneralNominalSupport.Tracked roles) (support : List (GeneralSourceDictionaries.Occurrence roles)) :
    ¬ GeneralNominalSharedSteps.PacketGuard state pPacket support :=
  GeneralNominalSharedSteps.missing_generation_blocks (p_first_round_blocked state)

theorem source_formed : GeneralNominalSharedSteps.SourceFormed registry root start :=
  .initial context initial_source

abbrev leaf := GeneralNominalSettledIntervalOutputs.packet

theorem leaf_generation (state : GeneralNominalSupport.Tracked roles) : GenerationGuard state leaf :=
  no_children_guard rfl

theorem leaf_captures : (inheritedReport leaf).captures =
    [⟨0,(2,2),some (.structural (.source 1) (.variant 0) 0)⟩,⟨1,(3,5),none⟩] := by
  unfold inheritedReport
  rw [GeneralNominalSettledIntervalOutputs.queries]
  simp [inspectMany,inspect,Report.visit,Report.append,leaf,GeneralNominalSettledIntervalOutputs.packet,
    GeneralNominalDemandMerging.pointSite,GeneralNominalSettledIntervalOutputs.leafRoot,
    GeneralNominalSettledIntervalOutputs.bounds,roles,source,view,views,List.ofFn_succ]
  repeat first
    | rw [inspectMany.eq_def]
    | rw [inspect.eq_def]
    | simp [Report.visit,Report.append,GeneralNormalizedObservation.Shape.arity,source,view,views]

theorem leaf_output_deferred (state : GeneralNominalSupport.Tracked roles) (facts readbacks) :
    ¬ Nonempty (GeneralNominalSharedSupport.OutputCertificate state facts readbacks leaf) := by
  rintro ⟨certificate⟩
  have present : (⟨1,.source 8,.actual⟩ : GeneralNominalMaterialization.Use) ∈
      (GeneralNominalPacketSupport.namedSchema leaf).variables := by
    rw [GeneralNominalSettledIntervalOutputs.schema_exact]
    simp [GeneralNominalSettledIntervalOutputs.body]
  obtain ⟨origin,_,⟨captured,member,same,recorded⟩,_⟩ := certificate.inputs _ present rfl (by
    simp [leaf,GeneralNominalSettledIntervalOutputs.packet,w,GeneralDeclarations.Declaration.outputNames])
  rw [leaf_captures] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · cases same
  · cases recorded

theorem shared_round_cycle {a b next : CommonNominalFullCarrier.Ty}
    (first : CommonNominalFullCarrier.Equivalent a (V b))
    (descent : CommonNominalFullCarrier.Equivalent a (V next))
    (second : CommonNominalFullCarrier.Equivalent next (V b)) : CommonNominalFullCarrier.Equivalent b (V b) := by
  open CommonNominalFullCarrier in
    have equal := GeneralNominalSettledIntervalObstruction.variant_cancel
      (⟨subtype_trans first.2 descent.1,subtype_trans descent.2 first.1⟩ : Equivalent (V b) (V next))
    exact ⟨subtype_trans equal.1 second.1,subtype_trans second.2 equal.2⟩

end Yulang.GeneralNominalSharedPump
