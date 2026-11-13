import Yulang.GeneralNominalProvenancePrefix
import Yulang.GeneralNominalAliasObservation

/-! Actual journal-certified observations for the first emitted Extract input.
Both fresh endpoints are recorded as aliases of the original list source. -/
set_option linter.unusedSimpArgs false
namespace Yulang.GeneralNominalProvenanceObserved
open GeneralNominalProvenanceDeclarations GeneralNominalProvenanceSource GeneralNominalProvenancePrefix
open GeneralNominalSaturationState GeneralNominalSupport GeneralSourceDictionaries
open GeneralNominalAliasObservation

noncomputable abbrev current := afterP.current.context.state

theorem flat : Flat current := ⟨rfl,rfl,fun _ => rfl,fun _ => rfl⟩

theorem absent (purpose owner position : Nat) :
    ∀ slot : Fin current.base.slots, current.base.source slot ≠ allocated purpose owner position := by
  intro slot same
  have bound := slot.isLt
  have large := GeneralNominalIdentities.source_above_seed state.seed
    (GeneralNominalAllocation.origin root.identity p.id purpose owner position)
  change slot.val = allocated purpose owner position at same
  change slot.val < 8 at bound
  change 7 < allocated purpose owner position at large
  omega

theorem reserved_member (purpose owner position : Nat)
    (owned : GeneralNominalAllocation.origin root.identity p.id purpose owner position ∈
      GeneralNominalAllocation.keys registry root.identity) :
    allocated purpose owner position ∈ GeneralNominalState.sources current := by
  apply List.mem_append_left
  apply List.mem_append_right
  change allocated purpose owner position ∈ [] ++ GeneralNominalAllocation.reserved state registry root.identity ++ []
  simpa only [List.nil_append,List.append_nil,GeneralNominalAllocation.reserved] using
    (List.mem_map.mpr ⟨_,owned,rfl⟩ : allocated purpose owner position ∈
      GeneralNominalAllocation.reserved state registry root.identity)

theorem lo_reserved : argumentLo 10 0 ∈ GeneralNominalState.sources current :=
  reserved_member 3 10 0 (by decide +kernel)

theorem hi_reserved : argumentHi 10 0 ∈ GeneralNominalState.sources current :=
  reserved_member 4 10 0 (by decide +kernel)

noncomputable abbrev lowerContext := GeneralNominalAliasObservation.context afterP.current (argumentLo 10 0)
  (absent 3 10 0) (1 : Fin 8) (listDescriptor 2) rfl
noncomputable def lower : Tracked roles :=
  {afterP with current := regenerate afterP.current lowerContext}

noncomputable def lower_certificate : GeneralNominalFeedbackSteps.Refresh afterP.current lowerContext :=
  certificate afterP.current flat (argumentLo 10 0) (absent 3 10 0) (1 : Fin 8) (listDescriptor 2) rfl
    lo_reserved extractA_endpoints.1

theorem lower_step : GeneralNominalValueSteps.Step registry root afterP lower :=
  actual_step afterP registry root flat (argumentLo 10 0) (absent 3 10 0) (1 : Fin 8) (listDescriptor 2) rfl
    lo_reserved extractA_endpoints.1

theorem lower_models (assignment : GeneralNominalCommonBridge.Assignment) :
    Models lower.current assignment ↔ Models afterP.current assignment :=
  GeneralNominalCycleSteps.refresh_models lower_certificate assignment

theorem lower_flat : Flat lower.current.context.state :=
  snapshot_flat current (argumentLo 10 0) (absent 3 10 0) (1 : Fin 8) (listDescriptor 2) rfl

theorem endpoints_distinct : argumentLo 10 0 ≠ argumentHi 10 0 := by
  intro same
  have equal := (GeneralNominalAllocation.source_identity state registry root.identity _ _).mp same
  have purpose := congrArg (fun origin => origin.2.2.1) equal
  cases purpose

theorem upper_absent : ∀ slot, lower.current.context.state.base.source slot ≠ argumentHi 10 0 := by
  intro slot
  refine Fin.lastCases ?_ (fun old => ?_) slot
  · simpa only [lower,lowerContext,regenerate,GeneralNominalAliasObservation.context,snapshot,
      GeneralNominalAliasObservation.base,identifiers,Fin.lastCases_last] using endpoints_distinct
  · simpa only [lower,lowerContext,regenerate,GeneralNominalAliasObservation.context,snapshot,
      GeneralNominalAliasObservation.base,identifiers,Fin.lastCases_castSucc] using absent 4 10 0 old

abbrev liftedDescriptor := GeneralNominalRefinements.renameDescriptor (@Fin.castSucc 8) (listDescriptor 2)

theorem lifted_recorded : lower.current.context.state.nominals (1 : Fin 8).castSucc = some liftedDescriptor := by
  change (Option.some (listDescriptor 2)).map (GeneralNominalRefinements.renameDescriptor (@Fin.castSucc 8)) = _
  rfl

theorem upper_reserved : argumentHi 10 0 ∈ GeneralNominalState.sources lower.current.context.state :=
  GeneralNominalRefinements.sources lower_certificate.1 _ hi_reserved

theorem upper_equal : GeneralNominalFeedbackK2.Equal lower.current (argumentHi 10 0)
    (lower.current.context.state.base.source (1 : Fin 8).castSucc) := by
  intro assignment valid
  have same := extractA_endpoints.2 assignment ((lower_models assignment).mp valid)
  change CommonNominalFullCarrier.Equivalent (assignment (argumentHi 10 0)).1
    (assignment (identifiers current (argumentLo 10 0) (1 : Fin 8).castSucc)).1
  simp only [identifiers,Fin.lastCases_castSucc]
  exact same

noncomputable abbrev upperContext := GeneralNominalAliasObservation.context lower.current (argumentHi 10 0)
  upper_absent (1 : Fin 8).castSucc liftedDescriptor lifted_recorded
noncomputable def observed : Tracked roles :=
  {lower with current := regenerate lower.current upperContext}

noncomputable def upper_certificate : GeneralNominalFeedbackSteps.Refresh lower.current upperContext :=
  certificate lower.current lower_flat (argumentHi 10 0) upper_absent (1 : Fin 8).castSucc
    liftedDescriptor lifted_recorded upper_reserved upper_equal

theorem upper_step : GeneralNominalValueSteps.Step registry root lower observed :=
  actual_step lower registry root lower_flat (argumentHi 10 0) upper_absent (1 : Fin 8).castSucc
    liftedDescriptor lifted_recorded upper_reserved upper_equal

theorem observed_models (assignment : GeneralNominalCommonBridge.Assignment) :
    Models observed.current assignment ↔ Models afterP.current assignment :=
  (GeneralNominalCycleSteps.refresh_models upper_certificate assignment).trans (lower_models assignment)

theorem steps : B4Target.Steps (GeneralNominalValueSteps.Step registry root) start observed :=
  .tail (.tail (.tail .refl first_step) lower_step) upper_step

theorem formed : GeneralNominalValueSteps.SourceFormed registry root observed :=
  .update (.update first_formed lower_step) upper_step

theorem generated : Generated observed.current root kidExtractA := by
  exact GeneralNominalValueSteps.generated_monotone upper_step
    (GeneralNominalValueSteps.generated_monotone lower_step
      (generated_children kidExtractA (by rw [children]; simp)))

theorem endpoints_known : GeneralNominalState.Known observed.current.context.state (argumentLo 10 0) ∧
    GeneralNominalState.Known observed.current.context.state (argumentHi 10 0) := by
  constructor
  · exact upper_certificate.1.known _
      (known current (argumentLo 10 0) (absent 3 10 0) (1 : Fin 8) (listDescriptor 2) rfl)
  · exact known lower.current.context.state (argumentHi 10 0) upper_absent (1 : Fin 8).castSucc
      liftedDescriptor lifted_recorded


noncomputable abbrev lowerSlot : Fin observed.current.context.state.base.slots := (Fin.last 8).castSucc
noncomputable abbrev upperSlot : Fin observed.current.context.state.base.slots := Fin.last 9

theorem lower_identity : observed.current.context.state.base.source lowerSlot = argumentLo 10 0 := by
  change identifiers lower.current.context.state (argumentHi 10 0) (Fin.castSucc (Fin.last 8)) = _
  simp only [identifiers,Fin.lastCases_castSucc]
  rfl

theorem upper_identity : observed.current.context.state.base.source upperSlot = argumentHi 10 0 := by
  change identifiers lower.current.context.state (argumentHi 10 0) (Fin.last 9) = _
  simp only [identifiers,Fin.lastCases_last]
  rfl

theorem extract_arguments (index : Fin (roles kidExtractA.demand.role).arity) :
    kidExtractA.demand.arguments index = (argumentLo 10 0,argumentHi 10 0) := by
  have zero : index.val = 0 := by have bound := index.isLt; change index.val < 1 at bound; omega
  simp [kidExtractA,GeneralNominalFeedbackSites.clauseChild,GeneralDictionaryEmissionPlans.occurrence,
    GeneralNominalFeedbackSites.frame,GeneralDeclarationDemands.emit,GeneralDeclarationDemands.childDemand,
    GeneralDeclarationDemands.inputInterval,GeneralNominalAllocation.frame,GeneralNominalAllocation.allocation,
    packet,extractA,zero,GeneralNominalDemandMerging.pointSite,GeneralDeclarationPatterns.normalize,argumentLo,argumentHi,allocated]

noncomputable abbrev extractBounds : List (GeneralNominalInspection.Bounds observed.current.context.state) :=
  [(lowerSlot,upperSlot)]

theorem extract_located : GeneralNominalRecursiveCandidates.arguments observed.current.context kidExtractA = some extractBounds := by
  change GeneralCandidateBoundaryParts.locate observed.current.context.state.base
    [kidExtractA.demand.arguments ⟨0,by decide +kernel⟩] = _
  rw [extract_arguments]
  have lo : GeneralDictionaryBinderLocations.sourceSlot observed.current.context.state.base (argumentLo 10 0) = some lowerSlot :=
    (GeneralDictionaryBinderLocations.sourceSlot_exact ..).mpr lower_identity
  have hi : GeneralDictionaryBinderLocations.sourceSlot observed.current.context.state.base (argumentHi 10 0) = some upperSlot :=
    (GeneralDictionaryBinderLocations.sourceSlot_exact ..).mpr upper_identity
  simp [GeneralCandidateBoundaryParts.locate,lo,hi,extractBounds]

theorem extract_ready : ¬ GeneralNominalState.RootPending observed.current.context.state kidExtractA.demand := by
  rintro ⟨index,unknown⟩
  apply unknown
  rw [extract_arguments]
  exact endpoints_known.1

theorem extract_query : GeneralNominalInspection.queries observed.current.context.state
    observed.current.context.interpretation extract = [.nominal 0 [.variables [0]]] := by
  change GeneralNominalInspection.queries state interpretation extract = _
  simp [GeneralNominalInspection.queries,GeneralDeclarations.Declaration.normalHead,
    GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,GeneralNominalInspection.translate,
    extract,interpretation,constructors,GeneralDeclarationExamples.constructors]

noncomputable abbrev extractReport : GeneralNominalRecursiveInspection.Report observed.current.context.state where
  captures := [⟨0,((2 : Fin 10),(2 : Fin 10)),some (.nominal (.source (argumentLo 10 0)) 0 0)⟩,
    ⟨0,((2 : Fin 10),(2 : Fin 10)),some (.nominal (.source (argumentHi 10 0)) 0 0)⟩]
  inspected := [(lowerSlot,upperSlot)]
  checked := [(lowerSlot,upperSlot),(lowerSlot,upperSlot),((2 : Fin 10),(2 : Fin 10)),((2 : Fin 10),(2 : Fin 10))]
  anchors := [(.nominal (.source (argumentLo 10 0)) 0 0,((2 : Fin 10),(2 : Fin 10))),
    (.nominal (.source (argumentHi 10 0)) 0 0,((2 : Fin 10),(2 : Fin 10)))]

noncomputable abbrev currentDescriptor : GeneralNominalState.Descriptor observed.current.context.state.base.slots :=
  ⟨0,⟨[.type],0⟩,[.type ((2 : Fin 10),(2 : Fin 10))],rfl⟩

theorem lo_recorded : observed.current.context.state.nominals lowerSlot = some currentDescriptor := rfl

theorem hi_recorded : observed.current.context.state.nominals upperSlot = some currentDescriptor := rfl

theorem slots_distinct : lowerSlot ≠ upperSlot := by
  intro equal
  have impossible := congrArg Fin.val equal
  change 8 = 9 at impossible
  cases impossible

theorem extract_report : GeneralNominalRecursiveCandidates.report observed.current.context extract extractBounds = extractReport := by
  unfold GeneralNominalRecursiveCandidates.report
  rw [extract_query]
  simp only [extractBounds,GeneralNominalRecursiveInspection.inspectMany,GeneralNominalRecursiveInspection.inspect,
    lo_recorded,hi_recorded,currentDescriptor,GeneralNominalRecursiveInspection.typeArguments,slots_distinct,
    ↓reduceIte,List.mapM_cons,List.mapM_nil]
  simp [GeneralNominalRecursiveInspection.Report.visit,GeneralNominalRecursiveInspection.Report.append,
    GeneralNominalRecursiveInspection.inspectMany.eq_1,GeneralNominalRecursiveInspection.inspectMany.eq_2,
    GeneralNominalRecursiveInspection.inspect.eq_1,extractReport,lower_identity,upper_identity]

theorem extract_finished : GeneralNominalRecursiveInspection.Finished
    (GeneralNominalRecursiveCandidates.report observed.current.context extract extractBounds) := by
  rw [extract_report]
  exact ⟨rfl,rfl,rfl⟩

end Yulang.GeneralNominalProvenanceObserved
