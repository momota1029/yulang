import Yulang.GeneralRebaseReceiptCompile289

/-! The auxiliary mark is entailed by the provenance-checked slice,
not a newly observed head of the original snapshot. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28800
set_option maxHeartbeats 18500000
namespace Yulang.GeneralRebaseReceiptPoint289
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentFrame287 (after effect after_exact)
open GeneralRebaseRowGeneratedChild287 (current)
open GeneralRebaseRowSemanticMark287 (outputDescriptor marked)
open GeneralRebaseRowLeafSlice288 (finalFacts prior slice_exact)
open GeneralRebaseReceiptCompile289 (Mark observe actualMark concrete_compile)
open GeneralRebaseReceiptScopedTrace289 (Family family_iff)
open GeneralRebaseReceiptRawProduct289 (Config Next initial)
open GeneralRebaseReceiptFixture289 (request)
open GeneralRebaseReceiptWitness289 (Witness witness_positive)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedSupport233 (SliceModels)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Equivalent subtype_trans)

abbrev pointObservation : GeneralCanonicalObservations.Observation := .nominal raw.base (2 : Fin 3) outputDescriptor

theorem compiled_mark_denotes (m : Assignment) :
    actualMark.Holds m ↔ pointObservation.Holds m :=
  (GeneralRebaseRowOutputHeadSupport288.prior_descriptor_meaning m).symm

theorem checked_slice_entails (m : Assignment) (slice : SliceModels (after true) (finalFacts true) m) :
    actualMark.Holds m := by
  have proof := (slice_exact true m).mp slice
  have raised : Equivalent (F (m 1).1) (F (F (m 0).1)) :=
    GeneralNominalCenteredHeadMatCompilerSemantics.nominal_congr 0 (.cons proof.1.2 .nil)
  exact ⟨subtype_trans proof.2.1 raised.2,subtype_trans raised.1 proof.2.2⟩

theorem release_exact (choice : Bool) {s : Config}
    (path : B4Target.Steps (Next choice) initial s) (code : Mark) :
    observe root s.phase = some code ↔
      choice = true ∧ s.raw = after true ∧ s.phase = .published (request true) ∧ code = actualMark := by
  constructor
  · intro view
    have family := (family_iff choice s).mp path
    cases family with
    | start => cases view
    | earlyDenied => cases view
    | afterScan => cases view
    | received _ => cases view
    | stillPending _ => cases view
    | published yes =>
      subst choice
      change GeneralRebaseReceiptCompile289.compile root (request true) = some code at view
      rw [concrete_compile] at view
      exact ⟨rfl,rfl,rfl,(Option.some.inj view).symm⟩
  · rintro ⟨yes,_,phase,rfl⟩
    rw [phase]
    exact concrete_compile true

theorem published_models (choice : Bool) {s : Config}
    (path : B4Target.Steps (Next choice) initial s) (code : Mark)
    (released : observe root s.phase = some code) (m : Assignment) (valid : Models s.raw m) :
    code.Holds m := by
  obtain ⟨_,rawEq,_,rfl⟩ := (release_exact choice path code).mp released
  have actual := rawEq ▸ valid
  apply checked_slice_entails
  exact GeneralRebaseLeafOutput288.output_models witness_positive.exactOutputCut actual

theorem not_old_known (choice : Bool) {s : Config}
    (path : B4Target.Steps (Next choice) initial s) (code : Mark)
    (released : observe root s.phase = some code) :
    ¬ GeneralNominalState.Known s.raw.core.erased.current.context.state code.target := by
  obtain ⟨_,rawEq,_,rfl⟩ := (release_exact choice path code).mp released
  rw [rawEq]
  exact GeneralRebaseRowLedger288.unknown_output true

theorem noncircular_source_countermodel :
    GeneralRebaseInertLeaf288.SourceSlice (after true) GeneralRebaseRowLeafLifetime288.topOutput ∧
      ¬ actualMark.Holds GeneralRebaseRowLeafLifetime288.topOutput := by
  refine ⟨GeneralRebaseRowLeafLifetime288.source_survives
    (context := GeneralRebaseRowGeneratedChild287.current true),?_⟩
  intro mark
  exact GeneralNominalTopObservation.top_not_nominal 0 _ mark.1

end Yulang.GeneralRebaseReceiptPoint289
