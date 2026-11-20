import Yulang.GeneralRebaseSourceHeadTransport288

/-! The actually retained child's direct root head has an independent
source proof after any guarded refresh. The leaf's nested read list is
empty. This establishes head and local equations, not full Holds. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29000
set_option maxHeartbeats 18000000
namespace Yulang.GeneralRebaseRowLeafSourceHeads288
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentPacket287 (child)
open GeneralRebaseRowParentFrame287 (after)
open GeneralRebaseRowLedger288 (supplemented)
open GeneralRebaseRowLeafWitness288 (source_exact)
open GeneralRebaseRowLeafLifetime288 (topOutput source_survives)
open GeneralRebaseRowLeafLocality288 (same_leaf_local_checks no_class_restrictions)
open GeneralRebaseRowTrustedBoundary287 (raw_after)
open GeneralRebaseRowRefreshPackets288 (child_frame)
open GeneralRebaseNonleafCommitted276 (result refinement interpretation)
open GeneralRebaseInertLeaf288 (SourceSlice)
open GeneralNominalVersionedMixedObservations233 (Refresh)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalRefinements (renameDescriptor)
open GeneralNominalSupport (Head)
open GeneralNominalRecursiveInspection (Test)
open GeneralCanonicalObservations (Observation)
open GeneralNominalCommonBridge (Assignment)

variable {context : GeneralNominalCandidates.Context}

noncomputable def inputObservation (cert : Refresh supplemented context) : Observation :=
  .nominal context.state.base (cert.refines.base.embed (0 : Fin 3))
    (renameDescriptor cert.refines.base.embed inner)

theorem actual_head (cert : Refresh supplemented context) :
    Head context.state 0 (.nominal 6 1) (inputObservation cert) := by
  have visible := cert.refines.nominals (0 : Fin 3) inner rfl
  have head := GeneralNominalSupport.Head.nominal (snapshot := context.state)
    (cert.refines.base.embed (0 : Fin 3)) (renameDescriptor cert.refines.base.embed inner) visible
  have source : context.state.base.source (cert.refines.base.embed (0 : Fin 3)) = 0 := cert.refines.base.source (0 : Fin 3)
  exact source ▸ head

theorem source_supported (cert : Refresh supplemented context) (m : Assignment)
    (source : SourceSlice (refresh supplemented context) m) :
    (inputObservation cert).Holds m := by
  have original : SourceSlice (after true) m := source
  have valid := (raw_after true m).mpr ((source_exact true m).mp original)
  have head := valid.2.1 (0 : Fin 3) inner rfl
  exact (GeneralRebaseSourceHeadTransport288.denotes_iff cert.refines m (0 : Fin 3) inner).mpr head

theorem nested_reads_empty (cert : Refresh supplemented context) :
    GeneralNominalSupport.readsMany context.state
      (GeneralNominalInspection.queries context.state context.interpretation opaqueChild)
      (result child_frame cert).packet.bounds = [] := by
  have same : GeneralNominalInspection.queries context.state context.interpretation opaqueChild =
      GeneralNominalInspection.queries (GeneralRebaseRowGeneratedChild287.current true).state
        (GeneralRebaseRowGeneratedChild287.current true).interpretation opaqueChild := by
    simp only [GeneralNominalInspection.queries,cert.interpretation,cert.refines.constructors]
    rfl
  rw [same,GeneralRebaseRowWholeChild287.query]
  generalize (result child_frame cert).packet.bounds = bounds
  cases bounds <;> simp [GeneralNominalSupport.readsMany,GeneralNominalSupport.reads]

theorem actual_source_scoped_checks (cert : Refresh supplemented context) :
    Head context.state 0 (.nominal 6 1) (inputObservation cert) ∧
    (∀ m, SourceSlice (refresh supplemented context) m →
      (inputObservation cert).Holds m ∧ GeneralNominalVersionedPlans231.Inputs (result child_frame cert) m ∧
      GeneralNominalVersionedPlans231.Outputs (result child_frame cert) m) := by
  refine ⟨actual_head cert,fun m source => ⟨source_supported cert m source,?_⟩⟩
  exact same_leaf_local_checks cert m source

end Yulang.GeneralRebaseRowLeafSourceHeads288
