import Yulang.GeneralRebaseRowPhaseSimulation288

/-! Fresh source-only leaf certification is not monotone in the raw
snapshot. The source survives a harmless output refresh, but the exact
current packet now observes that output. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29000
set_option maxHeartbeats 18500000
namespace Yulang.GeneralRebaseRowLeafLifetime288
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentPacket287 (child)
open GeneralRebaseRowParentFrame287 (after after_model)
open GeneralRebaseRowLedger288 (supplemented)
open GeneralRebaseRowLeafWitness288 (source_exact)
open GeneralRebaseRowTrustedBoundary287 (putTop outside_source)
open GeneralRebaseRowRefreshShape288 (actually_nominal)
open GeneralRebaseInertLeaf288 (SourceSlice Leaf)
open GeneralNominalVersionedMixedObservations233 (Refresh)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalState (Known)
open GeneralNominalCommonBridge (Assignment)

abbrev topOutput : Assignment := putTop (model Common.rowEmpty) 2

theorem source_survives {context : GeneralNominalCandidates.Context} :
    SourceSlice (refresh supplemented context) topOutput := by
  change SourceSlice (after true) topOutput
  apply (source_exact true _).mpr
  exact (outside_source (model Common.rowEmpty) (by decide)).mpr
    ((GeneralRebaseRowChildRaw287.exact_source _).mp (raw_model Common.rowEmpty))

theorem outside_snapshot {context : GeneralNominalCandidates.Context}
    (cert : Refresh supplemented context) (known : Known context.state 2) :
    ¬ GeneralNominalState.Models context.state topOutput := by
  intro raw
  let slot := cert.refines.base.embed (2 : Fin 3)
  let descriptor := GeneralNominalRefinements.renameDescriptor cert.refines.base.embed
    GeneralRebaseRowSemanticMark287.outputDescriptor
  have seen : context.state.nominals slot = some descriptor := actually_nominal context cert known
  have stored := raw.2.1 slot descriptor seen
  obtain ⟨arguments,fit,denotes⟩ := stored
  have atSlot : context.state.base.source slot = 2 := cert.refines.base.source (2 : Fin 3)
  rw [atSlot] at denotes
  exact GeneralNominalTopObservation.top_not_nominal _ _ denotes.1

theorem no_fresh_leaf {context : GeneralNominalCandidates.Context}
    (cert : Refresh supplemented context) (known : Known context.state 2)
    (focus : GeneralSourceDictionaries.Occurrence roles) (key : Nat) (p : GeneralNominalCenters.Plan roles) :
    ¬ Leaf (registry true) (refresh supplemented context) focus key p := by
  intro fresh
  have raw := (fresh.sourcePacket topOutput source_survives).1
  rw [fresh.frame.context_eq] at raw
  exact outside_snapshot cert known raw

theorem origin_works_but_fresh_recertification_fails {context : GeneralNominalCandidates.Context}
    (cert : Refresh supplemented context) (known : Known context.state 2) :
    Leaf (registry true) (after true) (child true) 1 GeneralRebaseRowWholeChild287.plan ∧
    (∀ m, GeneralNominalVersionedJournal232.Models (refresh supplemented context) m ↔
      GeneralNominalVersionedJournal232.Models (after true) m) ∧
    (∀ key p, ¬ Leaf (registry true) (refresh supplemented context) (child true) key p) :=
  ⟨GeneralRebaseRowLeafWitness288.leaf,
    fun m => (GeneralNominalVersionedMixedObservations233.refresh_models cert).trans
      (GeneralRebaseRowLedger288.models_eq m),
    no_fresh_leaf cert known (child true)⟩

end Yulang.GeneralRebaseRowLeafLifetime288
