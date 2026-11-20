import Yulang.GeneralRebaseRowRefreshShape288

/-! Every permitted first refresh of the guarded static fixture has the
same type identities readable, and point-only nominal descriptors. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28700
set_option maxHeartbeats 17000000
namespace Yulang.GeneralRebaseRowRefreshClosed288
open GeneralRebaseRowChildSource287
open GeneralRebaseRowLedger288 (supplemented models_eq)
open GeneralRebaseRowGeneratedChild287 (current)
open GeneralRebaseRowSemanticMark287 (outputDescriptor)
open GeneralRebaseRowLedgerFirst288 (cannot_certify_private)
open GeneralRebaseRowRefreshShape288 (only_descriptor actually_nominal)
open GeneralNominalVersionedMixedObservations233 (Refresh cache_sound refresh_models)
open GeneralNominalState (Known Descriptor)
open GeneralNominalReobservationSteps (PointClosed PointDescriptor)
open GeneralNominalRefinements (renameDescriptor)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalVersionedJournal232 (Models)

variable {context : GeneralNominalCandidates.Context}

theorem recognized_exact (cert : Refresh supplemented context) (new : Known context.state 2) (n : Nat) :
    Known context.state n ↔ n ≤ 2 := by
  constructor
  · intro known
    by_cases low : n ≤ 2
    · exact low
    · exact (cannot_certify_private cert n (by omega) known).elim
  · intro small
    by_cases edge : n = 2
    · exact edge.symm ▸ new
    · exact cert.refines.known n (GeneralRebaseRowAdministrative287.already_known true n (by omega))

theorem point_renamed {first last : Nat} (embed : Fin first → Fin last)
    (d : Descriptor first) (point : PointDescriptor d) : PointDescriptor (renameDescriptor embed d) := by
  intro param mem
  obtain ⟨old,oldMem,rfl⟩ := List.mem_map.mp mem
  have eq := point old oldMem
  cases old with
  | type bounds => exact congrArg embed eq
  | row bounds => exact congrArg embed eq

theorem point_output : PointDescriptor outputDescriptor := by
  intro param mem
  cases List.mem_singleton.mp mem
  rfl

theorem point_closed (cert : Refresh supplemented context) (new : Known context.state 2) :
    PointClosed context.state := by
  intro slot desc seen
  have recognized := (recognized_exact cert new _).mp ⟨slot,rfl,.inr ⟨desc,seen⟩⟩
  have opts : context.state.base.source slot = 0 ∨ context.state.base.source slot = 1 ∨
      context.state.base.source slot = 2 := by omega
  rcases opts with zero | one | two
  · have ind : slot = cert.refines.base.embed (0 : Fin 3) :=
      context.state.base.source_injective (zero.trans (cert.refines.base.source (0 : Fin 3)).symm)
    have earlier := cert.refines.nominals (0 : Fin 3) inner rfl
    rw [← ind,seen] at earlier
    cases Option.some.inj earlier
    exact point_renamed _ inner (GeneralRebaseRowAdministrative287.point_closed true (0 : Fin 3) inner rfl)
  · have ind : slot = cert.refines.base.embed (1 : Fin 3) :=
      context.state.base.source_injective (one.trans (cert.refines.base.source (1 : Fin 3)).symm)
    have earlier := cert.refines.nominals (1 : Fin 3) outer rfl
    rw [← ind,seen] at earlier
    cases Option.some.inj earlier
    exact point_renamed _ outer (GeneralRebaseRowAdministrative287.point_closed true (1 : Fin 3) outer rfl)
  · rw [only_descriptor context cert two seen]
    exact point_renamed _ outputDescriptor point_output

theorem no_more_refresh (cert : Refresh supplemented context) (new : Known context.state 2)
    {other : GeneralNominalCandidates.Context} (next : Refresh (refresh supplemented context) other)
    (n : Nat) (old : ¬ Known context.state n) : ¬ Known other.state n := by
  intro further
  have high : 2 < n := by
    by_cases small : n ≤ 2
    · exact (old ((recognized_exact cert new n).mpr small)).elim
    · omega
  let witness := GeneralRebaseRowTrustedBoundary287.putTop (model Common.rowEmpty) n
  have valid := (refresh_models cert).mpr ((models_eq witness).mpr
    ((GeneralRebaseRowParentFrame287.after_exact true witness).mpr
      ((GeneralRebaseRowAdministrative287.output_elsewhere (model Common.rowEmpty) high).mpr
        ((GeneralRebaseRowParentFrame287.after_exact true _).mp
          (GeneralRebaseRowParentFrame287.after_model true Common.rowEmpty)))))
  obtain ⟨test,obs,headed⟩ := GeneralNominalCenteredHeadMatStepCache.known_has_head further
  have checked := GeneralDictionaryGroundCopy218Refresh.head_holds headed
    (cache_sound next.cache (GeneralNominalSupport.head_recorded headed) valid)
  change test.Holds (if n = n then .top else (model Common.rowEmpty n).1) at checked
  rw [ite_eq_left rfl] at checked
  exact GeneralDictionaryGroundCopy218Refresh.top_no_head test checked

end Yulang.GeneralRebaseRowRefreshClosed288
