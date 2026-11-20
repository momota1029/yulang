import Yulang.GeneralMixedCompoundEarlyRefresh308
import Yulang.GeneralMixedCompoundPointAcc307

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 18000
set_option maxHeartbeats 8500000
namespace Yulang.GeneralMixedCompoundEarlySquare308
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralDictionaryCompoundSource238 (registry sourceRegistry)
open GeneralDictionaryCompoundFrame238 (before installed)
open GeneralDictionaryCompoundPoint238 (point)
open GeneralMixedCompoundEarlyBase308 (looseSnap wideLoose same_domain)
open GeneralMixedCompoundUpperSnapshot307 (snap desc context)
open GeneralMixedCompoundUpperRefresh307 (upperState)
open GeneralMixedCompoundEarlyRefresh308 (early static_installed_early cache_point)
open GeneralMixedCompoundEarlyModels308 (equal)
open GeneralMixedCacheStatic308 (cache)
open GeneralNominalReobservationSteps (Revision Improves PointAt PointDescriptor)
open GeneralNominalVersionedMixedObservations233 (Reobserve reobserve_models)
open GeneralNominalVersionedRefresh232 (reobserve)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalVersionedJournal232 (Models State)
open GeneralNominalCommonBridge (Assignment)

noncomputable def revision : Revision early.core.erased.current :=
  ⟨snap.nominals,snap.catalogue,snap.bodies_opaque,fun slot => (same_domain slot).symm⟩

theorem result_exact : reobserve early revision = upperState := rfl

theorem desc_is_point : PointDescriptor desc := by
  intro parameter member
  change parameter ∈ [.type ((2 : Fin 8),2),.type (2,2)] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl <;> rfl

theorem witness_zero : PointAt revision.snapshot (0 : Fin 8) :=
  ⟨desc,rfl,desc_is_point⟩

theorem loose_not_point : ¬ PointAt looseSnap (0 : Fin 8) := by
  rintro ⟨d,seen,point⟩
  have same : wideLoose = d := Option.some.inj seen
  subst d
  have bad := point (.type ((4 : Fin 8),2)) (by exact List.mem_cons_self)
  exact (by decide : (4 : Fin 8) ≠ 2) bad

theorem improves : Improves revision := by
  refine ⟨?_,(0 : Fin 8),loose_not_point,witness_zero⟩
  rintro i ⟨d,recorded,_⟩
  change Fin 8 at i
  by_cases z : i = 0
  · subst i; exact witness_zero
  · by_cases o : i = 1
    · subst i
      exact ⟨desc,rfl,desc_is_point⟩
    · change (if i = 0 then some wideLoose else if i = 1 then some desc else none) = some d at recorded
      simp [z,o] at recorded

theorem certificate : Reobserve early revision :=
  ⟨fun m h => (equal m).mpr h,cache static_installed_early cache_point⟩

theorem step : Step registry root early upperState := by
  rw [← result_exact]
  exact ⟨root,.root,.administrative (.reobserve root revision certificate improves)⟩

theorem common_model (m : Assignment) : Models upperState m ↔ Models early m :=
  reobserve_models certificate

theorem batch_step : Step registry root point upperState :=
  ⟨root,.root,.refresh root context GeneralMixedCompoundBatch307.batch
    GeneralDictionaryCompoundBase239.lo (GeneralDictionaryCompoundRefresh239.supported 5 (by decide))
    GeneralDictionaryCompoundRefreshStep239.lower_unknown GeneralMixedCompoundUpperSupport307.known_lo⟩

theorem square :
    Step registry root installed point ∧ Step registry root point upperState ∧
    Step registry root installed early ∧ Step registry root early upperState ∧
    (∀ next : State roles, ¬ Step registry root upperState next) :=
  ⟨GeneralDictionaryCompoundPoint238.step,batch_step,GeneralMixedCompoundEarlyRefresh308.step,step,
    GeneralMixedCompoundUpperHalt307.halted⟩

theorem early_not_point : early ≠ point := by
  intro h
  have counts := congrArg (fun s : State roles => s.core.erased.current.context.state.base.slots) h
  exact (by decide : (8 : Nat) ≠ 5) counts

end Yulang.GeneralMixedCompoundEarlySquare308
