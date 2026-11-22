import Yulang.GeneralDeclarativeTxnObserve348
import Yulang.GeneralDeclarativeTxnEffects348

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeTxnTrace348
open GeneralDeclarations (Registry)
open GeneralNominalCenters (Plan Site)
open GeneralNominalCandidates (Context)
open GeneralNominalReobservationSteps (Revision)
open GeneralWhereVersionInstall317 (Journal Models install emitted)
open GeneralDeclarativeWhereTxn348 (Txn)
open GeneralDeclarativeTxnObserve348 (refresh revise refresh_models revise_models)
open GeneralWhereOriginSupport318 (journalSources)
open GeneralNominalCenteredFrame179 (Agree)
open GeneralNominalCommonBridge (Assignment)

/-- Experimental and explicitly checked transition fragment. It does
not claim that the unmodified native driver executes either the
new transaction or arbitrary replay of its former attempts. The
protected set is verified before each new commit. -/
inductive Step (r : Registry) (keep : List Nat) : Journal rs → Journal rs → Prop
  | transaction {j} (ctx : Context) (p : Plan rs) :
      Txn r j ctx p → keep ⊆ journalSources j → Step r keep j (install j ctx p)
  | observe {j} (ctx : Context) :
      GeneralNominalVersionedMixedObservations233.Refresh j.mixed ctx →
      Step r keep j (refresh j ctx)
  | reobserve {j} (revision : Revision j.mixed.core.erased.current) :
      GeneralNominalVersionedMixedObservations233.Reobserve j.mixed revision →
      GeneralNominalReobservationSteps.Improves revision → Step r keep j (revise j revision)

theorem projects {a b : Journal rs} (step : Step r keep a b) (m : Assignment) :
    Models b m → Models a m := by
  intro fit
  cases step with
  | transaction _ _ clause _ =>
    obtain ⟨physical⟩ := clause.physical
    exact GeneralDeclarativeJournalPrefix347.previous physical m fit
  | observe _ observed => exact (refresh_models observed m).mp fit
  | reobserve _ observed _ => exact (revise_models observed m).mp fit

theorem extends_step {a b : Journal rs} (step : Step r keep a b) (m : Assignment) (fit : Models a m) :
    ∃ n, Models b n ∧ Agree keep m n := by
  cases step with
  | transaction _ _ clause stable =>
    obtain ⟨n,model,agree⟩ := clause.extends_models m fit
    exact ⟨n,model,fun k used => agree k (stable used)⟩
  | observe _ observed => exact ⟨m,(refresh_models observed m).mpr fit,fun _ _ => rfl⟩
  | reobserve _ observed _ => exact ⟨m,(revise_models observed m).mpr fit,fun _ _ => rfl⟩

theorem path_projects {a b : Journal rs} (path : B4Target.Steps (Step r keep) a b)
    (m : Assignment) (fit : Models b m) : Models a m := by
  induction path with
  | refl => exact fit
  | tail _ last ih => exact ih (projects last m fit)

theorem path_extends {a b : Journal rs} (path : B4Target.Steps (Step r keep) a b)
    (m : Assignment) (fit : Models a m) : ∃ n, Models b n ∧ Agree keep m n := by
  induction path with
  | refl => exact ⟨m,fit,fun _ _ => rfl⟩
  | tail _ last ih =>
    obtain ⟨middle,legal,first⟩ := ih
    obtain ⟨n,valid,rest⟩ := extends_step last middle legal
    exact ⟨n,valid,fun k used => (first k used).trans (rest k used)⟩

end Yulang.GeneralDeclarativeTxnTrace348
