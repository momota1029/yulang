import Yulang.GeneralNominalVersionedInstall232
import Yulang.GeneralNominalVersionedEffects231

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeferredLadderRequestFree303
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalVersionedInstall232 (install install_models installCore InstallationModels)
open GeneralNominalCenteredHeadOutputs (requests)
open GeneralNominalVersionedPlans231 (Holds)

theorem classes_empty (core : GeneralNominalCenteredSteps.State roles)
    (o : GeneralSourceDictionaries.Occurrence roles) (none : requests core o = [])
    (p : GeneralNominalCenters.Plan roles) (m : GeneralNominalCommonBridge.Assignment) :
    GeneralNominalVersionedEffects231.ClassEffects core o p m := by
  constructor
  · intro a ra
    rw [none] at ra
    cases ra
  · unfold GeneralNominalCenteredHeadOutputs.EqualOutputs
    rw [none]
    intro a ra
    cases ra

theorem model_of_request_free_install {s : State roles} (e : Effect roles)
    (snapshot : e.snapshot = s.core)
    (emptyLegacy : s.legacy.effects = [])
    (old : ∀ o, requests s.core o = [])
    (next : ∀ o, requests (installCore s.core e.plan) o = [])
    (held : ∀ m, Models s m → Holds e.plan m) :
    ∀ m, Models (install s e) m ↔ Models s m := by
  intro m
  constructor
  · intro found
    exact ((install_models snapshot).mp found).1
  · intro found
    have valid := held m found
    apply (install_models snapshot).mpr
    refine ⟨found,valid,⟨GeneralNominalVersionedPlans231.head_models valid,?_⟩,?_,?_,?_⟩
    · exact classes_empty _ _ (by rw [snapshot]; exact old _) _ m
    · exact classes_empty _ _ (next _) _ m
    · intro previous member
      rw [emptyLegacy] at member
      cases member
    · intro previous _
      exact classes_empty _ _ (next _) _ m

theorem model_alignment {s t : State roles} (e f : Effect roles)
    (one : ∀ m, Models (install s e) m ↔ Models s m)
    (same : ∀ m, Models s m ↔ Models t m)
    (two : ∀ m, Models (install t f) m ↔ Models t m) :
    ∀ m, Models (install s e) m ↔ Models (install t f) m :=
  fun m => (one m).trans ((same m).trans (two m).symm)

end Yulang.GeneralDeferredLadderRequestFree303
