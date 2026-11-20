import Yulang.GeneralRebaseObserverExact267
import Yulang.GeneralRebaseInstallDeltaModels279

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseSignedModels297
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalVersionedMixedMaterialization237 (Residual)
open GeneralNominalVersionedMixedCommon235 (installation_models_iff)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalCenteredHeadAllocEncoding (registry)
open GeneralNominalVersionedInstall232 (install)
open GeneralRebaseInstallChecks267 (semanticCommitted)

inductive Sign where
 | pass
 | reject
 deriving DecidableEq, Repr

def Conditions (s : State roles) (p : Plan roles) (m : Assignment) : Prop :=
  GeneralNominalVersionedPlans231.Holds p m ∧
    GeneralNominalVersionedEffects231.ClassEffects s.core p.packet.site.occurrence p m

def Test (s : State roles) (p : Plan roles) (sign : Sign) (m : Assignment) : Prop :=
  Models s m ∧ match sign with
  | .pass => Conditions s p m
  | .reject => ¬ Conditions s p m

theorem reject_exact (s : State roles) (p : Plan roles) :
    (∃ m, Test s p .reject m) ↔ ¬ semanticCommitted s p := by
  classical
  constructor
  · rintro ⟨m,old,no⟩ yes
    exact no (yes m old)
  · intro no
    apply Classical.byContradiction
    intro lacks
    apply no
    intro m old
    apply Classical.byContradiction
    intro rejected
    exact lacks ⟨m,old,rejected⟩

theorem pass_exact {s : State roles} {e : Effect roles}
    (checked : (boundary roles).Checked r)
    (path : B4TargetV8.Reachable (boundary roles) r root s)
    (reg : e.registry = registry r) (snap : e.snapshot = s.core) (m : Assignment) :
    Test s e.plan .pass m ↔ Residual s e m :=
  (installation_models_iff checked path reg snap).symm.trans
    (GeneralNominalVersionedMixedMaterialization237.installation_models_iff checked path reg snap)

/-- Reachability upgrades the local conjunction to the exact installed raw model. -/
theorem accepted_exact {s : State roles} {e : Effect roles}
    (checked : (boundary roles).Checked r)
    (path : B4TargetV8.Reachable (boundary roles) r root s)
    (reg : e.registry = registry r) (snap : e.snapshot = s.core) (m : Assignment) :
    Test s e.plan .pass m ↔ Models (install s e) m :=
  (installation_models_iff checked path reg snap).symm.trans
    (GeneralNominalVersionedInstall232.install_models snap).symm

theorem rejected_exact {s : State roles} {e : Effect roles}
    (checked : (boundary roles).Checked r)
    (path : B4TargetV8.Reachable (boundary roles) r root s)
    (reg : e.registry = registry r) (snap : e.snapshot = s.core) (m : Assignment) :
    Test s e.plan .reject m ↔ Models s m ∧ ¬ Models (install s e) m := by
  refine ⟨fun h => ⟨h.1,fun after => h.2 ((accepted_exact checked path reg snap m).mpr after).2⟩,?_⟩
  exact fun h => ⟨h.1,fun yes => h.2 ((accepted_exact checked path reg snap m).mp ⟨h.1,yes⟩)⟩

theorem exclusive (s : State roles) (p : Plan roles) (m : Assignment) :
    ¬ (Test s p .pass m ∧ Test s p .reject m) :=
  fun h => h.2.2 h.1.2

theorem neither_of_no_model (s : State roles) (empty : ¬ ∃ m, Models s m)
    (p : Plan roles) (sign : Sign) : ¬ ∃ m, Test s p sign m :=
  fun ⟨m,yes⟩ => empty ⟨m,yes.1⟩

theorem reject_loses {s : State roles} {e : Effect roles} (snap : e.snapshot = s.core)
    (m : Assignment) (rejected : Test s e.plan .reject m) :
    Models s m ∧ ¬ Models (install s e) m :=
  ⟨rejected.1, fun accepted =>
    let checks := (GeneralRebaseInstallDeltaModels279.models_iff snap m).mp accepted
    rejected.2 ⟨checks.2.1,checks.2.2.1⟩⟩

theorem loss_includes_delta {s : State roles} {e : Effect roles} (snap : e.snapshot = s.core)
    (m : Assignment) :
    (Models s m ∧ ¬ Models (install s e) m) ↔
      Test s e.plan .reject m ∨
      (Test s e.plan .pass m ∧ ¬ GeneralRebaseInstallDeltaModels279.Delta s e m) := by
  classical
  rw [GeneralRebaseInstallDeltaModels279.models_iff snap m]
  constructor
  · rintro ⟨old,no⟩
    by_cases h : Conditions s e.plan m
    · exact Or.inr ⟨⟨old,h⟩,fun d => no ⟨old,h.1,h.2,d⟩⟩
    · exact Or.inl ⟨old,h⟩
  · rintro (⟨old,no⟩ | ⟨⟨old,_⟩,no⟩)
    · exact ⟨old,fun yes => no ⟨yes.2.1,yes.2.2.1⟩⟩
    · exact ⟨old,fun yes => no yes.2.2.2⟩

theorem loss_exact_of_no_requests {s : State roles} {e : Effect roles}
    (snap : e.snapshot = s.core)
    (quiet : GeneralRebaseInstallDeltaModels279.NoFreshRequests s e) (m : Assignment) :
    (Models s m ∧ ¬ Models (install s e) m) ↔ Test s e.plan .reject m := by
  rw [loss_includes_delta snap]
  exact ⟨fun h => h.elim id (fun q => False.elim
    (q.2 (GeneralRebaseInstallDeltaModels279.delta_of_no_requests quiet m))),Or.inl⟩

end Yulang.GeneralRebaseSignedModels297
