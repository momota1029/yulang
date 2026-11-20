import Yulang.GeneralMixedDiagnosticSliceReplay304

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralMixedDiagnosticReplayStep304
open GeneralDeclarations GeneralSourceDictionaries CommonRoleOutermostResolver
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalVersionedInstall232 (install install_models)
open GeneralNominalVersionedMixedKernel234 (Installable Step Committed)
open GeneralNominalVersionedEffects231 (ClassEffects class_effects_iff)
open GeneralNominalVersionedPlans231 (Holds head_models)
open GeneralDeferredLadderResnapshot304 (HeadView resnapshot safe_forward alternatives_forward)
open GeneralDeferredLadderOperationalView304 (classes_iff after_install choices choice_forward generated_iff committed_iff)
open GeneralDeferredLadderAdministrative304 (known_forward)
open GeneralMixedDiagnosticSliceReplay304 (KeepsRequests class_iff stays_on_other_side semantics_after)
open GeneralMixedDiagnosticSlice304 (Semantics)
open GeneralNominalCommonBridge (Assignment)

variable {roles : Roles.RoleDecls} {a b : State roles}

theorem model_after (s : State roles) (e : Effect roles) (atS : e.snapshot = s.core)
    (stable : KeepsRequests s e.plan) (m : Assignment) :
    Models (install s e) m ↔ Models s m ∧ Holds e.plan m ∧
      ClassEffects s.core e.plan.packet.site.occurrence e.plan m := by
  constructor
  · intro valid
    have v := (install_models atS).mp valid
    exact ⟨v.1,v.2.1,(class_iff _ (stable _) _ m).mp v.2.2.2.1⟩
  · rintro ⟨old,packet,output⟩
    refine (install_models atS).mpr ⟨old,packet,⟨head_models packet,atS.symm ▸ output⟩,
      (class_iff _ (stable _) _ m).mpr output,?_,?_⟩
    · intro legacyEffect found
      have held := (old.1.2.2.2.2.2 legacyEffect found).2
      exact (class_effects_iff ..).mp ((class_iff _ (stable _) _ m).mpr
        ((class_effects_iff ..).mpr held))
    · intro prior present
      exact (class_iff _ (stable _) _ m).mpr (old.2.2 prior present).2

theorem after_models (same : HeadView a b) (e : Effect roles) (atA : e.snapshot = a.core)
    (stable : KeepsRequests a e.plan) (m : Assignment) :
    Models (install a e) m ↔ Models (install b (resnapshot same e atA)) m :=
  (model_after a e atA stable m).trans
    ((and_congr (same.raw.models m) (and_congr Iff.rfl
      (classes_iff same.raw e.plan e.plan.packet.site.occurrence m))).trans
      (model_after b (resnapshot same e atA) rfl (stays_on_other_side same e.plan stable) m).symm)

theorem after_head (same : HeadView a b) (e : Effect roles) (atA : e.snapshot = a.core)
    (stable : KeepsRequests a e.plan) :
    HeadView (install a e) (install b (resnapshot same e atA)) := by
  refine ⟨after_install same.raw _ _ rfl rfl (after_models same e atA stable),rfl,?_⟩
  change a.core.sites ++ _ = b.core.sites ++ _
  rw [same.centers]
  rfl

theorem mirrored_installable (same : HeadView a b) (chosen : choices a = choices b)
    (e : Effect roles) (good : Installable registry a e)
    (stable : KeepsRequests a e.plan)
    (cache : GeneralNominalVersionedMixedObservations233.CacheSound b b.core.erased.current.context.state) :
    Installable registry b (resnapshot same e good.snapshot_eq) := by
  refine ⟨good.registry_eq,rfl,known_forward same good.safe,cache,good.materialized,
    choice_forward same.raw chosen good.choice,safe_forward same good.positions,
    alternatives_forward same good.alternatives,?_⟩
  obtain ⟨m,satisfies⟩ := good.common
  exact ⟨m,(install_models (effect := resnapshot same e good.snapshot_eq) rfl).mp
    ((after_models same e good.snapshot_eq stable m).mp
      ((install_models good.snapshot_eq).mpr satisfies))⟩

theorem actual_install (same : HeadView a b) (chosen : choices a = choices b)
    (e : Effect roles) (good : Installable registry a e)
    (stable : KeepsRequests a e.plan)
    (cache : GeneralNominalVersionedMixedObservations233.CacheSound b b.core.erased.current.context.state)
    (generated : GeneralNominalSaturationState.Generated a.core.erased.current root e.plan.packet.site.occurrence)
    (novel : ¬ Committed a e.plan) :
    Step registry root b (install b (resnapshot same e good.snapshot_eq)) :=
  ⟨_,(generated_iff same.raw).mp generated,.install _
    (mirrored_installable same chosen e good stable cache)
    (fun already => novel ((committed_iff same.raw e.plan).mpr already))⟩

theorem local_after (same : HeadView a b) (slices : Semantics a b) (e : Effect roles)
    (atA : e.snapshot = a.core) (stable : KeepsRequests a e.plan) (registry : Registry)
    (root : Occurrence roles) (front : Frontier (Occurrence roles)) :
    B4TargetV8.Local (GeneralMixedDiagnosticHead304.boundary8 roles) registry (install a e) root front ↔
      B4TargetV8.Local (GeneralMixedDiagnosticHead304.boundary8 roles) registry
        (install b (resnapshot same e atA)) root front :=
  GeneralMixedDiagnosticLocal304.local_iff (after_head same e atA stable)
    (semantics_after same slices e atA stable) registry root front

end Yulang.GeneralMixedDiagnosticReplayStep304
