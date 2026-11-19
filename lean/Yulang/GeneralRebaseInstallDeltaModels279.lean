import Yulang.GeneralRebaseInstallRequestDelta279

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseInstallDeltaModels279
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Models Effect)
open GeneralNominalVersionedInstall232 (install installCore install_models)
open GeneralNominalVersionedPlans231 (Holds head_models)
open GeneralNominalVersionedEffects231 (ClassEffects class_effects_iff)
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseInstallRequestDelta279 (EffectDelta class_iff FreshRequest)

variable {roles : Roles.RoleDecls} {state : State roles} {effect : Effect roles}

def Delta (state : State roles) (effect : Effect roles) (m : Assignment) : Prop :=
  EffectDelta state.core effect.plan effect.plan.packet.site.occurrence effect.plan m ∧
  (∀ older ∈ state.legacy.effects,
    EffectDelta state.core effect.plan older.plan.packet.site.occurrence older.plan m) ∧
  ∀ prior ∈ state.effects,
    EffectDelta state.core effect.plan prior.plan.packet.site.occurrence prior.plan m

theorem snapshot_effect (snapshot : effect.snapshot = state.core) (m : Assignment) :
    effect.Holds m ↔ GeneralNominalVersionedPlans231.HeadModels effect.plan.packet m ∧
      ClassEffects state.core effect.plan.packet.site.occurrence effect.plan m := by
  unfold Effect.Holds
  rw [snapshot]

theorem models_iff (snapshot : effect.snapshot = state.core) (m : Assignment) :
    Models (install state effect) m ↔
      Models state m ∧ Holds effect.plan m ∧
      ClassEffects state.core effect.plan.packet.site.occurrence effect.plan m ∧ Delta state effect m := by
  rw [install_models snapshot]
  constructor
  · rintro ⟨valid,held,_,live,legacy,prior⟩
    have current := (class_iff state.core effect.plan _ effect.plan m).mp live
    refine ⟨valid,held,current.1,current.2,?_,?_⟩
    · intro old mem
      have updated := (class_effects_iff _ _ _ _).mpr (legacy old mem)
      exact ((class_iff state.core effect.plan _ old.plan m).mp updated).2
    · intro old mem
      exact ((class_iff state.core effect.plan _ old.plan m).mp (prior old mem)).2
  · rintro ⟨valid,held,current,new,legacy,prior⟩
    refine ⟨valid,held,(snapshot_effect snapshot m).mpr ⟨head_models held,current⟩,
      (class_iff state.core effect.plan _ effect.plan m).mpr ⟨current,new⟩,?_,?_⟩
    · intro old mem
      apply (class_effects_iff _ _ _ _).mp
      exact (class_iff state.core effect.plan _ old.plan m).mpr
        ⟨(class_effects_iff _ _ _ _).mpr (valid.1.2.2.2.2.2 old mem).2,legacy old mem⟩
    · intro old mem
      exact (class_iff state.core effect.plan _ old.plan m).mpr
        ⟨(valid.2.2 old mem).2,prior old mem⟩

def NoFreshRequests (state : State roles) (effect : Effect roles) : Prop :=
  ∀ root output, ¬ FreshRequest state.core effect.plan root output

theorem delta_of_no_requests (silent : NoFreshRequests state effect) (m : Assignment) :
    Delta state effect m := by
  have every (p : Plan roles) : EffectDelta state.core effect.plan p.packet.site.occurrence p m :=
    ⟨fun _ fresh => False.elim (silent _ _ fresh),
    fun _ _ _ _ disj => False.elim (disj.elim (silent _ _) (silent _ _))⟩
  exact ⟨every effect.plan,fun p _ => every p.plan,fun p _ => every p.plan⟩

theorem no_fresh_iff (snapshot : effect.snapshot = state.core)
    (silent : NoFreshRequests state effect) (m : Assignment) :
    Models (install state effect) m ↔ Models state m ∧ Holds effect.plan m ∧
      ClassEffects state.core effect.plan.packet.site.occurrence effect.plan m := by
  rw [models_iff snapshot]
  exact ⟨fun h => ⟨h.1,h.2.1,h.2.2.1⟩,fun h => ⟨h.1,h.2.1,h.2.2,delta_of_no_requests silent m⟩⟩

end Yulang.GeneralRebaseInstallDeltaModels279
