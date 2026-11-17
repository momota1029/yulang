import Yulang.GeneralNominalVersionedSemanticCompletion236
import Yulang.GeneralNominalVersionedPacketFrame236
import Yulang.GeneralNominalVersionedMixedCommon235
import Yulang.GeneralDictionaryDefaultJournalSupport213
import Yulang.GeneralDictionaryDefault214ActualBodyFrame
set_option backward.isDefEq.respectTransparency false
/-! Finite semantic support for the full mixed journal, including historical
and current class effects. This is a real model transport law, not a fresh-name
claim; supported assignments must actually agree. -/
namespace Yulang.GeneralNominalVersionedJournalFrame236
open GeneralNominalCenters GeneralNominalVersionedJournal232
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredFrame179 (Agree)
open GeneralNominalVersionedPacketFrame236 (headSources head_models_iff)
open GeneralDictionaryDefault214ActualBodyFrame (classSources)
variable {roles : Roles.RoleDecls} {first last : Assignment}

theorem class_iff (state : GeneralNominalCenteredSteps.State roles)
 (focus : GeneralSourceDictionaries.Occurrence roles) (plan : Plan roles)
 (same : Agree (classSources state focus plan) first last) :
 GeneralNominalVersionedEffects231.ClassEffects state focus plan first ↔
 GeneralNominalVersionedEffects231.ClassEffects state focus plan last := by
 rw [GeneralNominalVersionedEffects231.class_effects_iff,GeneralNominalVersionedEffects231.class_effects_iff]
 exact GeneralDictionaryDefault214ActualBodyFrame.class_iff state focus plan same

noncomputable def effectSources (state : State roles) (effect : Effect roles) : List Nat :=
 headSources effect.plan.packet ++
 classSources effect.snapshot effect.plan.packet.site.occurrence effect.plan ++
 classSources state.core effect.plan.packet.site.occurrence effect.plan

theorem effect_iff (state : State roles) (effect : Effect roles)
 (same : Agree (effectSources state effect) first last) :
 (effect.Holds first ∧ effect.Live state.core first) ↔
 (effect.Holds last ∧ effect.Live state.core last) := by
 apply and_congr
 · apply and_congr
   · exact head_models_iff _ (fun name member => same name (by simp [effectSources,member]))
   · exact class_iff _ _ _ (fun name member => same name (by simp [effectSources,member]))
 · exact class_iff _ _ _ (fun name member => same name (by simp [effectSources,member]))

noncomputable def sources (state : State roles) : List Nat :=
 GeneralDictionaryDefaultJournalSupport213.journalSources state.legacy ++
 state.plans.flatMap GeneralNominalVersionedPacketFrame236.sources ++
 state.effects.flatMap (effectSources state)

theorem models_iff (state : State roles) (same : Agree (sources state) first last) :
 Models state first ↔ Models state last := by
 apply and_congr
 · exact GeneralDictionaryDefaultJournalSupport213.models_iff state.legacy
     (fun name member => same name (by simp [sources,member]))
 apply and_congr
 · apply forall_congr'; intro plan
   apply forall_congr'; intro member
   apply GeneralNominalVersionedPacketFrame236.holds_iff
   intro name present
   have included : name ∈ state.plans.flatMap GeneralNominalVersionedPacketFrame236.sources :=
     List.mem_flatMap.mpr ⟨plan,member,present⟩
   exact same name (by simp [sources,included])
 · apply forall_congr'; intro effect
   apply forall_congr'; intro member
   apply effect_iff
   intro name present
   have included : name ∈ state.effects.flatMap (effectSources state) := List.mem_flatMap.mpr ⟨effect,member,present⟩
   exact same name (by simp [sources,included])

theorem assign_models (state : State roles)
 (names : Fin count → Nat) (values : Fin count → CommonNominalFullCarrier.Ty)
 (outside : ∀ index, names index ∉ sources state) (valid : Models state first) :
 Models state (GeneralNominalCenteredModelExtension.assign first names values) :=
 (models_iff state (GeneralNominalCenteredFrame179.assign_agree names values _ outside)).mp valid

/-- Simultaneous preservation with the actual finite aggregate patch. This
requires semantic journal disjointness, not merely allocation ownership. -/
theorem aggregate_models (state : State roles) (packet : GeneralNominalSaturationState.Packet roles)
 (fresh : GeneralNominalVersionedAggregateRealization236.Fresh packet.context.state.seed
   packet.site.occurrence.identity packet.declaration.id packet.bindings packet.declaration.inputNames (sources state))
 (valid : Models state first) :
 Models state (GeneralNominalVersionedSemanticCompletion236.extended packet first) := by
 apply (models_iff state _).mp valid
 intro identity member
 exact (GeneralNominalVersionedAggregateRealization236.preserves _ _ _ _ _ fresh identity member).symm
end Yulang.GeneralNominalVersionedJournalFrame236
