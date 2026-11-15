import Yulang.GeneralDictionaryDefaultPacketSupport213

/-! Finite support for corrected journal Models, with total packet meanings,
explicit/default snapshot effects, and the current merged-class effects. -/
namespace Yulang.GeneralDictionaryDefaultJournalSupport213
open GeneralNominalCenters GeneralNominalCenteredHeadMatStepJournal
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredFrame179 (Agree siteSources site_iff)
open GeneralDictionaryDefaultModeEffects213 (classSources class_iff)
open GeneralDictionaryDefaultPacketSupport213 (packetSources packet_iff)
variable {roles : Roles.RoleDecls} {first last : Assignment}

 noncomputable def effectSources (state : State roles) (effect : Effect roles) : List Nat :=
  GeneralNominalHeadLedgerFrame182.headSources effect.plan ++
    classSources effect.snapshot effect.plan.packet.site.occurrence effect.plan ++
    classSources state.core effect.plan.packet.site.occurrence effect.plan

 theorem effect_iff (state : State roles) (effect : Effect roles)
    (same : Agree (effectSources state effect) first last) :
    (effect.Holds first ∧ effect.Live state.core first) ↔
    (effect.Holds last ∧ effect.Live state.core last) := by
  apply and_congr
  · apply and_congr
    · exact GeneralNominalHeadLedgerFrame182.head_iff effect.plan
        (fun name member => same name (by simp [effectSources,member]))
    · exact class_iff _ _ _ (fun name member => same name (by simp [effectSources,member]))
  · exact class_iff _ _ _ (fun name member => same name (by simp [effectSources,member]))

 noncomputable def journalSources (state : State roles) : List Nat :=
  GeneralDictionaryDefaultRawSupport213.sources state.core.erased.current.context.state ++
  GeneralDictionaryDefaultRawSupport213.sources state.core.erased.source.state ++
  state.core.erased.current.sites.flatMap GeneralNominalCenteredEmptyFrame179.rawSiteSources ++
  state.core.sites.flatMap siteSources ++ state.core.plans.flatMap packetSources ++
  state.effects.flatMap (effectSources state)

 theorem models_iff (state : State roles) (same : Agree (journalSources state) first last) :
    Models state first ↔ Models state last := by
  have raw (snapshot : GeneralNominalState.State)
      (support : Agree (GeneralDictionaryDefaultRawSupport213.sources snapshot) first last) :
      GeneralNominalState.Models snapshot first ↔ GeneralNominalState.Models snapshot last :=
    GeneralDictionaryDefaultRawSupport213.models_iff _ support
  apply and_congr (raw _ (fun name member => same name (by simp [journalSources,member])))
  apply and_congr (raw _ (fun name member => same name (by simp [journalSources,member])))
  apply and_congr
  · apply forall_congr'; intro site
    apply forall_congr'; intro member
    apply GeneralNominalCenteredEmptyFrame179.raw_site_iff
    intro name present
    have included : name ∈ state.core.erased.current.sites.flatMap GeneralNominalCenteredEmptyFrame179.rawSiteSources :=
      List.mem_flatMap.mpr ⟨site,member,present⟩
    exact same name (by simp [journalSources,included])
  apply and_congr
  · apply forall_congr'; intro site
    apply forall_congr'; intro member
    apply site_iff
    intro name present
    have included : name ∈ state.core.sites.flatMap siteSources := List.mem_flatMap.mpr ⟨site,member,present⟩
    exact same name (by simp [journalSources,included])
  apply and_congr
  · apply forall_congr'; intro plan
    apply forall_congr'; intro member
    apply packet_iff
    intro name present
    have included : name ∈ state.core.plans.flatMap packetSources := List.mem_flatMap.mpr ⟨plan,member,present⟩
    exact same name (by simp [journalSources,included])
  · apply forall_congr'; intro effect
    apply forall_congr'; intro member
    apply effect_iff
    intro name present
    have included : name ∈ state.effects.flatMap (effectSources state) := List.mem_flatMap.mpr ⟨effect,member,present⟩
    exact same name (by simp [journalSources,included])

 theorem models_assign (state : State roles)
    (names : Fin count → Nat) (values : Fin count → CommonNominalFullCarrier.Ty)
    (outside : ∀ index, names index ∉ journalSources state) (valid : Models state first) :
    Models state (GeneralNominalCenteredModelExtension.assign first names values) :=
  (models_iff state (GeneralNominalCenteredFrame179.assign_agree names values _ outside)).mp valid

end Yulang.GeneralDictionaryDefaultJournalSupport213
