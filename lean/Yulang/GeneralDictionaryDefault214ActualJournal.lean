import Yulang.GeneralDictionaryDefault214ActualEffects

/-! Corrected journal frame with normalized semantic explicit-body support.
Snapshot/live defaults and all total packet meanings remain unchanged. -/
namespace Yulang.GeneralDictionaryDefault214ActualJournal
open GeneralNominalCenters GeneralNominalCenteredHeadMatStepJournal
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredFrame179 (Agree siteSources site_iff)
open GeneralDictionaryDefault214ActualBodyFrame (classSources class_iff)
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

open GeneralDeclarations GeneralSourceDictionaries
open GeneralDictionaryDefaultKernel208
open GeneralDictionaryDefaultDepth208 (InstalledDepthBound)
open GeneralDictionaryDefault214ActualReadback (Actual actual_same)
open GeneralDictionaryDefault214ActualSupport
open GeneralDictionaryDefault214ActualEffects

 theorem head_capture_subset (plan : Plan roles) :
     GeneralNominalHeadLedgerFrame182.headCaptureSources plan ⊆
       GeneralNominalCenteredFrame179.captureSources plan := by
   intro name member
   obtain ⟨binder,present,within⟩ := List.mem_flatMap.mp member
   exact List.mem_flatMap.mpr ⟨binder,
     (GeneralNominalCenteredFrame179.capture_mem plan binder).mpr (Or.inl present),within⟩

 theorem head_support_actual
     (source : GeneralNominalSourceFormation.InitialSource registry context root)
     (bound : InstalledDepthBound registry context root limit)
     (path : B4Target.Steps (Step registry root) (initial context root) state)
     (plan : Plan roles) (registered : plan ∈ state.core.plans)
     (member : fresh context.state.seed invocation declaration 8 owner position ∈
       GeneralNominalHeadLedgerFrame182.headSources plan) :
     ∃ origin, Actual state (fresh context.state.seed invocation declaration 8 owner position) origin := by
   rcases List.mem_append.mp member with member | member
   · rcases List.mem_append.mp member with input | captures
     · exact site_support_actual source bound path plan.input (registered_input path plan registered) input
     · exact capture_support_actual source bound path plan registered (head_capture_subset plan captures)
   · exact GeneralDictionaryDefault214ActualSupport.head_support_actual source bound path plan registered member

 theorem effect_support_actual
     (source : GeneralNominalSourceFormation.InitialSource registry context root)
     (bound : InstalledDepthBound registry context root limit)
     (path : B4Target.Steps (Step registry root) (initial context root) state)
     (effect : Effect roles) (registered : effect ∈ state.effects)
     (member : fresh context.state.seed invocation declaration 8 owner position ∈ effectSources state effect) :
     ∃ origin, Actual state (fresh context.state.seed invocation declaration 8 owner position) origin := by
   rcases List.mem_append.mp member with member | live
   · rcases List.mem_append.mp member with head | snapshot
     · exact head_support_actual source bound path effect.plan (effect_plan_registered path effect registered) head
     · exact snapshot_support_actual source bound path effect registered snapshot
   · exact live_support_actual source bound path effect registered live

 /-- One historical actual origin is chosen before the model quantifier.
 This does not assert agreement with any new candidate's origin. -/
 theorem uniform_effect_readback
     (source : GeneralNominalSourceFormation.InitialSource registry context root)
     (bound : InstalledDepthBound registry context root limit)
     (path : B4Target.Steps (Step registry root) (initial context root) state)
     (effect : Effect roles) (registered : effect ∈ state.effects)
     (member : fresh context.state.seed invocation declaration 8 owner position ∈ effectSources state effect) :
     ∃ origin, Actual state (fresh context.state.seed invocation declaration 8 owner position) origin ∧
       ∀ model, Models state model → GeneralNominalOriginTerms.Same model origin
         (.source (fresh context.state.seed invocation declaration 8 owner position)) := by
   obtain ⟨origin,producer⟩ := effect_support_actual source bound path effect registered member
   exact ⟨origin,producer,fun _ valid => actual_same valid producer⟩

end Yulang.GeneralDictionaryDefault214ActualJournal
