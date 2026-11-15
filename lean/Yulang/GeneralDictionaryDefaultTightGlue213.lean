import Yulang.GeneralDictionaryDefaultJournalSupport213
import Yulang.GeneralDictionaryDefaultModelGlue212
import Yulang.GeneralDictionaryDefaultAvailability208

/-! Exact common-model reduction to agreement on a finite overlap. The two
witnesses are not silently identified. No reachability or syntax restriction
is needed for the support theorem; compatibility remains explicit. -/
namespace Yulang.GeneralDictionaryDefaultTightGlue213
open GeneralNominalCenters GeneralNominalCenteredHeadMatStepJournal
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredFrame179 (Agree)
open GeneralDictionaryDefaultJournalSupport213 (journalSources models_iff)
open GeneralDictionaryDefaultPacketSupport213 (packetSources packet_iff)
open GeneralDictionaryDefaultModeEffects213 (classSources class_iff)
variable {roles : Roles.RoleDecls} {first last : Assignment}

 noncomputable def localSources (effect : Effect roles) : List Nat :=
  packetSources effect.plan ++ GeneralNominalHeadLedgerFrame182.headSources effect.plan ++
    classSources effect.snapshot effect.plan.packet.site.occurrence effect.plan

 theorem local_iff (effect : Effect roles) (same : Agree (localSources effect) first last) :
    (GeneralNominalCenteredHeadMatStepPackets.Holds effect.plan first ∧ effect.Holds first) ↔
    (GeneralNominalCenteredHeadMatStepPackets.Holds effect.plan last ∧ effect.Holds last) := by
  apply and_congr (packet_iff _ (fun name member => same name (by simp [localSources,member])))
  exact and_congr
    (GeneralNominalHeadLedgerFrame182.head_iff _ (fun name member => same name (by simp [localSources,member])))
    (class_iff _ _ _ (fun name member => same name (by simp [localSources,member])))

open GeneralDictionaryDefaultModelGlue212 (splice splice_keeps splice_agrees)

 theorem common_of_overlap (state : State roles) (effect : Effect roles)
    (journal : Models state first)
    (localModel : GeneralNominalCenteredHeadMatStepPackets.Holds effect.plan last ∧ effect.Holds last)
    (overlap : ∀ name ∈ journalSources state, name ∈ localSources effect → first name = last name) :
    ∃ model, Models state model ∧
      GeneralNominalCenteredHeadMatStepPackets.Holds effect.plan model ∧ effect.Holds model := by
  let model := splice (journalSources state) first last
  exact ⟨model,(models_iff state (splice_keeps _ first last)).mp journal,
    (local_iff effect (splice_agrees _ _ first last overlap)).mp localModel⟩

 theorem common_iff_overlap (state : State roles) (effect : Effect roles) :
    (∃ model, Models state model ∧
      GeneralNominalCenteredHeadMatStepPackets.Holds effect.plan model ∧ effect.Holds model) ↔
    ∃ first last, Models state first ∧
      (GeneralNominalCenteredHeadMatStepPackets.Holds effect.plan last ∧ effect.Holds last) ∧
      ∀ name ∈ journalSources state, name ∈ localSources effect → first name = last name := by
  constructor
  · rintro ⟨model,journal,packet,effects⟩
    exact ⟨model,model,journal,⟨packet,effects⟩,fun _ _ _ => rfl⟩
  · rintro ⟨first,last,journal,localModel,overlap⟩
    exact common_of_overlap state effect journal localModel overlap

 theorem disjoint_common (state : State roles) (effect : Effect roles)
    (separate : ∀ name ∈ journalSources state, name ∉ localSources effect)
    (journal : ∃ model, Models state model)
    (localModel : ∃ model, GeneralNominalCenteredHeadMatStepPackets.Holds effect.plan model ∧ effect.Holds model) :
    ∃ model, Models state model ∧
      GeneralNominalCenteredHeadMatStepPackets.Holds effect.plan model ∧ effect.Holds model := by
  obtain ⟨first,valid⟩ := journal
  obtain ⟨last,held⟩ := localModel
  exact common_of_overlap state effect valid held (fun name one two => False.elim (separate name one two))

/-- This is a sufficient gluing interface, not a proof that selected nodes
have compatible overlap witnesses. It feeds the existing exact installability API. -/
 theorem installable_of_overlap
    (checked : (GeneralDictionaryDefaultBoundary208.boundary roles).Checked value)
    (reachable : B4TargetV7.Reachable (GeneralDictionaryDefaultBoundary208.boundary roles) value root state)
    (selected : GeneralDictionaryDefaultBoundary208.Local value state effect.plan.packet.site.occurrence
      (.selected effect.plan.packet.declaration.id children))
    (registryEq : effect.registry = GeneralNominalCenteredHeadAllocEncoding.registry value)
    (snapshot : effect.snapshot = state.core)
    (choice : GeneralNominalCycleSteps.ChoiceCompatible state.core.erased.current effect.plan.packet)
    (journal : Models state first)
    (localModel : GeneralNominalCenteredHeadMatStepPackets.Holds effect.plan last ∧ effect.Holds last)
    (overlap : ∀ name ∈ journalSources state, name ∈ localSources effect → first name = last name) :
    GeneralDictionaryDefaultKernel208.Installable (GeneralNominalCenteredHeadAllocEncoding.registry value) state effect :=
  (GeneralDictionaryDefaultAvailability208.selected_installable_iff checked reachable selected registryEq snapshot).mpr
    ⟨choice,common_of_overlap state effect journal localModel overlap⟩

end Yulang.GeneralDictionaryDefaultTightGlue213
