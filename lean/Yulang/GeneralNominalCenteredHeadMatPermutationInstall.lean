import Yulang.GeneralNominalCenteredHeadMatPermutationAdministrative

set_option backward.isDefEq.respectTransparency false

/-! Installation extends a coherent plan table. A repeated raw packet may
carry different centers; novelty is therefore checked on complete plans. -/
namespace Yulang.GeneralNominalCenteredHeadMatPermutationInstall
open GeneralDeclarations GeneralSourceDictionaries GeneralRegistryReordering GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal
open GeneralNominalCenteredHeadMatStepKernel
open GeneralNominalCenteredHeadMatPermutationRaw
open GeneralNominalCenteredHeadMatPermutationPlans (Pair)
open GeneralNominalCenteredHeadMatPermutationLedger
open GeneralNominalCenteredHeadMatPermutationLocal (frame_counterpart)
open GeneralNominalLedgerPermutation (All₂)
variable {roles : Roles.RoleDecls} {relation : Plan roles → Plan roles → Prop} {first last : State roles}

theorem core_installed {first last : GeneralNominalCenteredSteps.State roles} (same : Core first last) (pair : Pair plan other) :
    Core (installCore first plan) (installCore last other) := by
  refine ⟨⟨pair.privateContexts,.cons pair.matched.packet.toPacketPair same.current.packets,?_,?_,same.current.aliases⟩,
    same.source,?_,same.roots⟩
  · intro site
    change site ∈ first.erased.current.sites ++ plan.emitted.map Site.observed ↔
      site ∈ last.erased.current.sites ++ other.emitted.map Site.observed
    simp only [List.mem_append,List.mem_map,same.current.sites,pair.emitted]
  · change first.erased.current.edges ++ plan.packet.children.map _ = last.erased.current.edges ++ other.packet.children.map _
    rw [same.current.edges,pair.matched.packet.children,pair.matched.packet.site]
  · intro site
    change site ∈ first.sites ++ plan.emitted ↔ site ∈ last.sites ++ other.emitted
    simp only [List.mem_append,same.centers,pair.emitted]

def Extend (relation : Plan roles → Plan roles → Prop) (plan other : Plan roles) (a b : Plan roles) : Prop :=
  (a = plan ∧ b = other) ∨ relation a b

theorem coherent_extended (same : Related relation first last)
    (oneNew : plan ∉ first.core.plans) (twoNew : other ∉ last.core.plans) : Coherent (Extend relation plan other) := by
  refine ⟨?_,?_⟩
  · intro a b c one two
    rcases one with ⟨rfl,rfl⟩ | one
    · rcases two with ⟨_,rfl⟩ | two
      · rfl
      · exact False.elim (oneNew (same.recorded _ _ two).1)
    · rcases two with ⟨rfl,rfl⟩ | two
      · exact False.elim (oneNew (same.recorded _ _ one).1)
      · exact same.coherent.left one two
  · intro a b c one two
    rcases one with ⟨rfl,rfl⟩ | one
    · rcases two with ⟨rfl,_⟩ | two
      · rfl
      · exact False.elim (twoNew (same.recorded _ _ two).2)
    · rcases two with ⟨rfl,rfl⟩ | two
      · exact False.elim (twoNew (same.recorded _ _ one).2)
      · exact same.coherent.right one two

theorem installed_related (same : Related relation first last) (one : a.snapshot = first.core) (two : b.snapshot = last.core)
    (pair : Pair a.plan b.plan) (oneNew : a.plan ∉ first.core.plans) (twoNew : b.plan ∉ last.core.plans) :
    Related (Extend relation a.plan b.plan) (install first a) (install last b) := by
  refine ⟨core_installed same.core pair,coherent_extended same oneNew twoNew,?_,?_,?_,?_,?_⟩
  · intro p q marked
    rcases marked with ⟨rfl,rfl⟩ | marked
    · exact ⟨List.mem_cons_self ..,List.mem_cons_self ..⟩
    · exact ⟨List.mem_cons_of_mem _ (same.recorded p q marked).1,List.mem_cons_of_mem _ (same.recorded p q marked).2⟩
  · exact .cons ⟨Or.inl ⟨rfl,rfl⟩,pair⟩ (all_mono (fun _ _ pair => ⟨Or.inr pair.1,pair.2⟩) same.plans)
  · exact .cons ⟨⟨Or.inl ⟨rfl,rfl⟩,pair⟩,one.symm ▸ two.symm ▸ same.core.snapshot⟩
      (all_mono (fun _ _ pair => ⟨⟨Or.inr pair.plan.1,pair.plan.2⟩,pair.snapshot⟩) same.effects)
  · intro plan member
    rcases List.mem_cons.mp member with rfl | member
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (same.packetsLeft plan member)
  · intro plan member
    rcases List.mem_cons.mp member with rfl | member
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (same.packetsRight plan member)

theorem choice_forward (same : Raw left right) (pair : GeneralNominalJournalPermutation.PacketPair packet other)
    (valid : GeneralNominalCycleSteps.ChoiceCompatible left packet) : GeneralNominalCycleSteps.ChoiceCompatible right other := by
  intro prior member alias
  obtain ⟨old,present,paired⟩ := same.packet_right member
  rw [← pair.identity,← paired.identity]
  apply valid old present
  apply (same.alias _ _).mpr
  rwa [pair.site,paired.site]

theorem committed (same : Related relation first last) (pair : Pair plan other) :
    Committed first plan ↔ Committed last other := by
  simp only [Committed,same.models,pair.holds,pair.matched.packet.children,
    pair.matched.packet.site,same.core.current.edges]

theorem counterpart_enabled (same : Related relation first last) (order : Reorders registry otherRegistry)
    (roleEq : registry.roles = roles) (enabled : Installable registry first effect) :
    ∃ other : Effect roles, Installable otherRegistry last other ∧ Pair effect.plan other.plan ∧
      other.snapshot = last.core := by
  have frame := enabled.snapshot_eq ▸ enabled.registry_eq ▸ effect.frame
  obtain ⟨plan,otherFrame,pair⟩ := frame_counterpart same.core order roleEq frame
  have rootEq := congrArg GeneralNominalDemandMerging.Site.occurrence pair.matched.packet.site
  have selected := installable_selected enabled
  have moved := (GeneralNominalCenteredHeadMatPermutationLocal.local_iff same registry roleEq _ _).mp selected
  have reordered := (GeneralNominalCenteredHeadMatStepOrder.local_iff order last _ _).mp (GeneralNominalCenteredHeadMatStepBoundary.local_iff.mpr moved)
  have selection : GeneralNominalCenteredHeadMatStepBoundary.Local otherRegistry last plan.packet.site.occurrence
      (.selected plan.packet.declaration.id plan.packet.children) := by
    simpa only [rootEq,pair.matched.packet.identity,pair.matched.packet.children] using reordered
  have ready : GeneralNominalCenteredHeadMatEffects.Ready last.core plan.packet.site.occurrence plan := by
    have old := enabled.snapshot_eq ▸ effect.ready
    have moved := (pair.ready first.core effect.plan.packet.site.occurrence).mp old
    rw [rootEq] at moved
    exact (same.core.snapshot.ready _ plan).mp moved
  have frame' : GeneralNominalCenteredHeadOutputs.Frame otherRegistry last.core plan.packet.site.occurrence
      plan.packet.declaration.id plan := rootEq ▸ pair.matched.packet.identity ▸ otherFrame
  cases selection with
  | selected safe unique clear =>
      let other : Effect roles := ⟨otherRegistry,last.core,plan,frame',unique,ready⟩
      have effectPair : EffectPair (fun _ _ => True) effect other :=
        ⟨⟨True.intro,pair⟩,enabled.snapshot_eq.symm ▸ same.core.snapshot⟩
      have nextCore := core_installed same.core pair
      have common : ∃ model, InstallationModels last other model := by
        obtain ⟨model,valid,branch,recorded,live,prior⟩ := enabled.common
        refine ⟨model,(same.models model).mp valid,(pair.holds model).mp branch,
          (effectPair.holds model).mp recorded,(effectPair.live nextCore.snapshot model).mp live,?_⟩
        intro effect member
        obtain ⟨old,present,paired⟩ := GeneralNominalLedgerPermutation.all₂_right same.effects member
        exact (paired.live nextCore.snapshot model).mp (prior old present)
      have chosen : GeneralNominalCenteredHeadMatStepBoundary.Local otherRegistry last plan.packet.site.occurrence
          (.selected plan.packet.declaration.id plan.packet.children) := .selected safe unique clear
      have cache := (same.cache first.core.erased.current.context.state).mp enabled.cache
      have cache := (GeneralNominalCenteredHeadMatPermutationAdministrative.cache_snapshot same.core.current.context.state last).mp cache
      refine ⟨other,⟨rfl,rfl,safe,cache,?_,choice_forward same.core.current pair.matched.packet.toPacketPair enabled.choice,
        GeneralNominalCenteredHeadMatStepAvailability.selected_safe chosen frame',?_,common⟩,pair,rfl⟩
      · change (GeneralNominalCenteredHeadMatPlans.emittedSchema plan).unknown = false
        rw [← pair.schema]; exact enabled.materialized
      · exact GeneralNominalCenteredHeadMatStepAvailability.selected_alternatives (plan.input_exact.symm ▸ chosen)

end Yulang.GeneralNominalCenteredHeadMatPermutationInstall
