import Yulang.GeneralRebasePrivateObserved282

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebasePrivateJournal282
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable)
open GeneralRebaseMixedOwnedTrace277 (raw)
open GeneralRebasePrivateKey282 (port)
open GeneralRebasePrivateTrace282 (historical frame_safe raw_outputs_safe sites_safe)
open GeneralRebasePrivateObserved282 (observations observed_private source_private)
open GeneralRebasePrivateSchema282 (site_private)
open GeneralRebasePrivatePacket282 (Safe sources_private head_sources_private)
open GeneralRebasePrivateClass282 (class_private)
open GeneralNominalVersionedJournalFrame236 (sources effectSources)
open GeneralRebaseAggregateTags281 (Tag)
open GeneralNominalCommonBridge (Assignment)

variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles} {state : State roles}

def Hidden (seed : Nat) (id : Nat) : Prop := ∃ (owner decl : Nat) (tag : Tag), id = port seed owner decl tag

def AgreeOutside (seed : Nat) (first last : Assignment) : Prop :=
    ∀ id, ¬ Hidden seed id → first id = last id

theorem request_safe (reach : Reachable registry root state) (owner decl : Nat) (tag : Tag)
    (focus : Occurrence roles) (out : GeneralSourceState.Output)
    (listed : out ∈ GeneralNominalCenteredHeadOutputs.requests state.core focus) :
    port (raw state).seed owner decl tag ≠ out.target := by
  obtain ⟨site,member,_,used⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp listed
  exact raw_outputs_safe reach owner decl tag site member out used

theorem effect_context (reach : Reachable registry root state) {eff : Effect roles}
    (listed : eff ∈ state.effects) :
    ∃ prior, Reachable registry root prior ∧ eff.snapshot = prior.core ∧
      eff.plan.packet.context.state.seed = (raw prior).seed ∧ (raw prior).seed = (raw state).seed := by
  obtain ⟨prior,path,snap,seed⟩ := (historical reach).2 eff listed
  refine ⟨prior,path,snap,?_,seed⟩
  exact congrArg (fun c : GeneralNominalCandidates.Context => c.state.seed)
    (eff.frame.context_eq.trans (congrArg (fun c : GeneralNominalCenteredSteps.State roles =>
      c.erased.current.context) snap))

theorem plan_private (reach : Reachable registry root state) (owner decl : Nat) (tag : Tag)
    (p : Plan roles) (listed : p ∈ state.plans) :
    port (raw state).seed owner decl tag ∉ GeneralNominalVersionedPacketFrame236.sources p := by
  obtain ⟨eff,member,rfl⟩ := (historical reach).1 p listed
  obtain ⟨earlier,path,snap,first,last⟩ := effect_context reach member
  have frame := eff.frame
  rw [snap] at frame
  rw [← first.trans last]
  exact sources_private (frame_safe path frame owner decl tag)

theorem effect_private (reach : Reachable registry root state) (owner decl : Nat) (tag : Tag)
    (eff : Effect roles) (listed : eff ∈ state.effects) :
    port (raw state).seed owner decl tag ∉ effectSources state eff := by
  obtain ⟨earlier,path,snap,first,last⟩ := effect_context reach listed
  have frame := eff.frame
  rw [snap] at frame
  have safe := frame_safe path frame owner decl tag
  intro found
  rw [← first.trans last] at found
  rcases List.mem_append.mp found with historic|live
  · rcases List.mem_append.mp historic with head|body
    · exact head_sources_private eff.plan safe.visible safe.excludes head
    · apply class_private safe eff.snapshot eff.plan.packet.site.occurrence ?_ body
      intro out requested
      rw [first]
      exact request_safe path owner decl tag _ out (snap ▸ requested)
  · apply class_private safe state.core eff.plan.packet.site.occurrence ?_ live
    intro out requested
    rw [first,last]
    exact request_safe reach owner decl tag _ out requested

theorem legacy_private (reach : Reachable registry root state) (owner decl : Nat) (tag : Tag) :
    port (raw state).seed owner decl tag ∉ GeneralDictionaryDefaultJournalSupport213.journalSources state.legacy := by
  have empty := GeneralNominalVersionedMixedRegistry234.reachable_legacy_empty reach
  unfold GeneralDictionaryDefaultJournalSupport213.journalSources
  rw [empty.1,empty.2]
  simp only [List.flatMap_nil,List.append_nil]
  intro found
  rcases List.mem_append.mp found with old | center
  · rcases List.mem_append.mp old with raw | obs
    · rcases List.mem_append.mp raw with now|source
      · exact GeneralRebaseFixedOrigin281.fixed_absent owner decl tag reach
          (GeneralDictionaryDefaultRawSupport213.subset _ now)
      · exact source_private reach owner decl tag (GeneralDictionaryDefaultRawSupport213.subset _ source)
    · obtain ⟨site,seen,origin⟩ := List.mem_flatMap.mp obs
      rw [observations reach] at seen
      obtain ⟨actual,member,rfl⟩ := List.mem_map.mp seen
      exact observed_private (sites_safe reach owner decl tag actual member) origin
  · obtain ⟨site,used,hit⟩ := List.mem_flatMap.mp center
    exact site_private (sites_safe reach owner decl tag site used) hit

theorem journal_private (reach : Reachable registry root state) (owner decl : Nat) (tag : Tag) :
    port (raw state).seed owner decl tag ∉ sources state := by
  intro found
  rcases List.mem_append.mp found with old | effects
  · rcases List.mem_append.mp old with legacy|plans
    · exact legacy_private reach owner decl tag legacy
    · obtain ⟨plan,member,used⟩ := List.mem_flatMap.mp plans
      exact plan_private reach owner decl tag plan member used
  · obtain ⟨eff,member,used⟩ := List.mem_flatMap.mp effects
    exact effect_private reach owner decl tag eff member used

theorem models_iff (reach : Reachable registry root state) {a b : Assignment}
    (same : AgreeOutside (raw state).seed a b) :
    Models state a ↔ Models state b :=
  GeneralNominalVersionedJournalFrame236.models_iff state (fun n used => same n (by
    rintro ⟨owner,decl,tag,rfl⟩
    exact journal_private reach owner decl tag used))

end Yulang.GeneralRebasePrivateJournal282
