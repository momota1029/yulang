import Yulang.GeneralRebaseDepthPublic285
import Yulang.GeneralRebaseActualWatch284

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 26000
set_option maxHeartbeats 10000000
namespace Yulang.GeneralRebaseDepthRaw284Bridge285
open GeneralDictionaryOutputDepth252 (plan root registry initial)
open GeneralDictionaryOutputDepthInstall252 (installed effect)
open GeneralRebaseDepthReads285 (actualEquation explicit equation_emitted)
open GeneralNominalRebaseJournalView243 (compile effect)
open GeneralNominalJournalSupport249 (components effectComponents effectReads support)
open GeneralNominalRebaseClassView243 (equations)
open Core.PresenceGeneration (CompTerm)
open GeneralRebaseSliceJournal283 (journalReads)
open GeneralNominalCenteredHeadOutputs (requests request_retained)

theorem live_request : (⟨0,3⟩ : GeneralSourceState.Output) ∈ requests initial.core root :=
  request_retained (GeneralNominalDemandMerging.pointSite root) List.mem_cons_self (.refl _) List.mem_cons_self

theorem body_record :
    actualEquation ∈ (GeneralNominalRebaseJournalView243.effect installed effect CompTerm.var).historical.equations := by
  change actualEquation ∈ equations plan CompTerm.var (requests initial.core root)
  unfold equations
  refine List.mem_flatMap.mpr ⟨⟨0,3⟩,live_request,List.mem_flatMap.mpr ⟨explicit,?_,?_⟩⟩
  · change explicit ∈ (GeneralDictionaryAssociatedProvenance.lookup _ _ 0).toList
    have found : GeneralDictionaryAssociatedProvenance.lookup GeneralDictionaryOutputDepth252.roles plan.packet.declaration 0 = some explicit := rfl
    simp [found]
  · rw [equation_emitted]
    exact List.mem_cons_self

theorem raw_coordinate (n : Nat) (reads : n ∈ ([3,2] : List Nat)) : n ∈ journalReads installed := by
  let j := compile installed CompTerm.var
  let e := GeneralNominalRebaseJournalView243.effect installed effect CompTerm.var
  have member : e ∈ j.effects := by
    change e ∈ installed.effects.map (GeneralNominalRebaseJournalView243.effect installed · CompTerm.var)
    exact List.mem_map.mpr ⟨effect,List.mem_cons_self,rfl⟩
  have classRead : n ∈ GeneralNominalClassSupport249.support e.historical := by
    apply List.mem_append_left
    exact List.mem_flatMap.mpr ⟨actualEquation,body_record,reads⟩
  have effectRead : n ∈ effectReads e :=
    List.mem_flatten.mpr ⟨_,by simp [effectComponents],classRead⟩
  change n ∈ support j
  exact List.mem_flatten.mpr ⟨_,by simp [components],List.mem_flatMap.mpr ⟨e,member,effectRead⟩⟩

theorem raw_not_inputs_only : ¬ journalReads installed ⊆ [0,1,2] :=
  fun covered => by
    have impossible : 3 ∈ ([0,1,2] : List Nat) := covered (raw_coordinate 3 List.mem_cons_self)
    exact (by decide : 3 ∉ ([0,1,2] : List Nat)) impossible

end Yulang.GeneralRebaseDepthRaw284Bridge285
