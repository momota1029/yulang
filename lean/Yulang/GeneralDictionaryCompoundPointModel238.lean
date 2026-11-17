import Yulang.GeneralDictionaryCompoundObstruction238
import Yulang.GeneralNominalVersionedJournalFrame236
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryCompoundPointModel238
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryCompoundSource238
open GeneralDictionaryCompoundPoint238
open GeneralNominalAggregateVersion231
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
abbrev nextName (purpose : Nat) := slot snapshot.seed root.identity declaration.id purpose 0 [(0,2,2),(0,2,2)]
abbrev names (index : Fin 2) := nextName index.val
abbrev pool := GeneralDictionaryCompoundVersionedModel238.pool ++
  [GeneralDictionaryCompoundVersionedModel238.names 0,GeneralDictionaryCompoundVersionedModel238.names 1]
noncomputable def extended : Assignment := GeneralNominalCenteredModelExtension.assign
  GeneralDictionaryCompoundVersionedModel238.extended names (fun _ => .emptyRecord)

theorem outside (index : Fin 2) : names index ∉ pool := by
  have small := index.isLt
  have cases2 : index = 0 ∨ index = 1 := by
    have h : index.val = 0 ∨ index.val = 1 := by omega
    exact h.elim (fun h => Or.inl (Fin.ext h)) (fun h => Or.inr (Fin.ext h))
  rcases cases2 with rfl | rfl <;> decide +kernel

theorem old_value (name : Nat) (member : name ∈ pool) : extended name = GeneralDictionaryCompoundVersionedModel238.extended name :=
  GeneralNominalCenteredModelExtension.assign_outside _ _ _ (fun index same => outside index (same ▸ member))

theorem next_value (index : Fin 2) : (extended (names index)).1 = .emptyRecord :=
  GeneralNominalCenteredModelExtension.assign_value _ _ _ (by intro _ _ _; rfl) index

theorem installed_request (output : GeneralSourceState.Output)
    (member : output ∈ GeneralNominalCenteredHeadOutputs.requests GeneralDictionaryCompoundFrame238.installed.core root) :
    output = ⟨0,4⟩ := by
  have old : output ∈ GeneralNominalCenteredHeadOutputs.requests GeneralDictionaryCompoundFrame238.before.core root :=
    (GeneralNominalVersionedMixedCommon235.requests_iff ⟨rfl,checked⟩
      GeneralDictionaryCompoundStep238.initial_reachable (effect := GeneralDictionaryCompoundFrame238.effect) rfl rfl
      ⟨GeneralNominalDemandMerging.pointSite root,List.mem_singleton_self _,rfl⟩).mp member
  exact GeneralDictionaryCompoundPacket238.request_exact old

theorem class_support (core : GeneralNominalCenteredSteps.State roles)
    (requests : ∀ output ∈ GeneralNominalCenteredHeadOutputs.requests core root, output = ⟨0,4⟩) :
    GeneralDictionaryDefault214ActualBodyFrame.classSources core root GeneralDictionaryCompoundPacket238.plan ⊆ pool := by
  intro name member
  obtain ⟨output,present,member⟩ := List.mem_flatMap.mp member
  cases requests output present
  change name ∈ [4,4] at member
  rcases List.mem_cons.mp member with rfl | member
  · simp [pool,GeneralDictionaryCompoundVersionedModel238.pool]
  · cases List.mem_singleton.mp member
    simp [pool,GeneralDictionaryCompoundVersionedModel238.pool]

theorem support : GeneralNominalVersionedJournalFrame236.sources GeneralDictionaryCompoundFrame238.installed ⊆ pool := by
  intro name member
  unfold GeneralNominalVersionedJournalFrame236.sources at member
  rcases List.mem_append.mp member with old | effects
  · rcases List.mem_append.mp old with legacy | plans
    · exact (by decide +kernel : GeneralDictionaryDefaultJournalSupport213.journalSources
        GeneralDictionaryCompoundFrame238.installed.legacy ⊆ pool) legacy
    · obtain ⟨plan,present,within⟩ := List.mem_flatMap.mp plans
      cases List.mem_singleton.mp present
      exact (by decide +kernel : GeneralNominalVersionedPacketFrame236.sources GeneralDictionaryCompoundPacket238.plan ⊆ pool) within
  · obtain ⟨effect,present,within⟩ := List.mem_flatMap.mp effects
    cases List.mem_singleton.mp present
    unfold GeneralNominalVersionedJournalFrame236.effectSources at within
    rcases List.mem_append.mp within with head | current
    · rcases List.mem_append.mp head with head | old
      · exact (by decide +kernel : GeneralNominalVersionedPacketFrame236.headSources GeneralDictionaryCompoundPacket238.packet ⊆ pool) head
      · exact class_support _ (fun output h => GeneralDictionaryCompoundPacket238.request_exact h) old
    · exact class_support _ installed_request current

theorem model : GeneralNominalVersionedJournal232.Models point extended :=
  (models_iff _).mpr ((GeneralNominalVersionedJournalFrame236.models_iff GeneralDictionaryCompoundFrame238.installed
    (fun name member => (old_value name (support member)).symm)).mp GeneralDictionaryCompoundStep238.installed_model)

end Yulang.GeneralDictionaryCompoundPointModel238
