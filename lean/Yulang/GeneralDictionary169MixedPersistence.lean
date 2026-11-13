import Yulang.GeneralDictionary169RelocationComposition
import Yulang.GeneralDictionary169LeafPersistence
import Yulang.GeneralDictionarySharedTrustTransport
import Yulang.GeneralDictionarySharedEvidenceTrace

/-! Mixed certificates, including unrecorded structural leaves, survive real
Shared ordinary continuations. No semantic Instance/Evidence is an input. -/
namespace Yulang.GeneralDictionary169MixedPersistence
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport
open GeneralDictionaryReadback (Payload)
open GeneralDictionaryMixed168Tree (MixedTree)
open CommonRoleOutermostResolver (All₂)
variable {roles : Roles.RoleDecls}

theorem packets_steps {registry : Registry} {root : Occurrence roles} {before after : Tracked roles}
    (path : B4Target.Steps (GeneralNominalSharedSteps.Step registry root) before after) :
    ∀ packet ∈ before.current.packets, packet ∈ after.current.packets := by
  induction path with
  | refl => exact fun _ member => member
  | tail prior step ih =>
    obtain ⟨focus,_,update⟩ := step
    exact fun packet member => GeneralDictionarySharedTrustTransport.at_packets update packet (ih packet member)

theorem extension {registry : Registry} {before after : Tracked roles}
    (members : ∀ packet ∈ before.current.packets, packet ∈ after.current.packets)
    (growth : GeneralDictionaryOrdinaryTrace.Extension before.current.context after.current.context)
    (tree : MixedTree registry before occurrence payload) :
    MixedTree registry after occurrence payload := by
  induction tree using MixedTree.rec
    (motive_2 := fun sites payloads _ => All₂ (MixedTree registry after) sites payloads) with
  | recorded packet member relocation payloads children ih =>
    exact .recorded packet (members packet member)
      (GeneralDictionary169RelocationComposition.packet_extension registry before after packet relocation growth) payloads ih
  | scalar occurrence declaration visible checked shape =>
    obtain ⟨reserved,atoms,allocated,equal⟩ := growth
    apply MixedTree.scalar occurrence declaration visible checked
    rw [equal]
    exact GeneralDictionary169LeafPersistence.scalar before.current.context reserved atoms allocated shape
  | spine occurrence declaration visible checked shape =>
    obtain ⟨reserved,atoms,allocated,equal⟩ := growth
    apply MixedTree.spine occurrence declaration visible checked
    rw [equal]
    exact GeneralDictionary169LeafPersistence.nominal before.current.context reserved atoms allocated shape
  | nil => exact .nil
  | cons one rest ihOne ihRest => exact .cons ihOne ihRest

theorem ordinary_steps {registry : Registry} {root : Occurrence roles} {before after : Tracked roles}
    (path : B4Target.Steps (GeneralDictionarySharedEvidenceTrace.OrdinaryStep registry root) before after)
    (tree : MixedTree registry before occurrence payload) :
    MixedTree registry after occurrence payload :=
  extension (packets_steps (GeneralDictionarySharedEvidenceTrace.ordinary_trace_real _ _ _ _ path))
    (GeneralDictionarySharedEvidenceTrace.ordinary_trace_extension _ _ _ _ path) tree

/-- Only the final source-formed state and its current model interpret the
persisted certificate; no initial semantic dictionary is required. -/
theorem current_evidence {registry : Registry} {root : Occurrence roles} {before after : Tracked roles}
    (path : B4Target.Steps (GeneralDictionarySharedEvidenceTrace.OrdinaryStep registry root) before after)
    (formed : GeneralNominalSharedSteps.SourceFormed registry root after)
    (tree : MixedTree registry before occurrence payload)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models after.current model) :
    GeneralDictionaryRecursiveEvidence.Evidence registry after.current.context model occurrence payload :=
  GeneralDictionaryMixed168Tree.current_evidence formed (ordinary_steps path tree) model valid
end Yulang.GeneralDictionary169MixedPersistence

namespace Yulang.GeneralDictionary169MixedPersistence
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState GeneralNominalSupport
open GeneralDictionaryMixed168Tree (MixedTree)
variable {roles : Roles.RoleDecls}

theorem source_formed_steps {registry : Registry} {root : Occurrence roles} {before after : Tracked roles}
    (path : B4Target.Steps (GeneralNominalSharedSteps.Step registry root) before after)
    (formed : GeneralNominalSharedSteps.SourceFormed registry root before) :
    GeneralNominalSharedSteps.SourceFormed registry root after := by
  induction path with
  | refl => exact formed
  | tail prior step ih => exact .update ih step

theorem source_dictionary_steps {registry : Registry} {root : Occurrence roles} {before after : Tracked roles}
    (path : B4Target.Steps (GeneralDictionarySharedEvidenceTrace.OrdinaryStep registry root) before after)
    (formed : GeneralNominalSharedSteps.SourceFormed registry root before)
    (tree : MixedTree registry before occurrence payload) :
    MixedTree registry after occurrence payload ∧
    ∀ model, Models after.current model →
      GeneralDictionaryRecursiveEvidence.Evidence registry after.current.context model occurrence payload :=
  ⟨ordinary_steps path tree, fun model valid => current_evidence path
    (source_formed_steps (GeneralDictionarySharedEvidenceTrace.ordinary_trace_real _ _ _ _ path) formed)
    tree model valid⟩
end Yulang.GeneralDictionary169MixedPersistence
