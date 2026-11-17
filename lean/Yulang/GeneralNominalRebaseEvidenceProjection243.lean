import Yulang.GeneralNominalRebaseEvidenceView243
import Yulang.GeneralNominalRebasePublicModel242
import Yulang.GeneralNominalVersionedEffectCongruence238
set_option backward.isDefEq.respectTransparency false
/-! Same-public-model projection retains the actual whole packet and recursive
certificate judgment. Structural external/coherent/private-target conditions
remain explicit; no reachable-state producer for all of them is claimed. -/
namespace Yulang.GeneralNominalRebaseEvidenceProjection243
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenters (Plan)
open GeneralNominalAssignmentCongruence238 (Same)
open GeneralNominalFiniteEquationRealization236
open GeneralNominalRebaseEscapedProjection242
open GeneralNominalRebaseEscapedReplace242
open GeneralNominalRebaseRawProjection242 (Congruent)
open GeneralNominalRebasePublicModel242 (Models)

 theorem packet_congruent (plan : Plan roles) : Congruent (GeneralNominalVersionedPlans231.Holds plan) :=
 fun _ _ same => GeneralNominalVersionedPacketCongruence238.holds_iff same plan

theorem output_iff (same : Same first last) (plan : Plan roles) (output : GeneralSourceState.Output) :
 GeneralDictionaryDefaultEvidence204.OutputWitness plan first output ↔ GeneralDictionaryDefaultEvidence204.OutputWitness plan last output := by
 apply exists_congr; intro body
 apply and_congr Iff.rfl
 apply and_congr Iff.rfl
 rw [← GeneralNominalVersionedEffects231.body_holds_iff,← GeneralNominalVersionedEffects231.body_holds_iff]
 exact GeneralNominalVersionedEffectCongruence238.body_iff same plan output.target body

theorem certificate_iff (same : Same first last) (registry : GeneralDeclarations.Registry)
 (state : GeneralNominalCenteredSteps.State roles) (root : GeneralSourceDictionaries.Occurrence roles) (key : Nat)
 (children : List (GeneralSourceDictionaries.Occurrence roles)) (plan : Plan roles) :
 GeneralNominalVersionedEvidence231.Certificate registry state first root key children plan ↔
 GeneralNominalVersionedEvidence231.Certificate registry state last root key children plan := by
 constructor
 · intro source
   exact ⟨source.frame,source.children_eq,(packet_congruent plan _ _ same).mp source.packet,
     fun output member => (output_iff same plan output).mp (source.outputs output member)⟩
 · intro source
   exact ⟨source.frame,source.children_eq,(packet_congruent plan _ _ same).mpr source.packet,
     fun output member => (output_iff same plan output).mpr (source.outputs output member)⟩

theorem evidence_congruent (registry : GeneralDeclarations.Registry) (state : GeneralNominalCenteredSteps.State roles)
 (root : GeneralSourceDictionaries.Occurrence roles) (payload : GeneralDictionaryReadback.Payload) :
 Congruent (fun model => GeneralNominalVersionedEvidence231.Evidence registry state model root payload) := by
 intro first last same
 have instances : GeneralNominalVersionedEvidence231.Instance registry state first = GeneralNominalVersionedEvidence231.Instance registry state last := by
   funext demand key children
   apply propext
   exact exists_congr (fun plan => certificate_iff same registry state demand key children plan)
 unfold GeneralNominalVersionedEvidence231.Evidence
 dsimp only
 rw [instances]

theorem packet_public_replacement (oldEntries newEntries : List Entry)
 (oldCoherent : Coherent oldEntries) (oldExternal : External oldEntries)
 (newCoherent : Coherent newEntries) (newExternal : External newEntries)
 (within : TargetsWithin newEntries oldEntries) (hidden : ∀ entry ∈ oldEntries, entry.1 ∈ privateNames)
 (plan : Plan roles) (publicModel : Assignment) :
 Models privateNames (fun internal => Definitions oldEntries internal ∧ GeneralNominalVersionedPlans231.Holds plan internal) publicModel ↔
 Models privateNames (fun internal => Definitions newEntries internal ∧
   (GeneralNominalRebasePacketView243.compile plan (GeneralNominalRebaseLookup242.substitution oldEntries)).Holds internal) publicModel := by
 have exactRead (internal : Assignment) :
   (GeneralNominalRebasePacketView243.compile plan (GeneralNominalRebaseLookup242.substitution oldEntries)).Holds internal ↔
   GeneralNominalVersionedPlans231.Holds plan (patch oldEntries internal) := by
   rw [GeneralNominalRebasePacketView243.compile_exact]
   change GeneralNominalVersionedPlans231.Holds plan (GeneralNominalRebaseLookup242.patch oldEntries internal) ↔ _
   rw [GeneralNominalRebaseLookup242.patch_exact oldEntries oldCoherent internal]
 have base := GeneralNominalRebasePublicModel242.replacement_models_iff oldEntries newEntries oldCoherent oldExternal
   newCoherent newExternal within hidden _ (packet_congruent plan) publicModel
 simpa only [Models,← exactRead] using base

theorem evidence_public_replacement (oldEntries newEntries : List Entry)
 (oldCoherent : Coherent oldEntries) (oldExternal : External oldEntries)
 (newCoherent : Coherent newEntries) (newExternal : External newEntries)
 (within : TargetsWithin newEntries oldEntries) (hidden : ∀ entry ∈ oldEntries, entry.1 ∈ privateNames)
 (registry : GeneralDeclarations.Registry) (state : GeneralNominalCenteredSteps.State roles)
 (root : GeneralSourceDictionaries.Occurrence roles) (payload : GeneralDictionaryReadback.Payload) (publicModel : Assignment) :
 Models privateNames (fun internal => Definitions oldEntries internal ∧
   GeneralNominalVersionedEvidence231.Evidence registry state internal root payload) publicModel ↔
 Models privateNames (fun internal => Definitions newEntries internal ∧
   GeneralNominalRebaseEvidenceView243.Evidence registry state (GeneralNominalRebaseLookup242.substitution oldEntries) internal root payload) publicModel := by
 have base := GeneralNominalRebasePublicModel242.replacement_models_iff oldEntries newEntries oldCoherent oldExternal
   newCoherent newExternal within hidden _ (evidence_congruent registry state root payload) publicModel
 simpa only [Models,← GeneralNominalRebaseEvidenceView243.inline_exact registry state oldEntries oldCoherent] using base
end Yulang.GeneralNominalRebaseEvidenceProjection243
