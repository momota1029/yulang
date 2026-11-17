import Yulang.GeneralNominalRebaseJournalView243
import Yulang.GeneralNominalRebaseEvidenceProjection243
import Yulang.GeneralNominalVersionedSourceCongruence238
set_option backward.isDefEq.respectTransparency false
/-! One replacement preserves the full mixed-source journal AND an entire
recursive dictionary in one internal witness and the same public assignment.
No arbitrary operational step is asserted to satisfy the structural premises. -/
namespace Yulang.GeneralNominalRebaseJournalProjection243
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalFiniteEquationRealization236
open GeneralNominalRebaseEscapedProjection242
open GeneralNominalRebaseEscapedReplace242
open GeneralNominalRebasePublicModel242 (Models)
open GeneralNominalVersionedJournal232 (State)

def Retained (registry : GeneralDeclarations.Registry) (state : State roles)
 (root : GeneralSourceDictionaries.Occurrence roles) (payload : GeneralDictionaryReadback.Payload) (model : Assignment) : Prop :=
 GeneralNominalVersionedJournal232.Models state model ∧
 GeneralNominalVersionedEvidence231.Evidence registry state.core model root payload

theorem retained_congruent (registry : GeneralDeclarations.Registry) (state : State roles)
 (empty : GeneralNominalVersionedMixedRegistry234.LegacyEmpty state)
 (root : GeneralSourceDictionaries.Occurrence roles) (payload : GeneralDictionaryReadback.Payload) :
 GeneralNominalRebaseRawProjection242.Congruent (Retained registry state root payload) := by
 intro first last same
 exact and_congr (GeneralNominalVersionedSourceCongruence238.models_iff same state empty)
   (GeneralNominalRebaseEvidenceProjection243.evidence_congruent registry state.core root payload first last same)

theorem journal_inline (state : State roles)
 (empty : GeneralNominalVersionedMixedRegistry234.LegacyEmpty state)
 (entries : List Entry) (coherent : Coherent entries) (model : Assignment) :
 (GeneralNominalRebaseJournalView243.compile state (GeneralNominalRebaseLookup242.substitution entries)).Models model ↔
 GeneralNominalVersionedJournal232.Models state (patch entries model) := by
 rw [GeneralNominalRebaseJournalView243.compile_exact state empty]
 change GeneralNominalVersionedJournal232.Models state (GeneralNominalRebaseLookup242.patch entries model) ↔ _
 rw [GeneralNominalRebaseLookup242.patch_exact entries coherent model]

theorem public_replacement (oldEntries newEntries : List Entry)
 (oldCoherent : Coherent oldEntries) (oldExternal : External oldEntries)
 (newCoherent : Coherent newEntries) (newExternal : External newEntries)
 (within : TargetsWithin newEntries oldEntries) (hidden : ∀ entry ∈ oldEntries, entry.1 ∈ privateNames)
 (registry : GeneralDeclarations.Registry) (state : State roles)
 (empty : GeneralNominalVersionedMixedRegistry234.LegacyEmpty state)
 (root : GeneralSourceDictionaries.Occurrence roles) (payload : GeneralDictionaryReadback.Payload) (publicModel : Assignment) :
 Models privateNames (fun internal => Definitions oldEntries internal ∧ Retained registry state root payload internal) publicModel ↔
 Models privateNames (fun internal => Definitions newEntries internal ∧
   (GeneralNominalRebaseJournalView243.compile state (GeneralNominalRebaseLookup242.substitution oldEntries)).Models internal ∧
   GeneralNominalRebaseEvidenceView243.Evidence registry state.core
     (GeneralNominalRebaseLookup242.substitution oldEntries) internal root payload) publicModel := by
 have base := GeneralNominalRebasePublicModel242.replacement_models_iff oldEntries newEntries oldCoherent oldExternal
   newCoherent newExternal within hidden _ (retained_congruent registry state empty root payload) publicModel
 simpa only [Models,Retained,← journal_inline state empty oldEntries oldCoherent,
   ← GeneralNominalRebaseEvidenceView243.inline_exact registry state.core oldEntries oldCoherent] using base

theorem point_legacy_empty
 (reachable : B4TargetV8.Reachable (GeneralNominalPointSourceBoundary240.boundary roles) registry root state) :
 GeneralNominalVersionedMixedRegistry234.LegacyEmpty state := by
 apply GeneralNominalVersionedMixedRegistry234.reachable_legacy_empty (value := registry) (root := root)
 obtain ⟨initial,source,path⟩ := reachable
 exact ⟨initial,source,GeneralNominalPointErasure240.steps_old path⟩
end Yulang.GeneralNominalRebaseJournalProjection243
