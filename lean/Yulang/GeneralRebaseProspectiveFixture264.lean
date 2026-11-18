import Yulang.GeneralRebaseProspectiveStep264
import Yulang.GeneralDictionaryCompoundStep238
import Yulang.GeneralNominalVersionedDiagnosticLaws232
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseProspectiveFixture264
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralDictionaryCompoundSource238 (sourceRegistry registry checked declaration)
open GeneralDictionaryCompoundFrame238 (before effect installed frame unique class_effects)
open GeneralDictionaryCompoundPacket238 (plan)
open GeneralDictionaryCompoundVersionedModel238 (extended initial_model)

private theorem request_only (demand : GeneralSourceDictionaries.Occurrence roles)
 (output : GeneralSourceState.Output)
 (member : output ∈ GeneralNominalCenteredHeadOutputs.requests before.core demand) : output = ⟨0,4⟩ := by
 obtain ⟨site,present,_,within⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp member
 cases List.mem_singleton.mp present
 exact List.mem_singleton.mp within

private theorem equal_outputs (demand : GeneralSourceDictionaries.Occurrence roles) :
 GeneralNominalCenteredHeadOutputs.EqualOutputs before.core demand extended := by
 intro first one last two _
 cases request_only demand first one
 cases request_only demand last two
 exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩

theorem selected : GeneralNominalVersionedMixedSourceBoundary234.Local sourceRegistry before root
 (.selected declaration.id (GeneralNominalVersionedFrame231.children plan.packet)) := by
 apply GeneralNominalVersionedMixedSourceBoundary234.local_iff.mpr
 apply GeneralNominalVersionedMixedBoundary234.local_iff.mpr
 exact GeneralNominalVersionedDiagnosticLaws232.selected_of_model
   GeneralDictionaryCompoundStep238.safe unique initial_model frame
   GeneralDictionaryCompoundPacket238.ready GeneralDictionaryCompoundVersionedPacket238.packet_holds
   class_effects (GeneralNominalVersionedMergedConflict232.models_exclude_conflict initial_model
     (fun demand _ => equal_outputs demand) (equal_outputs root))

theorem role_unique : ∀ a ∈ (GeneralNominalCenteredHeadAllocEncoding.registry sourceRegistry).declarations,
 ∀ b ∈ (GeneralNominalCenteredHeadAllocEncoding.registry sourceRegistry).declarations, a.role = b.role → a.id = b.id := by
 intro a one b two _
 cases List.mem_singleton.mp one
 cases List.mem_singleton.mp two
 rfl

/-- The common model is a concrete previously verified assignment, not a new
existential installation-model assumption. -/
theorem residual : GeneralNominalVersionedMixedMaterialization237.Residual before effect extended :=
 (GeneralNominalVersionedMixedMaterialization237.installation_models_iff
   (registry := sourceRegistry) ⟨rfl,checked⟩ GeneralDictionaryCompoundStep238.initial_reachable rfl rfl).mp
   GeneralDictionaryCompoundStep238.installation_models

theorem current : GeneralNominalVersionedMixedCurrentCandidate235.Current registry before root effect :=
 GeneralRebaseProspectiveCurrent264.role_unique_current ⟨rfl,checked⟩
   GeneralDictionaryCompoundStep238.initial_reachable effect rfl rfl selected role_unique ⟨extended,residual⟩

theorem check_success : GeneralRebaseClassCheck261.check plan
 (GeneralRebaseExecutableRequests262.requests before.core root) = .ok () :=
 GeneralRebaseProspectiveCurrent264.source_check ⟨rfl,checked⟩ GeneralDictionaryCompoundStep238.initial_reachable frame

/-- The new prospective chain starts at the actual empty source journal and
performs a genuine guarded installation with a nonempty resulting ledger. -/
theorem nonempty_install :
 before.plans = [] ∧
 (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Step sourceRegistry root before installed ∧
 (∃ model, GeneralNominalVersionedJournal232.Models installed model) ∧ plan ∈ installed.plans :=
 ⟨rfl,GeneralRebaseProspectiveStep264.role_unique_step ⟨rfl,checked⟩
   GeneralDictionaryCompoundStep238.initial_reachable effect rfl rfl selected role_unique ⟨extended,residual⟩
   (.root) GeneralDictionaryCompoundStep238.not_committed⟩
end Yulang.GeneralRebaseProspectiveFixture264
