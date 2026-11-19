import Yulang.GeneralRebaseScopedFrame276

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 26500
set_option maxHeartbeats 9200000
namespace Yulang.GeneralRebaseDisplayStep276
open GeneralNominalExamples (registry context displayRoot displayChild model state_models)
open GeneralDeclarationExamples (roles)
open GeneralRebaseDisplayFrame276 (before after frame effect installation)
open GeneralNominalNonleafPlan193 (plan packet)
open GeneralRebaseDisplaySafety276 (initial_safe initial_positions)
open GeneralNominalVersionedMixedKernel234 (Step Installable AlternativesSafe Committed)
open GeneralNominalVersionedJournal232

theorem alternatives : AlternativesSafe registry before plan.input := by
 intro alternative same framed
 have atRoot : plan.input.occurrence = displayRoot := rfl
 have locatedFrame : GeneralNominalVersionedEvidence231.Frame registry before.core displayRoot
   alternative.packet.declaration.id alternative := atRoot ▸ framed
 have declaration := GeneralRebaseScopedFrame276.declaration_for_focus locatedFrame
   GeneralRebaseDisplayFrame276.wrong_not_prepared
 have raw : alternative.packet.site = plan.packet.site := List.mem_singleton.mp locatedFrame.raw_recorded
 have equality := GeneralRebaseScopedFrame276.same_frame locatedFrame frame declaration raw same
 subst alternative
 exact initial_positions

theorem installable : Installable registry before effect := by
 refine ⟨rfl,rfl,initial_safe,?_,?_,?_,initial_positions,alternatives,model,installation model (state_models true)⟩
 · exact GeneralNominalVersionedMixedObservations233.legacy_cache
     (GeneralDictionaryDefaultCache208.initial_valid (context true) displayRoot)
 · change (GeneralNominalVersionedPlans231.emittedSchema plan).unknown = false
   rw [GeneralRebaseDisplayPacket276.emitted]
 · intro prior appears
   cases appears

theorem novel : ¬ Committed before plan := by
 intro committed
 have impossible := committed.2 displayChild (GeneralRebaseDisplayPacket276.children ▸ List.mem_singleton_self _)
 cases impossible

theorem actual_step : Step registry displayRoot before after :=
 ⟨displayRoot,.root,.install effect installable novel⟩

theorem initial_source : (GeneralNominalVersionedMixedBoundary234.boundary roles).Initial registry displayRoot before :=
 ⟨_,⟨context true,[.app 0 [.app 2 []]],GeneralDictionarySupportRecursiveExample.initial_source,
  (fun _ => rfl),GeneralNominalCenteredCompletionAliasTrace.ground,
  GeneralNominalCenteredHeadWFFixtures.display_coverage,rfl⟩,rfl⟩

theorem reachable :
 B4TargetV8.Reachable (GeneralNominalVersionedMixedBoundary234.boundary roles) registry displayRoot after :=
 ⟨before,initial_source,.tail .refl actual_step⟩

theorem substantive_positive :
 (GeneralNominalVersionedMixedBoundary234.boundary roles).Checked registry ∧
 B4TargetV8.Reachable (GeneralNominalVersionedMixedBoundary234.boundary roles) registry displayRoot after ∧
 GeneralNominalSaturationState.Generated after.core.erased.current displayRoot displayChild ∧
 Models after model ∧
 ∀ m, Models after m → GeneralNominalVersionedEvidence231.Evidence registry after.core m displayRoot (.node 1 [.node 3 []]) :=
 ⟨⟨rfl,GeneralNominalExamples.registry_checked⟩,reachable,GeneralRebaseDisplayFrame276.generated,
   GeneralRebaseDisplaySafety276.after_model,GeneralRebaseDisplayEvidence276.real_nonleaf⟩

end Yulang.GeneralRebaseDisplayStep276
