import Yulang.GeneralMixedReindexObserver305
import Yulang.GeneralMixedIndexedEvidence305
import Yulang.GeneralNominalCatalogueExtension305
import Yulang.GeneralMixedDiagnosticOutputFixture304
import Yulang.GeneralRebaseDepthHaltSelection285

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 26000
set_option maxHeartbeats 13000000
namespace Yulang.GeneralMixedReindexOutputFixture305
open GeneralDictionaryOutputDepth252 (registry root roles initial sourceRegistry)
open GeneralDictionaryOutputDepthInstall252 (installed)
open GeneralRebaseDepthScalar285 (old target cert refreshed from_source present previously_unknown new_zero)
open GeneralNominalCatalogueExtension305 (extend equivalent)
open GeneralNominalVersionedMixedObservations233 (Refresh)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalVersionedRefresh232 (refresh refresh_requests)
open GeneralMixedDiagnosticHead304 (boundary8)
open GeneralNominalCenteredHeadOutputs (requests)

variable (tag : Nat)

noncomputable def wide : GeneralNominalRecursiveCandidates.Context :=
  ⟨extend target.state (.variant tag) (by trivial) (fun i => Fin.elim0 i),target.interpretation⟩

noncomputable def coordinates : GeneralNominalReportContext305.EquivalentContexts target (wide tag) :=
  equivalent target (.variant tag) (by trivial) (fun i => Fin.elim0 i)

noncomputable def wideCert : Refresh installed (wide tag) := by
  let oldR := cert.refines
  refine ⟨⟨oldR.base,oldR.heads,oldR.nominals,oldR.ordinary,
    fun id was => (coordinates tag).forward.known id (oldR.known id was),
    oldR.reserved,oldR.allocated,oldR.seed,oldR.constructors⟩,
    cert.interpretation,cert.support,cert.constraints,?_⟩
  intro observation recorded
  exact ⟨[],[],.source,.source,fun m _ supported =>
    GeneralCanonicalObservations.recorded_sound (wide tag).state m
      ((GeneralNominalReportContext305.model_iff (coordinates tag) m).mp (from_source m supported.1)) recorded⟩

noncomputable def widened := refresh installed (wide tag)

theorem other_refresh : Step registry root installed (widened tag) :=
  ⟨root,.root,.refresh root (wide tag) (wideCert tag) 0 (present 0 (by decide))
    (previously_unknown 0 (by decide)) ((coordinates tag).forward.known 0 new_zero)⟩

theorem other_followup : B4Target.Steps (Step registry root) initial (widened tag) :=
  .tail (.tail .refl GeneralDictionaryOutputDepthInstall252.step) (other_refresh tag)

theorem widened_injective : Function.Injective widened := by
  intro a b same
  have listed := congrArg (fun s : GeneralNominalVersionedJournal232.State roles =>
    List.ofFn s.core.erased.current.context.state.view.shapes) same
  change [GeneralNormalizedObservation.Shape.variant a] = [.variant b] at listed
  exact GeneralNormalizedObservation.Shape.variant.inj (List.cons.inj listed).1

theorem different_successors : refreshed ≠ (widened tag) := by
  intro same
  have bad := congrArg (fun s : GeneralNominalVersionedJournal232.State roles =>
    s.core.erased.current.context.state.view.kinds) same
  change 0 = 1 at bad
  cases bad

theorem requests_both :
    (⟨0,3⟩ : GeneralSourceState.Output) ∈ requests refreshed.core root ∧
      (⟨0,3⟩ : GeneralSourceState.Output) ∈ requests (widened tag).core root := by
  have held := GeneralMixedDiagnosticOutputFixture304.real_install_with_request.2.2
  exact ⟨(refresh_requests installed target).mpr held,(refresh_requests installed (wide tag)).mpr held⟩

theorem diagnostic_exact (front : CommonRoleOutermostResolver.Frontier (GeneralSourceDictionaries.Occurrence roles)) :
    B4TargetV8.Local (boundary8 roles) registry refreshed root front ↔
    B4TargetV8.Local (boundary8 roles) registry (widened tag) root front :=
  GeneralMixedReindexObserver305.local_iff (s := refreshed) (coordinates tag) registry root front

theorem selected_both :
    GeneralNominalVersionedMixedSourceBoundary234.Local sourceRegistry refreshed root (.selected 0 []) ∧
    GeneralNominalVersionedMixedSourceBoundary234.Local sourceRegistry (widened tag) root (.selected 0 []) := by
  have yes := GeneralRebaseDepthHaltSelection285.selected
  refine ⟨yes,?_⟩
  apply GeneralNominalVersionedMixedSourceBoundary234.local_iff.mpr
  apply GeneralNominalVersionedMixedBoundary234.local_iff.mpr
  apply ((diagnostic_exact tag) _).mp
  exact GeneralNominalVersionedMixedBoundary234.local_iff.mp
    (GeneralNominalVersionedMixedSourceBoundary234.local_iff.mp yes)

theorem evidence_exact (m : GeneralNominalCommonBridge.Assignment) (p : GeneralDictionaryReadback.Payload) :
    GeneralNominalVersionedEvidence231.Evidence registry refreshed.core m root p ↔
      GeneralNominalVersionedEvidence231.Evidence registry (widened tag).core m root p :=
  GeneralMixedIndexedEvidence305.evidence_iff
    (GeneralMixedReindexObserver305.indexed (s := refreshed) (coordinates tag)) registry m root p

theorem checked_deep_payload (m : GeneralNominalCommonBridge.Assignment)
    (p : GeneralDictionaryReadback.Payload) :
    GeneralNominalVersionedJournal232.Models (widened tag) m ∧
      GeneralNominalVersionedEvidence231.Evidence registry (widened tag).core m root p ↔
    GeneralRebaseDepthGroundModels285.FinalTypeCheck m ∧ p = .node 0 [] := by
  exact (and_congr (GeneralMixedReindexObserver305.models_iff (s := refreshed) (coordinates tag) m).symm
    ((evidence_exact tag) m p).symm).trans (GeneralRebaseDepthHaltEvidence285.evidence_payload m p)

end Yulang.GeneralMixedReindexOutputFixture305
