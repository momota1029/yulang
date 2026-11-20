import Yulang.GeneralNominalReportContext305
import Yulang.GeneralNominalVersionedCandidates231
import Yulang.GeneralDeferredLadderTransport302

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalCandidateReplayModels305
open GeneralNominalRecursiveCandidates (Context report Metadata)
open GeneralNominalReportContext305 (EquivalentContexts model_iff report_exact)
open GeneralNominalReportSourceTransport (moveBounds bindings_preserved selfChecks_preserved)
open GeneralNominalRefinements (Refines)
open GeneralNominalInspection (Bounds)
open GeneralNominalRecursiveInspection (bindings selfChecks ProjectionModels)
open GeneralNominalVersionedCandidates231 (HeadModels privateState inputs)
open GeneralNominalVersionedAllocation231 (Fresh merges)
open GeneralSourceDictionaries (Occurrence)
open GeneralDeclarations (Registry Declaration)
open GeneralNominalCommonBridge (Assignment)
variable {old next : Context}

theorem source_iff (eq : EquivalentContexts old next) (id : Nat) :
    id ∈ GeneralNominalState.sources old.state ↔ id ∈ GeneralNominalState.sources next.state :=
  ⟨GeneralNominalRefinements.sources eq.forward id,GeneralNominalRefinements.sources eq.backward id⟩

theorem allocation_iff (eq : EquivalentContexts old next) (id : GeneralNominalIdentities.Origin) :
    id ∈ old.state.allocated ↔ id ∈ next.state.allocated :=
  ⟨eq.forward.allocated id,eq.backward.allocated id⟩

theorem fresh_iff (eq : EquivalentContexts old next) (r : Registry) (name : Nat)
    (bs : GeneralNominalAllocation.Bindings) :
    Fresh old.state r name bs ↔ Fresh next.state r name bs := by
  unfold Fresh
  simp only [eq.forward.seed,← source_iff eq,← allocation_iff eq]

theorem linked_iff (eq : EquivalentContexts old next) (root : Occurrence roles) :
    GeneralNominalState.Linked old.state root.demand ↔ GeneralNominalState.Linked next.state root.demand :=
  ⟨GeneralNominalRefinements.linked eq.forward _,GeneralNominalRefinements.linked eq.backward _⟩

theorem pending_iff (eq : EquivalentContexts old next) (root : Occurrence roles) :
    GeneralNominalState.RootPending old.state root.demand ↔ GeneralNominalState.RootPending next.state root.demand :=
  ⟨GeneralNominalRefinements.pending_backwards eq.backward _,GeneralNominalRefinements.pending_backwards eq.forward _⟩

theorem metadata_iff (eq : EquivalentContexts old next) (r : Registry) :
    Metadata r old ↔ Metadata r next :=
  ⟨GeneralDictionaryRefinedLocations.metadata old next eq.forward eq.interpretation.symm r,
    GeneralDictionaryRefinedLocations.metadata next old eq.backward eq.interpretation r⟩

theorem bindings_eq (eq : EquivalentContexts old next) (d : Declaration) (bs : List (Bounds old.state)) :
    bindings next.state (report next d (bs.map (moveBounds eq.geometry.slot))) =
      bindings old.state (report old d bs) := by
  rw [report_exact eq]
  exact bindings_preserved eq.geometry.slot eq.geometry.source_eq _

theorem checks_eq (eq : EquivalentContexts old next) (d : Declaration) (bs : List (Bounds old.state)) :
    selfChecks next.state (report next d (bs.map (moveBounds eq.geometry.slot))) =
      selfChecks old.state (report old d bs) := by
  rw [report_exact eq]
  exact selfChecks_preserved eq.geometry.slot eq.geometry.source_eq _

theorem merge_eq (eq : EquivalentContexts old next) (r : Registry) (owner : Nat) (d : Declaration)
    (bs : GeneralNominalAllocation.Bindings) :
    merges next.state r owner d bs = merges old.state r owner d bs := by
  unfold merges
  rw [GeneralDeferredLadderTransport302.capture_seed _ _ eq.forward.seed]

theorem private_iff (eq : EquivalentContexts old next) (r : Registry) (root : Occurrence roles)
    (d : Declaration) (bs : List (Bounds old.state)) (m : Assignment) :
    GeneralNominalState.Models (privateState r old root d bs) m ↔
      GeneralNominalState.Models (privateState r next root d (bs.map (moveBounds eq.geometry.slot))) m := by
  unfold privateState
  rw [GeneralNominalState.extend_models,GeneralNominalState.extend_models,
    GeneralNominalVersionedAllocation231.propagate_models,GeneralNominalVersionedAllocation231.propagate_models,
    bindings_eq eq,checks_eq eq,merge_eq eq,model_iff eq m]

theorem head_model_iff (eq : EquivalentContexts old next) (r : Registry) (root : Occurrence roles)
    (d : Declaration) (bs : List (Bounds old.state)) (m : Assignment) :
    HeadModels r old root d bs m ↔ HeadModels r next root d (bs.map (moveBounds eq.geometry.slot)) m := by
  unfold HeadModels
  rw [private_iff eq,report_exact eq]
  exact and_congr_right (fun _ => (GeneralNominalReportSourceTransport.projections_iff
    eq.geometry.slot eq.geometry.source_eq _ m).symm)

end Yulang.GeneralNominalCandidateReplayModels305
