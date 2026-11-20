import Yulang.GeneralRebaseDepthHaltEvidence285
import Yulang.GeneralRebaseInstalledOutputCycles271
import Yulang.GeneralNominalVersionedDiagnosticLaws232

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 12500000
namespace Yulang.GeneralRebaseDepthHaltSelection285
open GeneralDictionaryOutputDepth252 (registry root roles declaration declaration_checked sourceRegistry model)
open GeneralDictionaryOutputDepthInstall252 (installed installed_model smallModel small_source form form_value)
open GeneralRebaseDepthScalar285 (target refreshed fixed_models from_source)
open GeneralRebaseDepthCommit285 (finalPlan raw_sites center_sites no_edges located classes committed)
open GeneralRebaseDepthHaltEvidence285 (final_prepared final_ready final_frame final_children evidence_payload final_models)
open GeneralNominalVersionedCandidates231 (Survivor Unique survivor_children_functional)
open GeneralNominalVersionedJournal232 (Models)
open CommonNominalFullCarrier (Equivalent subtype_trans)
open GeneralDictionaryOutputDepthCycles252 (Form nominal_child equivalent_rank)
open GeneralNominalRecursiveInspection (Observes)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)

theorem raw_edge {a b : Fin target.state.base.slots}
    (edge : GeneralNominalMixedRecurrence.Edge target.state a b) : (form b.val).rank < (form a.val).rank := by
  rcases edge with structural | nominal
  · obtain ⟨kind,_⟩ := structural
    exact Fin.elim0 kind
  · obtain ⟨descriptor,recorded,index,actual,seen,same⟩ :=
      GeneralNominalMixedRecurrence.actual_edge_sound target.state a b nominal smallModel (from_source _ small_source)
    have observation := GeneralNominalRecursiveInspection.embed_observation smallModel _ actual seen
    cases observation with
    | nominal parent equal found =>
      cases parent
      change Equivalent (smallModel a.val).1 _ at equal
      rw [form_value] at equal
      obtain ⟨child,smaller,meaning⟩ := nominal_child (form a.val) equal found
      change Equivalent actual (smallModel b.val).1 at same
      rw [form_value] at same
      have ranks := equivalent_rank child (form b.val)
        ⟨subtype_trans meaning.2 same.1,subtype_trans same.2 meaning.1⟩
      omega

theorem raw_acyclic (slot : Fin target.state.base.slots) : ¬ GeneralNominalCycleK2.RecursAt target.state slot := by
  have paths : ∀ a b, GeneralNominalMixedRecurrence.Path target.state a b → (form b.val).rank ≤ (form a.val).rank := by
    intro a b path
    induction path with
    | nil => exact Nat.le_refl _
    | cons edge path ih => exact Nat.le_trans ih (Nat.le_of_lt (raw_edge edge))
  intro cycle
  obtain ⟨next,edge,path⟩ := GeneralNominalCycleK2.recurs_cycle _ _ cycle
  have down := raw_edge edge
  have same := paths _ _ path
  omega

theorem semantic_acyclic (o) : ¬ GeneralNominalVersionedCycles232.Cyclic refreshed o := by
  have modelEq : Models refreshed = Models installed := funext fun m => propext (fixed_models m)
  exact fun denied => GeneralRebaseInstalledOutputCycles271.no_cycle _
    ((GeneralNominalVersionedCycles232.full_models_only modelEq).mp denied)

theorem after_model : Models refreshed model := (fixed_models model).mpr installed_model

theorem known : ¬ GeneralNominalState.RootPending target.state root.demand := by
  rintro ⟨_,missing⟩
  exact missing GeneralRebaseDepthTerminalFrame285.known_two

theorem administrative : GeneralNominalVersionedDiagnostic232.AdministrativeReady refreshed root := by
  constructor
  · exact ⟨_,center_sites ▸ List.mem_cons_self,rfl⟩
  · intro a was _ b appears _
    rw [center_sites] at was appears
    cases List.mem_singleton.mp was
    cases List.mem_singleton.mp appears
    exact .refl _

theorem safe : B4TargetV8.SafeKnown (GeneralNominalVersionedDiagnostic232.boundary roles)
    registry refreshed root := by
 refine ⟨known,?_,?_,?_⟩
 · rintro (raw | (⟨i,cyclic⟩ | ⟨site,_,_,i,cyclic⟩))
   · obtain ⟨_,_,_,slot,_,cyclic⟩ := raw
     exact raw_acyclic slot cyclic
   · exact semantic_acyclic _ cyclic
   · exact semantic_acyclic _ cyclic
 · rintro (raw | ⟨p,_,entry,member,cyclic⟩)
   · obtain ⟨_,_,_,_,_,_,_,_,visited,_,cyclic⟩ := raw
     exact raw_acyclic visited.1 cyclic
   · exact semantic_acyclic _ cyclic
 · rintro (⟨_,d,visible,role,_,unprepared⟩ | unclosed)
   · cases List.mem_singleton.mp visible
     exact unprepared final_prepared
   · exact unclosed administrative

theorem survivor : Survivor registry target root 0 [] := by
 refine ⟨known,declaration,List.mem_cons_self,declaration_checked,rfl,rfl,
   finalPlan.packet.bounds,located,final_prepared,?_⟩
 exact final_children.symm

theorem unique : Unique registry target root 0 [] := by
  refine ⟨survivor,?_⟩
  intro key children other
  have other_copy := other
  obtain ⟨_,d,visible,_,ident,_,_,_,_,_⟩ := other
  cases List.mem_singleton.mp visible
  have ek : key = 0 := ident.symm
  subst key
  exact ⟨rfl,survivor_children_functional GeneralDictionaryOutputDepth252.checked other_copy survivor⟩

theorem no_merged :
    ¬ GeneralNominalVersionedMergedConflict232.MergedOutputConflict refreshed root := by
  rintro ⟨⟨a,b,member,_,_⟩,_⟩
  change (a,b) ∈ ([] : List (Nat × Nat)) at member
  cases member

theorem selected : Local sourceRegistry refreshed root (.selected 0 []) := by
  apply GeneralNominalVersionedMixedSourceBoundary234.local_iff.mpr
  apply GeneralNominalVersionedMixedBoundary234.local_iff.mpr
  exact GeneralNominalVersionedDiagnosticLaws232.selected_of_model safe unique after_model
    final_frame final_ready (committed.1 model after_model).1 (classes model after_model) no_merged

theorem evidence_at : B4SkeletonV8.EvidenceAt (boundary roles) sourceRegistry refreshed root := by
  intro m yes focus key children payloads scope _ _ pick supplied
  have equal : focus = root := scope.elim id
    (GeneralNominalVersionedMixedTerminalStable234.generated_only raw_sites no_edges)
  subst focus
  have code := B4TargetV8.local_functional pick selected
  cases code
  cases supplied
  exact ((evidence_payload m (.node 0 [])).mpr ⟨(final_models _).mp yes,rfl⟩).2

end Yulang.GeneralRebaseDepthHaltSelection285
