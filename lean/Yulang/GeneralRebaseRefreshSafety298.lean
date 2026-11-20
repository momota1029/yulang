import Yulang.GeneralRebasePackedSource298
import Yulang.GeneralRebaseDepthHaltSelection285

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 23000
set_option maxHeartbeats 9500000
namespace Yulang.GeneralRebaseRefreshSafety298
open GeneralDictionaryOutputDepth252 (roles sourceRegistry registry root snapshot initial plan declaration model)
open GeneralDictionaryOutputDepthInstall252 (smallModel small_source small_initial form_value form)
open GeneralDictionaryOutputDepthCycles252 (nominal_child equivalent_rank Form)
open GeneralRebasePreInstallReplay297 (target after cert refines candidate signs_preserved source_reachable)
open GeneralRebaseSignedDepth297 (checked)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedMixedObservations233 (refresh_models)
open GeneralNominalVersionedCandidates231 (Prepared inputs)
open GeneralNominalRecursiveCandidates (Metadata)
open GeneralRebaseCandidatePrepared267 (prepared_iff ready_exact)
open GeneralRebaseSourceSurvivor267 (Boundary Encoded declChecked)
open GeneralRebaseRawInstallScan297 (Known)
open CommonNominalFullCarrier (Equivalent subtype_trans)

theorem real_metadata : Metadata registry target :=
  GeneralRebaseSourceMetadata297.reachable_metadata source_reachable

theorem candidate_ready : candidate ∈ GeneralRebaseCandidatePrepared267.readyPlans registry after root (declChecked checked) := by
  have member := (GeneralRebasePreInstallReplay297.listed_after candidate).mpr rfl
  obtain ⟨f,_,safe⟩ := (GeneralRebaseSourceQuestions297.entries_exact ..).mp member
  exact (GeneralRebaseHeadProbe267.atFocus_exact ..).mp safe |>.1

theorem prepared : Prepared registry target root declaration := by
  obtain ⟨shell,_,preflight⟩ := (ready_exact ..).mp candidate_ready
  have head := GeneralNominalVersionedPlans231.head_models signs_preserved.1.2.1
  exact (prepared_iff registry after root candidate shell).mpr ⟨real_metadata,preflight,model,head⟩

theorem raw_edge {a b : Fin target.state.base.slots}
    (edge : GeneralNominalMixedRecurrence.Edge target.state a b) : (form b.val).rank < (form a.val).rank := by
  rcases edge with structural | nominal
  · obtain ⟨kind,_⟩ := structural
    exact Fin.elim0 kind
  · obtain ⟨descriptor,recorded,index,actual,seen,same⟩ :=
      GeneralNominalMixedRecurrence.actual_edge_sound target.state a b nominal smallModel small_source
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

theorem semantic_acyclic (o) : ¬ GeneralNominalVersionedCycles232.Cyclic after o := by
  have actual : Models after = Models initial := funext fun m => propext (refresh_models cert)
  exact fun cycle => GeneralDictionaryOutputDepthInstall252.no_cycle o
    ((GeneralNominalVersionedCycles232.full_models_only actual).mp cycle)

theorem administrative : GeneralNominalVersionedDiagnostic232.AdministrativeReady after root := by
  constructor
  · exact ⟨_,List.mem_cons_self,rfl⟩
  · intro a was _ b appears _
    cases List.mem_singleton.mp was
    cases List.mem_singleton.mp appears
    exact .refl _

theorem safe : Known sourceRegistry after root := by
  have noPending : ¬ GeneralNominalState.RootPending target.state root.demand := by
    exact (GeneralRebaseCandidateChecks267.allKnown_exact ..).mp (by decide +kernel)
  refine ⟨noPending,?_,?_,?_⟩
  · rintro (raw | (⟨i,cycle⟩ | ⟨site,_,_,i,cycle⟩))
    · obtain ⟨_,_,_,slot,_,cycle⟩ := raw
      exact raw_acyclic slot cycle
    · exact semantic_acyclic _ cycle
    · exact semantic_acyclic _ cycle
  · rintro (raw | ⟨p,_,entry,member,cycle⟩)
    · obtain ⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ := raw
      exact raw_acyclic visited.1 cycle
    · exact semantic_acyclic _ cycle
  · rintro (⟨_,d,visible,role,_,unprepared⟩ | unclosed)
    · cases List.mem_singleton.mp visible
      exact unprepared prepared
    · exact unclosed administrative

end Yulang.GeneralRebaseRefreshSafety298
