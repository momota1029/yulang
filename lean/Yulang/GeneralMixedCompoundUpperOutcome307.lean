import Yulang.GeneralMixedCompoundUpperHalt307
import Yulang.GeneralDictionaryCompoundVacuity239

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 18000
set_option maxHeartbeats 8000000
namespace Yulang.GeneralMixedCompoundUpperOutcome307
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralDictionaryCompoundSource238 (registry sourceRegistry declaration child)
open GeneralDictionaryCompoundSites238 (childSite signature)
open GeneralDictionaryCompoundRefresh239 (refreshed)
open GeneralMixedCompoundUpperRefresh307 (upperState models_iff)
open GeneralMixedCompoundUpperChild307 (no_survivor no_inspection_pending no_frame no_evidence known reachable)
open GeneralMixedCompoundUpperHalt307 (stable reached_cases)
open GeneralMixedCompoundUpperObstruction307 (currentPlan no_current_packet)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedDiagnostic232 (AdministrativeReady)
open GeneralNominalVersionedJournal232 (Models State)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedEvidence231 (Evidence)
open CommonRoleOutermostResolver

theorem generated : GeneralNominalSaturationState.Generated upperState.core.erased.current root childSite.occurrence :=
  .child .root (GeneralNominalVersionedInstall232.installed_child
    (GeneralDictionaryCompoundSites238.children ▸ List.mem_singleton_self _))

theorem admin_ready : AdministrativeReady upperState childSite.occurrence :=
  GeneralNominalVersionedMixedTrace235.administrative_ready reachable stable generated

theorem no_sharing : ¬ (boundary roles).SharingConflict registry upperState childSite.occurrence := by
  rintro ⟨key,kids,unique,_⟩
  exact no_survivor key kids unique.1

theorem rejected_child : B4TargetV8.Local (boundary roles) registry upperState childSite.occurrence .rejected := by
  apply B4TargetV8.Local.ordinary no_sharing
  classical
  by_cases merge : (boundary roles).toV7.MergedOutputConflict registry upperState childSite.occurrence
  · apply B4TargetV7.Local.mergedRejected merge
    rintro ⟨_,key,kids,_,_,one,_,_⟩
    exact no_survivor key kids one
  · apply B4TargetV7.Local.ordinary merge
    apply B4TargetV6.Local.rejected
    refine ⟨known,Or.inr (Or.inr ⟨?_,Or.inl no_survivor⟩)⟩
    rintro (pending|absent)
    · exact no_inspection_pending pending
    · exact absent admin_ready

theorem exact_child (found : B4TargetV8.Local (boundary roles) registry upperState childSite.occurrence status) :
    status = .rejected :=
  B4TargetV8.local_functional found rejected_child

theorem child_site (sig : child.Signature roles) :
    GeneralNominalVersionedFrame231.childSite currentPlan child sig =
      GeneralNominalVersionedFrame231.childSite GeneralDictionaryCompoundObstruction238.oldPlan child sig := by
  unfold GeneralNominalVersionedFrame231.childSite GeneralNominalVersionedFrame231.clauseChild
    GeneralDictionaryEmissionPlans.occurrence GeneralDeclarationDemands.emit
    GeneralDeclarationDemands.childDemand GeneralNominalVersionedFrame231.frame
    GeneralNominalVersionedFrame231.emittedCenter
  dsimp only
  congr 1
  congr 1
  congr 1
  all_goals
    funext index
    have same : index = 0 := Fin.ext (by have h := index.isLt; change index.val < 1 at h; omega)
    subst index
    rfl

theorem child_history_shape :
    GeneralNominalVersionedFrame231.children currentPlan.packet = [childSite.occurrence] := by
  have exactList : GeneralNominalVersionedFrame231.children currentPlan.packet =
      [(GeneralNominalVersionedFrame231.childSite currentPlan child signature).occurrence] := by
    unfold GeneralNominalVersionedFrame231.children GeneralDictionaryEmissionPlans.children
      GeneralCanonicalChildOrder.canonicalEmit
    simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_singleton]
    rfl
  rw [child_site] at exactList
  exact exactList

theorem root_local_children {key kids}
    (selected : B4TargetV8.Local (boundary roles) registry upperState root (.selected key kids)) :
    kids = [childSite.occurrence] := by
  obtain ⟨p,frame,children⟩ := GeneralNominalVersionedMixedSelectedFrame235.source_frame reachable selected
  rw [GeneralMixedCompoundUpperRoot307.frame_plan frame] at children
  exact children.symm.trans child_history_shape

private theorem selected_inv {focus : GeneralSourceDictionaries.Occurrence roles} {outcome}
    (h : B4TargetV8.Classify (boundary roles) registry upperState focus outcome) :
    ∀ payload, outcome = .selected payload →
      ∃ key kids dictionaries,
        B4TargetV8.Local (boundary roles) registry upperState focus (.selected key kids) ∧
        All₂ (fun child d => B4TargetV8.Classify (boundary roles) registry upperState child (.selected d))
          kids dictionaries :=
  match h with
  | .pending _ => fun _ eq => nomatch eq
  | .rejected _ => fun _ eq => nomatch eq
  | .ambiguous _ => fun _ eq => nomatch eq
  | .selected localRule kids => fun _ _ => ⟨_,_,_,localRule,kids⟩

theorem no_selected_tree (payload : GeneralDictionaryReadback.Payload) :
    ¬ B4TargetV8.Classify (boundary roles) registry upperState root (.selected payload) := by
  intro h
  obtain ⟨_,kids,_,localRule,proof⟩ := selected_inv h payload rfl
  rw [root_local_children localRule] at proof
  cases proof with
  | cons one _ =>
    obtain ⟨_,_,_,picked,_⟩ := selected_inv one _ rfl
    cases exact_child picked

theorem no_root_evidence (m : Assignment) (valid : Models upperState m)
    (payload : GeneralDictionaryReadback.Payload) :
    ¬ Evidence registry upperState.core m root payload := by
  intro ev
  have indexed := (GeneralDictionaryReadback.payload_iff_erased _ _ _).mpr ev
  cases indexed with
  | node instanceProof _ =>
    obtain ⟨p,cert⟩ := instanceProof
    have same := GeneralMixedCompoundUpperRoot307.frame_plan cert.frame
    subst p
    exact no_current_packet m valid cert.packet

theorem evidenceAt : B4SkeletonV8.EvidenceAt (boundary roles) sourceRegistry upperState root := by
  intro model valid focus key kids dict reached _ _ chosen evidence
  obtain ⟨p,frame,children⟩ := GeneralNominalVersionedMixedSelectedFrame235.source_frame reachable chosen
  have casesFocus : focus = root ∨ focus = childSite.occurrence :=
    reached.elim Or.inl reached_cases
  rcases casesFocus with rfl|rfl
  · have same := GeneralMixedCompoundUpperRoot307.frame_plan frame
    subst p
    rw [child_history_shape] at children
    subst kids
    cases evidence with
    | cons one _ => exact False.elim (no_evidence model _ one)
  · exact False.elim (no_frame key p frame)

end Yulang.GeneralMixedCompoundUpperOutcome307
