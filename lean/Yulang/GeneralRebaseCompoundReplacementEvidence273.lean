import Yulang.GeneralRebaseCompoundReplacementPublic273
import Yulang.GeneralDictionaryCompoundChildPending238

set_option maxRecDepth 24000
set_option maxHeartbeats 5000000
namespace Yulang.GeneralRebaseCompoundReplacementEvidence273
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedEvidence231 (Instance Certificate Evidence certificate_of_semantics)
open GeneralDictionaryCompoundPoint238 (point)
open GeneralDictionaryCompoundObstruction238 (oldPlan currentPlan)
open GeneralDictionaryCompoundSource238 (registry declaration child)
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralDictionaryCompoundSites238 (signature childSite)
open GeneralDictionaryReadback (Payload)
open GeneralRebaseCompoundReplacementFrame273 (Meaning)
open GeneralRebaseCompoundReplacementPublic273 (complete agrees completed)
open GeneralRebaseCompoundPublic273 (Fixed)
open GeneralRebaseCompoundRows273 (Agrees)
open GeneralNominalVersionedFrame231 (children childSite)

theorem current_children : children currentPlan.packet = [GeneralDictionaryCompoundSites238.childSite.occurrence] := by
 calc
  children currentPlan.packet = [(childSite currentPlan child signature).occurrence] := by
    unfold children GeneralDictionaryEmissionPlans.children GeneralCanonicalChildOrder.canonicalEmit
    simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_singleton]
    rfl
  _ = [GeneralDictionaryCompoundSites238.childSite.occurrence] := by rw [GeneralDictionaryCompoundReplay238.child_site]

theorem current_certificate (m : Assignment) (validated : Meaning m) :
 Certificate registry point.core m root declaration.id
  [GeneralDictionaryCompoundSites238.childSite.occurrence] currentPlan :=
 certificate_of_semantics GeneralDictionaryCompoundPrepared238.frame current_children.symm
  validated.1 GeneralDictionaryCompoundFeasible238.ready validated.2

theorem root_instance (m : Assignment) (validated : Meaning m) :
 Instance registry point.core m root declaration.id [GeneralDictionaryCompoundSites238.childSite.occurrence] :=
 ⟨currentPlan,current_certificate m validated⟩

theorem no_root_evidence (m : Assignment) (d : Payload) : ¬ Evidence registry point.core m root d := by
 intro witness
 have indexed := (GeneralDictionaryReadback.payload_iff_erased _ _ _).mpr witness
 cases indexed with
 | node instanceRule kids =>
   obtain ⟨p,instanceRule⟩ := instanceRule
   have same := GeneralDictionaryCompoundNoInstance238.frame_plan instanceRule.frame
   subst p
   rw [instanceRule.children_eq,current_children] at kids
   cases kids with
   | cons childProof _ =>
     exact GeneralDictionaryCompoundChildPending238.no_evidence m _
       ((GeneralDictionaryReadback.payload_iff_erased _ _ _).mp childProof)

/-- A local root instance is obtained over every accepted public boundary,
but the omitted child location remains an actual evidence obstruction on
the unchanged real raw core. -/
theorem local_not_global (boundary : Assignment) (known : Fixed boundary) :
 Agrees (complete boundary) boundary ∧
 Instance registry point.core (complete boundary) root declaration.id
   [GeneralDictionaryCompoundSites238.childSite.occurrence] ∧
 ∀ d, ¬ Evidence registry point.core (complete boundary) root d :=
 ⟨agrees boundary,root_instance _ (completed boundary known),no_root_evidence _⟩

end Yulang.GeneralRebaseCompoundReplacementEvidence273
