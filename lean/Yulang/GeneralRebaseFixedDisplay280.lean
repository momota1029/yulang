import Yulang.GeneralRebaseProjectedReach280
import Yulang.GeneralRebasePortCopy280
import Yulang.GeneralRebaseCompactDisplay279

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 10000000
namespace Yulang.GeneralRebaseFixedDisplay280
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalExamples (registry state displayRoot displayChild)
open GeneralDeclarationExamples (roles display_checked)
open GeneralRebaseDisplayFrame276 (before source_ids)
open GeneralRebaseCompiledDisplay277 (compiled parent after frame_parent)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseChildPorts280 (fixed fixedSite ports fixed_distinct)
open GeneralRebasePortMeaning280 (SiteMatches clauseAtoms clause_atoms site_holds)
open GeneralRebasePortCopy280 (PairWrites Unambiguous Apart Isolated Copy copy_agrees interval_copy)

abbrev c := GeneralDeclarationExamples.displayChild
theorem valid : c.Signature roles := display_checked.signature.2.2.2 _ (by simp)

def actual : Site roles := GeneralNominalVersionedFrame231.childSite parent c valid
def canonical : Site roles := fixedSite parent c valid
def target := ports 1 100 1 10 0
def writes := PairWrites target (1,1)

theorem original (i : Fin (roles c.role).arity) :
    actual.occurrence.demand.arguments i = (1,1) := by
  change (GeneralNominalVersionedFrame231.clauseChild parent.packet c valid).demand.arguments i = _
  have z : i.val = 0 := by have lt := i.isLt; change i.val < 1 at lt; omega
  have shape : GeneralDeclarationPatterns.normalize (c.arguments[i.val]'(by rw [valid.1]; exact i.isLt)) =
      .var 0 := by simp only [z]; rfl
  rw [GeneralRebaseChildPorts280.bare_capture _ _ _ _ shape]
  exact GeneralRebaseDisplayPacket276.capture

theorem copyTarget (i : Fin (roles c.role).arity) :
    canonical.occurrence.demand.arguments i = target := by
  have z : i.val = 0 := by have lt := i.isLt; change i.val < 1 at lt; omega
  change ports 1 100 1 10 i.val = _
  rw [z]
  rfl

theorem raw_occurrence : actual.occurrence = displayChild := by
  have cMember : actual ∈ GeneralNominalVersionedChildren232.emitted parent := by
    unfold GeneralNominalVersionedChildren232.emitted
    have listed : c ∈ GeneralCanonicalChildOrder.canonicalRequirements parent.packet.declaration.requirements := by decide +kernel
    exact List.mem_map.mpr ⟨⟨c,listed⟩,List.mem_attach ..,rfl⟩
  have kid := GeneralNominalVersionedChildren232.emitted_child_iff.mpr ⟨actual,cMember,rfl⟩
  rw [GeneralRebaseCompiledDisplay277.children] at kid
  exact List.mem_singleton.mp kid

theorem apart (limit : ∀ n ∈ pool, n ≤ 1) : Apart writes pool := by
  intro entry mentioned collision
  have high1 : 1 < target.1 := GeneralNominalIdentities.source_above_seed ..
  have high2 : 1 < target.2 := GeneralNominalIdentities.source_above_seed ..
  simp only [writes,PairWrites,List.mem_cons,List.not_mem_nil,or_false] at mentioned
  rcases mentioned with rfl|rfl <;> have small := limit _ collision <;> omega

theorem unique : Unambiguous writes := by
  intro a ha b hb _
  simp only [writes,PairWrites,List.mem_cons,List.not_mem_nil,or_false] at ha hb
  rcases ha with rfl|rfl <;> rcases hb with rfl|rfl <;> rfl

theorem isolated : Isolated writes := by
  apply apart
  intro n member
  simp only [writes,PairWrites,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl <;> omega

theorem write_matches (m : Assignment) : SiteMatches (Copy writes m) parent c valid := by
  intro i
  change GeneralRebasePortMeaning280.Matches _ (canonical.occurrence.demand.arguments i)
    (actual.occurrence.demand.arguments i)
  rw [copyTarget,original]
  exact interval_copy unique isolated (fun _ h => h) m

theorem model_copy (m : Assignment) (validModel : Models before m) : Models before (Copy writes m) := by
  have old := ((GeneralNominalVersionedJournal232.initial_models ..).mp validModel).1
  have new := (GeneralNominalSemanticRawFrame236.source_models_same (state true)
    (copy_agrees (apart (by intro n actual; exact source_ids n actual)) m)).mp old
  exact (GeneralNominalVersionedJournal232.initial_models ..).mpr
    ⟨new,point_root_holds _ _ (fun _ => rfl) _⟩

theorem model_after (m : Assignment) (validModel : Models after m) :
    Models after (Copy writes m) :=
  (GeneralRebaseCompiledInstall277.models _).mpr (model_copy m ((GeneralRebaseCompiledInstall277.models _).mp validModel))

theorem point_only_semantic :
    actual.occurrence.demand.arguments ⟨0,by decide +kernel⟩ = (1,1) ∧ target.1 ≠ target.2 :=
  ⟨original _,fixed_distinct 1 100 1 10 0⟩

theorem alias_holds (m : Assignment) :
    PresenceNormalForm.All CommonNominalFullCarrier.model (Copy writes m) (clauseAtoms parent c valid) :=
  (clause_atoms ..).mpr (write_matches m)

theorem canonical_site_holds (m : Assignment) (validModel : Models after m) :
    canonical.Holds (Copy writes m) := by
  have old := ((GeneralNominalVersionedJournal232.initial_models ..).mp
    ((GeneralRebaseCompiledInstall277.models _).mp (model_after m validModel))).1
  have packet := (GeneralRebaseCompiledRetag277.holds GeneralNominalNonleafPlan193.plan compiled rfl _).mpr
    (GeneralRebaseDisplayPacket276.holds _ old)
  have present : c ∈ parent.packet.declaration.requirements := List.mem_singleton_self _
  exact (site_holds (write_matches m)).mpr (packet.2.1.2.2.2.2.2.2 c present valid).1

theorem preserves_payload (m : Assignment) (validModel : Models after m) :
    GeneralNominalVersionedEvidence231.Evidence compiled after.core (Copy writes m) displayRoot (.node 1 [.node 3 []]) :=
  GeneralRebaseCompiledEvidence277.real_nonleaf _ (model_after m validModel)

end Yulang.GeneralRebaseFixedDisplay280
