import Yulang.GeneralRebasePortDecode280
import Yulang.GeneralRebaseFixedDisplay280

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
namespace Yulang.GeneralRebasePortGate280
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCandidates (Context)
open GeneralNominalState (State Known RootPending extend)
open GeneralNominalRecursiveCandidates (arguments)
open GeneralNominalVersionedFrame231 (childSite clauseChild)
open GeneralRebaseChildPorts280 (fixed fixedSite)
open GeneralRebasePortDecode280 (decode decodeSite writes occurrence_exact site_exact)
open GeneralNominalVersionedCandidates231 (Prepared Survivor)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)

theorem known_extend {s : State} (reserve : List Nat) (atoms : List (PresenceNormalForm.Atom Nat)) (name : Nat) :
    Known (extend s reserve atoms) name ↔ Known s name := Iff.rfl

theorem absent_not_known (s : State) (name : Nat)
    (absent : ∀ slot, s.base.source slot ≠ name) : ¬ Known s name :=
  fun ⟨slot,found,_⟩ => absent slot found

theorem pending_extended {o : Occurrence roles} {s : State} {i : Fin (roles o.demand.role).arity}
    (absent : ∀ slot, s.base.source slot ≠ (o.demand.arguments i).1)
    (reserve : List Nat) (atoms : List (PresenceNormalForm.Atom Nat)) :
    RootPending (extend s reserve atoms) o.demand :=
  ⟨i,fun known => absent_not_known s _ absent ((known_extend reserve atoms _).mp known)⟩

def restored (p : Plan roles) (c : Clause) (ok : c.Signature roles) : Occurrence roles :=
  decode (writes p.packet c ok) (fixed p.packet c ok)

theorem restored_eq (p : Plan roles) (c : Clause) (ok : c.Signature roles) :
    restored p c ok = clauseChild p.packet c ok :=
  occurrence_exact ..

theorem restore_prepared (p : Plan roles) (c : Clause) (ok : c.Signature roles)
    (r : Registry) (ctx : Context) (d : Declaration) :
    Prepared r ctx (restored p c ok) d ↔ Prepared r ctx (clauseChild p.packet c ok) d := by
  rw [restored_eq]

theorem restore_survivor (p : Plan roles) (c : Clause) (ok : c.Signature roles)
    (r : Registry) (ctx : Context) (k : Nat) (kids : List (Occurrence roles)) :
    Survivor r ctx (restored p c ok) k kids ↔ Survivor r ctx (clauseChild p.packet c ok) k kids := by
  rw [restored_eq]

theorem restore_evidence
    (p : Plan roles) (c : Clause) (ok : c.Signature roles)
    (s : GeneralNominalVersionedJournal232.State roles) (r : Registry) (m : Assignment)
    (payload : GeneralDictionaryReadback.Payload) :
    GeneralNominalVersionedEvidence231.Evidence r s.core m (restored p c ok) payload ↔
      GeneralNominalVersionedEvidence231.Evidence r s.core m (clauseChild p.packet c ok) payload := by
  rw [restored_eq]

namespace Display
open GeneralRebaseFixedDisplay280 (canonical actual c valid target copyTarget write_matches model_after)
open GeneralNominalExamples (state context displayRoot displayChild intDisplay)
open GeneralDeclarationExamples (roles)
open GeneralRebaseCompiledDisplay277 (parent frame_parent after compiled)
open GeneralRebasePortMeaning280 (SiteMatches)

def i : Fin (roles c.role).arity := ⟨0,by decide +kernel⟩

theorem unknown : ∀ slot, (state true).base.source slot ≠ (canonical.occurrence.demand.arguments i).1 := by
  intro slot
  rw [copyTarget]
  have hi : 1 < target.1 := GeneralNominalIdentities.source_above_seed ..
  have small := slot.isLt
  change slot.val < 2 at small
  change slot.val ≠ target.1
  omega

theorem raw_gate_fails (reserved : List Nat) (extra : List (PresenceNormalForm.Atom Nat)) :
    RootPending (extend (state true) reserved extra) canonical.occurrence.demand :=
  pending_extended (i := i) unknown reserved extra

theorem actual_point_known : ¬ RootPending (state true) actual.occurrence.demand := by
  rw [GeneralRebaseFixedDisplay280.raw_occurrence]
  intro pending
  obtain ⟨index,dec⟩ := pending
  exact dec ⟨1,rfl,Or.inl (by decide +kernel)⟩

theorem restored_point_known : ¬ RootPending (state true) (restored parent c valid).demand := by
  rw [restored_eq]
  exact actual_point_known

theorem restored_actual : restored parent c valid = displayChild :=
  (restored_eq parent c valid).trans GeneralRebaseFixedDisplay280.raw_occurrence

theorem restored_child_evidence (m : Assignment) (validModel : Models after m) :
    GeneralNominalVersionedEvidence231.Evidence compiled after.core m (restored parent c valid) (.node 3 []) := by
  rw [restored_actual]
  exact GeneralRebaseCompiledEvidence277.child_evidence m validModel

end Display
end Yulang.GeneralRebasePortGate280
