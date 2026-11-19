import Yulang.GeneralRebaseTerminalObservation274
import Yulang.GeneralDictionaryRebaseEvidence230243

set_option maxRecDepth 22000
set_option maxHeartbeats 7400000
namespace Yulang.GeneralRebaseTerminalPayload274
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedEvidence231 (Evidence)
open GeneralDictionaryReadback (Payload payload_iff_erased)
open GeneralDictionaryJournalRefinement228Source (root)
open GeneralDictionaryOptionalInitial229 (registry declaration)
open GeneralDictionaryVersionedSecondInstall233 (installed plan terminal)
open GeneralRebaseCompoundPublic273 (Fixed)
open GeneralRebaseTerminalDecode274 (decode)
open GeneralRebaseTerminalAlias274 (sourceId normalize normalize_valid)
open GeneralNominalRebaseRawView243 (read)
open Core.PresenceGeneration (CompTerm)

def accepts : Payload → Bool
 | .node key children => (key == declaration.id) && children.isEmpty

theorem payload_shape (m : Assignment) (data : Payload) (valid : Evidence registry installed.core m root data) :
 data = .node declaration.id [] := by
 have erasable := (payload_iff_erased _ _ _).mpr valid
 cases erasable with
 | node rule children =>
   obtain ⟨candidate,recorded⟩ := rule
   have frame := GeneralDictionaryVersionedSecondStable233.frame_plan recorded.frame
   subst candidate
   have key := recorded.frame.key_eq
   have empty := recorded.children_eq.trans
    ((GeneralNominalVersionedInstallation231.replay_children plan).trans terminal)
   rw [empty] at children
   cases children
   rw [← key]
   rfl

theorem accepted_shape (data : Payload) : accepts data = true ↔ data = .node declaration.id [] := by
 cases data with
 | node key list =>
   simp only [accepts,Bool.and_eq_true,beq_iff_eq,List.isEmpty_iff,CommonRoleOutermostResolver.Dictionary.node.injEq]

theorem checked (m : Assignment) (valid : Models installed m) (data : Payload) :
 accepts data = true ↔ Evidence registry installed.core m root data := by
 rw [accepted_shape]
 constructor
 · rintro rfl
   exact GeneralDictionaryVersionedSecondInstall233.evidence valid
 · exact payload_shape m data

/-- A finite type-alias substitution serves the genuine installed model;
   the row coordinate is never redirected to the source of a type alias. -/
def mapping (id : Nat) : CompTerm Nat := ⟨.var (sourceId id),.var id⟩

theorem read_exact (m : Assignment) : read mapping m = normalize m := rfl

def ViewEvidence (m : Assignment) (data : Payload) : Prop :=
 GeneralNominalRebaseEvidenceView243.Evidence registry installed.core mapping m root data

theorem view_exact (m : Assignment) (valid : Models installed m) (data : Payload) :
 accepts data = true ↔ ViewEvidence m data := by
 unfold ViewEvidence
 rw [GeneralNominalRebaseEvidenceView243.evidence_exact,read_exact]
 exact checked _ (normalize_valid m valid) data

theorem decode_acceptance (boundary : Assignment) (data : Payload) :
 (Fixed boundary ∧ accepts data = true) ↔
 (Models installed (decode boundary) ∧ ViewEvidence (decode boundary) data) := by
 constructor
 · rintro ⟨fixed,computed⟩
   have model := GeneralRebaseTerminalDecode274.terminal boundary fixed
   exact ⟨model,(view_exact _ model data).mp computed⟩
 · rintro ⟨model,evidence⟩
   exact ⟨(GeneralRebaseTerminalRows274.terminal_public boundary).mp
     ⟨decode boundary,GeneralRebaseTerminalDecode274.agrees boundary,model⟩,
     (view_exact _ model data).mpr evidence⟩

theorem rejects_wrong_key : accepts (.node (declaration.id+1) []) = false := rfl

theorem rejects_children : accepts (.node declaration.id [.node declaration.id []]) = false := rfl

end Yulang.GeneralRebaseTerminalPayload274
