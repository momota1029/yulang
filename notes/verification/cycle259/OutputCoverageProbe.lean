import Yulang.GeneralRebaseCheckedFixtures259
import Yulang.GeneralDictionaryOutputInputs258
open Yulang
namespace Cycle259OutputCoverageProbe
open GeneralDictionaryOutputDepth252
open GeneralRebaseStep258

def atom (slot : Fin snapshot.base.slots) : Option Nat := if slot = 2 then some 0 else none

def facts : List Fact := [.installed 0,.lower 0 0,.upper 0 0,.binder 0,.binder 1]

theorem actual_decoder_accepts : GeneralRebaseFiniteReport259.compile 0 atom
 (GeneralNominalPacketSupport.report packet) = some facts := by
 change GeneralRebaseFiniteReport259.compile 0 atom
  (GeneralNominalRecursiveCandidates.report context declaration [(2,2)]) = _
 rw [report_exact]
 rfl

theorem checked_write_accepts : GeneralRebaseCheckedWrite259.commit (initial facts) facts =
 .ok (some (done facts)) := rfl

/-- An actual prepared source packet, not an arbitrary forged Report. Syntactic
acceptance and internal basis closure are not an output semantic certificate. -/
theorem accepted_report_not_output_certificate :
 GeneralRebaseFiniteReport259.compile 0 atom (GeneralNominalPacketSupport.report packet) = some facts ∧
 GeneralNominalVersionedEvidence231.Frame registry GeneralDictionaryOutputDepth252.initial.core root 0 plan ∧
 GeneralNominalVersionedJournal232.Models GeneralDictionaryOutputDepth252.initial
  (GeneralDictionaryPendingOutput258.replace .bottom) ∧
 ¬ GeneralNominalVersionedPlans231.Holds plan (GeneralDictionaryPendingOutput258.replace .bottom) :=
 ⟨actual_decoder_accepts,GeneralDictionaryOutputPremise258.frame_not_packet⟩

#print axioms actual_decoder_accepts
#print axioms checked_write_accepts
#print axioms accepted_report_not_output_certificate
end Cycle259OutputCoverageProbe
