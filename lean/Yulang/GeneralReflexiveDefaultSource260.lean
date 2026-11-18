import Yulang.GeneralRebaseBodyDecoder260
import Yulang.GeneralDictionaryVersionedDefault202Local233
namespace Yulang.GeneralReflexiveDefaultSource260
open GeneralDictionaryAllocDefaultSource202
open GeneralRebaseStep258
abbrev body : GeneralDictionaryAssociatedProvenance.Body := .default 0 0 (.var 0)
abbrev schema := GeneralNominalCenteredHeadMatEffects.bodySchema plan 1 body
abbrev facts := GeneralDefaultRebaseSource260.facts
abbrev initialState := GeneralRebaseStep258.initial facts
abbrev finalState := done facts
abbrev report := GeneralNominalPacketSupport.report packet

theorem schema_exact : schema = ⟨[⟨1,.actual,.variable 0⟩],false⟩ := rfl

theorem output_keys : GeneralRebaseOwnedOutputKeys260.keys 37 schema = [.binder 1408] := rfl

theorem body_meaning (assignment : GeneralNominalCommonBridge.Assignment) :
 GeneralNominalVersionedEffects231.BodyHolds plan 1 assignment body ↔
 CommonNominalFullCarrier.Equivalent (assignment 1).1 (assignment 1).1 :=
 (GeneralNominalVersionedEffects231.body_holds_iff ..).trans
   (GeneralNominalCenteredHeadMatEffects.positional_default plan assignment (0 : Fin 1))

theorem report_clear : report.blocked = [] ∧ report.conflicts = [] ∧ report.arity = [] ∧ report.captures = [] := by
 change let result := GeneralNominalRecursiveCandidates.report context declaration [(1,1)];
  result.blocked = [] ∧ result.conflicts = [] ∧ result.arity = [] ∧ result.captures = []
 rw [report_exact]
 exact ⟨rfl,rfl,rfl,rfl⟩

inductive Failure where
 | unhandledReport
 | body (reason : GeneralRebaseBodyDecoder260.Failure)
 deriving Repr

def proposal : Except Failure Proposal :=
 if !report.blocked.isEmpty || !report.conflicts.isEmpty || !report.arity.isEmpty then .error .unhandledReport
 else match GeneralRebaseBodyDecoder260.compile plan 37 ⟨0,1⟩ with
 | .error reason => .error (.body reason)
 | .ok proposed => .ok proposed

theorem proposal_exact : proposal = .ok facts := by
 unfold proposal
 rw [report_clear.1,report_clear.2.1,report_clear.2.2.1]
 rfl

def observe : Observer facts := fun _ => match proposal with
 | .error _ => []
 | .ok proposed => [proposed]

theorem observe_equal : observe = GeneralDefaultRebaseSource260.observe := by
 funext state
 simp only [observe,proposal_exact,GeneralDefaultRebaseSource260.observe,
   GeneralDefaultRebaseSource260.proposal_exact]
end Yulang.GeneralReflexiveDefaultSource260
