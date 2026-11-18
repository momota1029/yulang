import Yulang.GeneralDefaultRebaseBody260
namespace Yulang.GeneralDefaultRebaseSource260
open GeneralDictionaryDefaultGap206Source
open GeneralDefaultRebaseBody260 (body schema)
open GeneralRebaseStep258

abbrev report := GeneralNominalPacketSupport.report packet

theorem report_clear : report.blocked = [] ∧ report.conflicts = [] ∧ report.arity = [] ∧ report.captures = [] := by
 change let result := GeneralNominalRecursiveCandidates.report context declaration [(1,1)];
  result.blocked = [] ∧ result.conflicts = [] ∧ result.arity = [] ∧ result.captures = []
 rw [report_exact]
 exact ⟨rfl,rfl,rfl,rfl⟩

def facts : List Fact := [.installed 37,.binder 1408]

theorem output_keys : GeneralRebaseOwnedOutputKeys260.keys 37 schema = [.binder 1408] := rfl

/-- This terminal source has no capture obligations. Its actual default body
is still looked up and translated; an empty capture report does not skip it. -/
def proposal : Except GeneralRebaseOutputDecoder260.Failure Proposal :=
 if !report.blocked.isEmpty || !report.conflicts.isEmpty || !report.arity.isEmpty then .error .unhandledReport
 else match GeneralDictionaryAssociatedProvenance.lookup roles declaration 0 with
 | none => .error .unhandledReport
 | some chosen =>
   let outputSchema := GeneralNominalCenteredHeadMatEffects.bodySchema plan 0 chosen
   if outputSchema.unknown then .error .untranslatedOutputs
   else .ok (.installed 37 :: GeneralRebaseOwnedOutputKeys260.keys 37 outputSchema)

theorem proposal_exact : proposal = .ok facts := by
 unfold proposal
 rw [report_clear.1,report_clear.2.1,report_clear.2.2.1]
 rfl

abbrev initialState := GeneralRebaseStep258.initial facts
abbrev finalState := done facts

def observe : Observer facts := fun _ => match proposal with
 | .error _ => []
 | .ok proposed => [proposed]

theorem observe_exact : observe = fun _ => [facts] := by
 funext state
 simp only [observe,proposal_exact]

theorem closed : GeneralRebaseClosedObserver259.Closed observe := by
 intro state proposed member
 have same : proposed = facts := by simpa only [observe_exact,List.mem_singleton] using member
 subst proposed
 exact List.Subset.refl _

theorem write_initial : write initialState facts = finalState := by apply state_ext; decide

theorem first : Step observe initialState finalState :=
 ⟨facts,by simp [observe_exact],write_initial.symm,by decide⟩

theorem stop (after : State facts) : ¬ Step observe finalState after := by
 rintro ⟨proposed,_,equal,changed⟩
 apply changed
 rw [equal]
 rfl

theorem terminating (state : State facts) : Acc (fun after before => Step observe before after) state := accessible _ _
end Yulang.GeneralDefaultRebaseSource260
