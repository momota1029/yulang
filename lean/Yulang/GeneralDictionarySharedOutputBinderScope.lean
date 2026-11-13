import Yulang.GeneralNominalSharedCaptures
import Yulang.GeneralNominalSupportSiblings

/-! Scope correction for a proposed producer/consumer fixture. A fresh
output-only binder cannot occur in a checked child input at all. This is an
existing declaration-checker restriction, not a newly discovered Shared
generation or source-reachability counterexample. -/
namespace Yulang.GeneralDictionarySharedOutputBinderScope
open GeneralDeclarations GeneralDeclarationPatterns GeneralNominalSharedCaptures
open GeneralNominalSupportSiblings
open GeneralNominalSaturationState

/-- Every Needed name of any checked packet is an original head input name. -/
theorem needed_is_input (packet : Packet roles) (name : Nat) (needed : Needed packet name) :
    name ∈ packet.declaration.inputNames := by
  obtain ⟨clause,member,used⟩ := needed
  exact packet.checked.scope.1 clause member name used

abbrev consumer : Clause := ⟨106,0,[.var 2],[]⟩
abbrev proposed : Declaration :=
  ⟨90,0,[.app 0 [.var 0]],[cp,consumer],[],[⟨2,100,101⟩]⟩

theorem proposed_output : 2 ∈ proposed.outputNames := by
  simp [Declaration.outputNames]

theorem proposed_consumer_input : 2 ∈ variablesArgs consumer.arguments := by
  simp [variablesArgs,Pattern.variables]

/-- No checked packet can be formed from this tempting but invalid proposal. -/
theorem proposed_not_checked :
    ¬ DeclarationChecked GeneralDeclarationExamples.constructors GeneralDeclarationExamples.roles proposed :=
  output_input_rejected proposed consumer (by simp) 2 proposed_output proposed_consumer_input

theorem no_checked_packet (packet : Packet GeneralDeclarationExamples.roles)
    (same : packet.declaration = proposed)
    (constructors : packet.registry.constructors = GeneralDeclarationExamples.constructors) : False := by
  apply proposed_not_checked
  have checked := packet.checked
  simpa only [same,constructors] using checked

/-- Candidate alternative: both clauses mention the original captured input,
and the producer equation refines that input. No new output-only binder. -/
abbrev producerOnInput : Clause := ⟨110,2,[.app 0 [.var 0]],[⟨111,1,.var 0⟩]⟩
abbrev consumerOnInput : Clause := ⟨112,0,[.var 0],[]⟩
abbrev capturedProposal : Declaration :=
  ⟨113,0,[.app 0 [.app 0 [.var 0]]],[producerOnInput,consumerOnInput],[],[]⟩

theorem captured_proposal_checked :
    DeclarationChecked GeneralDeclarationExamples.constructors GeneralDeclarationExamples.roles capturedProposal := by
  constructor
  · simp [Declaration.Signature,Clause.Signature,Declared,producerOnInput,consumerOnInput,
      GeneralDeclarationExamples.roles,GeneralDeclarationExamples.bareRole,GeneralDeclarationExamples.outputRole]
  · simp [Declaration.Identified,Declaration.outputNames,producerOnInput,consumerOnInput]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,producerOnInput,consumerOnInput,
      normalizeArgs,normalize,variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,GeneralDeclarationExamples.constructors,
      producerOnInput,consumerOnInput]
  · intro clause member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> exact ⟨rfl,rfl⟩
  · intro clause member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> exact (checkSmaller_exact _ _).mp (by decide +kernel)
  · intro clause member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> unfold ConservativeSmaller <;> decide +kernel
  · intro clause member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    all_goals
      intro capture
      constructor
      · simp only [counted,substArgs,Pattern.subst,
          normalizeArgs,normalize,encodeArgs,Pattern.encode,Roles.argsSize,Roles.Term.size]
        omega
      · intro name
        simp only [counted,substArgs,Pattern.subst,
          normalizeArgs,normalize,encodeArgs,Pattern.encode,Roles.argsOccurrences,Roles.Term.occurrences]
        omega

theorem captured_proposal_no_output_binders : capturedProposal.outputNames = [] := rfl

end Yulang.GeneralDictionarySharedOutputBinderScope
