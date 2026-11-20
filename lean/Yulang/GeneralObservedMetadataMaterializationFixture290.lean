import Yulang.GeneralObservedMetadataBranch290

/-! Real parent-output extraction and an independent control with a
constructor occurring only in an associated rhs. The control is not
claimed to be an executed raw install. -/
set_option maxHeartbeats 17000000
namespace Yulang.GeneralObservedMetadataMaterializationFixture290
open GeneralRebaseRowChildSource287
open GeneralDeclarations GeneralDeclarationPatterns
open GeneralDeclarationExamples (bareRole outputRole)
open GeneralObservedMetadataBranch290 (branchFootprint branchFrom referenceRequests accepted_branch)
open GeneralObservedMetadataRequests290 (requestKeys schemaFrom)
open GeneralObservedMetadataScope290 (coverage certify)
open GeneralObservedMetadataControls290 (insertInvariant)
open GeneralRebaseReceiptCollision289 (removed)

abbrev bounds : List (GeneralNominalInspection.Bounds ctx.state) := [(1,1)]

theorem actual_request_keys (choice : Bool) :
    requestKeys (referenceRequests (registry choice) ctx root parentDecl parent_checked bounds) = [0,0] := by
  cases choice <;> decide +kernel

theorem actual_scope (choice : Bool) :
    branchFootprint (registry choice) ctx root parentDecl parent_checked bounds = [6,0,0,0,0] := by
  cases choice <;> decide +kernel

theorem actual_schema_not_deferred (choice : Bool) :
    (GeneralNominalRecursiveCandidates.generated (registry choice) ctx root parentDecl parent_checked bounds).unknown =
      false := by
  cases choice <;> decide +kernel

abbrev alternate : Declaration :=
  { parentDecl with associated := [⟨0,0,.app 0 [.app 1 [.var 0]]⟩] }

theorem alternate_checked : DeclarationChecked constructors roles alternate := by
  refine ⟨?_,parent_checked.identified,parent_checked.produced,parent_checked.outputOnly,
    ?_,?_,parent_checked.countsCovered,parent_checked.paterson,parent_checked.conservative,parent_checked.captureStable⟩
  · simp [Declaration.Signature,Clause.Signature,roles,bareRole,Declared]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,normalizeArgs,normalize,
      variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors,
      GeneralDeclarationExamples.constructors]

abbrev anotherInterp := insertInvariant interp 1
abbrev anotherContext : GeneralNominalCandidates.Context := ⟨raw,anotherInterp⟩

theorem request_only_key :
    let full := branchFootprint (registry true) anotherContext root alternate alternate_checked bounds
    1 ∉ coverage raw [alternate] ∧ 1 ∈ full := by
  decide +kernel

theorem head_certificate_cannot_speak_for_schema :
    certify (coverage raw [alternate]) constructors anotherInterp (removed 1).constructors anotherInterp = .good ∧
    certify (branchFootprint (registry true) anotherContext root alternate alternate_checked bounds)
      constructors anotherInterp (removed 1).constructors anotherInterp = .disagreement ∧
    (branchFrom (registry true) raw constructors anotherInterp root alternate alternate_checked bounds).2.2.unknown = false ∧
    (branchFrom (registry true) raw (removed 1).constructors anotherInterp root alternate alternate_checked bounds).2.2.unknown = true := by
  decide +kernel

end Yulang.GeneralObservedMetadataMaterializationFixture290
