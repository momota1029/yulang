import Yulang.GeneralDictionaryChildCaptureTransport
import Yulang.GeneralDictionaryNonpointStrict

/-! A checked nonterminal declaration really changes its child interval while
retaining the child identity. This is an emitter/Fits regression, not yet a
selected child or operational output-installation theorem. -/
set_option linter.unusedSimpArgs false
namespace Yulang.GeneralDictionaryChildCaptureExample
open GeneralDeclarations GeneralDeclarationPatterns GeneralDeclarationDemands
open GeneralNominalAllocation GeneralNominalCaptureMerges GeneralNominalMaterialization
open GeneralDictionarySemanticCollapseSchema GeneralDictionaryNonpointStrict
open GeneralDictionaryChildCaptureTransport CommonNominalFullCarrier
abbrev clause : Clause := ⟨12,0,[.var 7],[]⟩
abbrev parent : Declaration := ⟨31,0,[.app 0 [.app 0 [.var 7]]],[clause],[],[]⟩
abbrev catalogue : Registry := ⟨source.constructors,roles,[parent]⟩
theorem clause_signature : clause.Signature roles := by
  simp [Clause.Signature,clause,roles,GeneralDeclarationExamples.roles,GeneralDeclarationExamples.bareRole]
theorem parent_checked : DeclarationChecked catalogue.constructors roles parent := by
  constructor
  · simp [Declaration.Signature,Clause.Signature,Declared,roles,GeneralDeclarationExamples.roles,
      GeneralDeclarationExamples.bareRole,parent,clause]
  · simp [Declaration.Identified,Declaration.outputNames,parent,clause]
  · simp [Declaration.Produced,parent]
  · simp [Declaration.OutputOnly,Declaration.outputNames,parent]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,parent,clause,
      normalizeArgs,normalize,variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,parent,clause,catalogue,GeneralDictionaryNonpointStrict.source,
      GeneralDeclarationExamples.constructors]
  · intro child member
    have eq := List.mem_singleton.mp member
    subst child
    exact ⟨rfl,rfl⟩
  · intro child member
    have eq := List.mem_singleton.mp member
    subst child
    exact (checkSmaller_exact _ _).mp (by decide +kernel)
  · intro child member
    have eq := List.mem_singleton.mp member
    subst child
    unfold ConservativeSmaller
    decide +kernel
  · intro child member capture
    have eq := List.mem_singleton.mp member
    subst child
    constructor
    · simp [parent,clause,counted,substArgs,Pattern.subst,normalizeArgs,normalize,
        encodeArgs,Pattern.encode,Roles.argsSize,Roles.Term.size]
      omega
    · intro name
      simp [parent,clause,counted,substArgs,Pattern.subst,normalizeArgs,normalize,
        encodeArgs,Pattern.encode,Roles.argsOccurrences,Roles.Term.occurrences]

noncomputable def oldChild := childDemand parent clause clause_signature
  (oldCapture shape catalogue root.identity parent)
  (allocation source catalogue root.identity parent.id clause)
noncomputable def currentChild := childDemand parent clause clause_signature
  (newCapture shape catalogue root.identity parent)
  (allocation revision.snapshot catalogue root.identity parent.id clause)

theorem old_argument : oldChild.arguments ⟨0,by exact Nat.zero_lt_succ 0⟩ = (loId,hiId) := by
  change (oldCapture shape catalogue root.identity parent).inputs 7 = (loId,hiId)
  unfold oldCapture
  rw [GeneralDictionarySemanticCollapse.bindings_before]
  rfl

theorem current_argument : currentChild.arguments ⟨0,by exact Nat.zero_lt_succ 0⟩ = (3,4) := by
  change (newCapture shape catalogue root.identity parent).inputs 7 = (3,4)
  unfold newCapture
  rw [GeneralDictionarySemanticCollapse.bindings_after]
  rfl

theorem outputs_equal : currentChild.outputs = oldChild.outputs := rfl

theorem child_fits_strictly_enlarges :
    Fits model (currentChild.arguments ⟨0,by exact Nat.zero_lt_succ 0⟩) .bottom ∧
      ¬ Fits model (oldChild.arguments ⟨0,by exact Nat.zero_lt_succ 0⟩) .bottom := by
  rw [old_argument,current_argument]
  exact fits_strictly_enlarges

/-- Identity alone cannot justify substituting the complete demand. -/
theorem child_demands_differ : currentChild ≠ oldChild := by
  intro same
  have args : currentChild.arguments ⟨0,by exact Nat.zero_lt_succ 0⟩ = oldChild.arguments ⟨0,by exact Nat.zero_lt_succ 0⟩ := by
    have heq := (GeneralSourceState.Demand.mk.inj same).2.1
    exact congrFun (eq_of_heq heq) ⟨0,by exact Nat.zero_lt_succ 0⟩
  exact child_fits_strictly_enlarges.2 (args ▸ child_fits_strictly_enlarges.1)

noncomputable def oldOccurrence := GeneralDictionaryEmissionPlans.occurrence
  (frame source catalogue root.identity [])
  (emit root.identity parent clause clause_signature (oldCapture shape catalogue root.identity parent)
    (allocation source catalogue root.identity parent.id clause))
noncomputable def currentOccurrence := GeneralDictionaryEmissionPlans.occurrence
  (frame revision.snapshot catalogue root.identity [])
  (emit root.identity parent clause clause_signature (newCapture shape catalogue root.identity parent)
    (allocation revision.snapshot catalogue root.identity parent.id clause))

theorem actual_old_children :
    children GeneralDictionaryNonpointStrict.source catalogue root parent parent_checked
      (GeneralNominalRecursiveInspection.bindings start.context.state
        (GeneralNominalRecursiveInspection.inspect start.context.state
          (GeneralDictionarySemanticCollapse.query shape) (shape.root,shape.root) none)) = [oldOccurrence] := by
  let fr := frame (roles := roles) GeneralDictionaryNonpointStrict.source catalogue root.identity
      (GeneralNominalRecursiveInspection.bindings start.context.state
        (GeneralNominalRecursiveInspection.inspect start.context.state
          (GeneralDictionarySemanticCollapse.query shape) (shape.root,shape.root) none))
  have perm := (GeneralCanonicalChildOrder.canonicalEmit_perm root.identity parent parent_checked
    (fr.capture parent.id) (fr.allocation parent.id)).map (GeneralDictionaryEmissionPlans.occurrence fr)
  have left : (emitAll root.identity parent parent_checked.signature
      (fr.capture parent.id) (fr.allocation parent.id)).map
      (GeneralDictionaryEmissionPlans.occurrence fr) = [oldOccurrence] := rfl
  rw [left] at perm
  exact List.perm_singleton.mp perm.symm

theorem actual_current_children :
    children revision.snapshot catalogue root parent parent_checked
      (GeneralNominalRecursiveInspection.bindings revision.snapshot
        (GeneralNominalRecursiveInspection.inspect revision.snapshot
          (GeneralDictionarySemanticCollapse.query shape) (shape.root,shape.root) none)) = [currentOccurrence] := by
  let fr := frame (roles := roles) revision.snapshot catalogue root.identity
      (GeneralNominalRecursiveInspection.bindings revision.snapshot
        (GeneralNominalRecursiveInspection.inspect revision.snapshot
          (GeneralDictionarySemanticCollapse.query shape) (shape.root,shape.root) none))
  have perm := (GeneralCanonicalChildOrder.canonicalEmit_perm root.identity parent parent_checked
    (fr.capture parent.id) (fr.allocation parent.id)).map (GeneralDictionaryEmissionPlans.occurrence fr)
  have left : (emitAll root.identity parent parent_checked.signature
      (fr.capture parent.id) (fr.allocation parent.id)).map
      (GeneralDictionaryEmissionPlans.occurrence fr) = [currentOccurrence] := rfl
  rw [left] at perm
  exact List.perm_singleton.mp perm.symm

theorem identity_equal : currentOccurrence.identity = oldOccurrence.identity := rfl

theorem actual_nonterminal_boundary :
    DeclarationChecked catalogue.constructors roles parent ∧
    parent.requirements = [clause] ∧
    currentOccurrence.identity = oldOccurrence.identity ∧
    currentOccurrence.demand ≠ oldOccurrence.demand ∧
    Fits model (currentChild.arguments ⟨0,by exact Nat.zero_lt_succ 0⟩) .bottom ∧
    ¬ Fits model (oldChild.arguments ⟨0,by exact Nat.zero_lt_succ 0⟩) .bottom :=
  ⟨parent_checked,rfl,identity_equal,child_demands_differ,child_fits_strictly_enlarges⟩
end Yulang.GeneralDictionaryChildCaptureExample
