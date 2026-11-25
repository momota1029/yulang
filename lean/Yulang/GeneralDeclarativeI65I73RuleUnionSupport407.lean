import Yulang.GeneralDeclarativeI65I73RuleUnionNormal407

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72
open GeneralDeclarativeI65
open CommonRoleOutermostResolver (Result Dictionary Tree Summarizes All₂)
open CommonNominalFullCarrier (Equivalent)

private theorem R0_original_event_keeps_fixed_rows407 {s q t e}
    (trace : SourceTrace R0 s q t (some e)) : RetainedVariableOutputs403 e ∨ RetainedTypedValueRows403 e := by
  cases trace with
  | selected _ _ elected _ _ => exact R0_keeps_fixed_rows407 _ _ _ _ elected

/-- Locate the original receipt inside an actual mixed recursive
proof, then get the fixed target meaning in the same model.
The selected producer's support proof is not inserted into the
consumer dictionary or taken to be a successful where child. -/
theorem R0_original_support_on_one_same_model_ledger407 {s needs need}
    (forest : SupportForest R0 s needs) (index : Nat) (atIndex : needs[index]? = some need) :
    ∃ producer : ExactOutputSupport R0 s need,
      ∃ tree : I72.GeneralTree producer.source need.dictionary,
        CanonicalReplay tree tree.ledger ∧
        need.expected.occurrence = need.producer.occurrence ∧
        need.expected.outputOrdinal = need.ordinal.val ∧
        need.expected.original = need.producer.demand.outputs[need.ordinal] ∧
        ∀ m, Fits s m → DictionaryEvidence s m need.producer need.dictionary ∧
          ∃ ty, need.expected.actualEquation m = some (need.expected.original.target,ty) ∧
            Equivalent (m.assignment need.expected.original.target).1 ty := by
  let producer := forest.atOriginal index atIndex
  obtain ⟨tree,replay,_,whole⟩ := R0_trace_has_one_canonical_ledger407 producer.source producer.completion
  have occ := congrArg NamedMixedReceipt401.occurrence producer.sameTypedOutput.symm
  have ordinal := congrArg NamedMixedReceipt401.outputOrdinal producer.sameTypedOutput.symm
  have wanted : need.expected.original = need.producer.demand.outputs[need.ordinal] :=
    congrArg NamedMixedReceipt401.original producer.sameTypedOutput.symm
  refine ⟨producer,tree,replay,occ,ordinal,wanted,fun m fit => ⟨whole m fit,?_⟩⟩
  have fixed := R0_original_event_keeps_fixed_rows407 producer.source
  have thisTarget : FixedTargets m producer.event := fixed.elim
    (fun a => retained_variable_targets_sound403 a m fit)
    (fun b => retained_typed_rows_satisfy_fixed_targets403 b m fit)
  obtain ⟨ty,read,related⟩ := thisTarget need.ordinal
  rw [producer.sameTypedOutput,← wanted] at read
  exact ⟨ty,read,by rw [wanted]; exact related⟩

/-- A mixed producer/where combination is an actual new C402 trace,
not just a disjunction of homogeneous top-level Classifies
statements. The parent primitive is the same approved supported
variable rule; its exact output proof can come from the larger
authored-native family. -/
theorem actual_mixed_native_support_enters_variable_rule407 {s q p t original d e trees dKids}
    (source : SourceTrace authoredNativeSelectedSource405 s p t (some original))
    (exactDone : Summarizes t (.selected d)) (i : Fin p.demand.outputs.length)
    (parent : supportedVariableSource404.elected s q e [⟨p,d,i,(original.outputs i).receipt⟩])
    (safe : ¬ RootCycle s q) (whereTree : WhereForest R0 s e.kids trees)
    (whereDone : All₂ Summarizes trees (dKids.map Result.selected)) :
    ∃ trace : SourceTrace R0 s q (.selected e.frame.decl.id trees) (some e),
      Classifies R0 s q (.selected (.node e.frame.decl.id dKids)) ∧
      ∃ tree : I72.GeneralTree trace (.node e.frame.decl.id dKids),
        CanonicalReplay tree tree.ledger ∧
        ∀ m, Fits s m → DictionaryEvidence s m q (.node e.frame.decl.id dKids) := by
  let childSource := include_fixed_family_trace_R0 .authoredNative source
  let dependency : SupportForest R0 s [⟨p,d,i,(original.outputs i).receipt⟩] :=
    .cons childSource exactDone rfl .nil
  let trace : SourceTrace R0 s q (.selected e.frame.decl.id trees) (some e) :=
    .selected e safe ⟨supportedVariableSource404,.supported,parent⟩ dependency whereTree
  have complete : Summarizes (.selected e.frame.decl.id trees) (.selected (.node e.frame.decl.id dKids)) :=
    .selected whereDone (.selected rfl)
  obtain ⟨tree,ledger,_,models⟩ := R0_trace_has_one_canonical_ledger407 trace complete
  exact ⟨trace,⟨_,_,⟨trace⟩,complete⟩,tree,ledger,models⟩

end Yulang.GeneralDeclarativeI65.I72
