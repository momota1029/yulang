import Yulang.GeneralDeclarativeI65ActualUnaryDispatch379
import Yulang.GeneralDeclarativeWitnessNativeAmbiguity361

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65
open GeneralDeclarativeWitnessNestedInstall360 (Run)
open GeneralDeclarativeWitnessSequentialNative360 (Sequence)
open GeneralDeclarativeWitnessNativePortTransport361 (Port)
open GeneralDeclarativeWitnessNativeLeafClassify361 (visible)
open GeneralDeclarativeWitnessNativeAmbiguity361 (inspect compare)
open GeneralDeclarativeWitnessNestedLeaf361 (writerSlots)
open GeneralDeclarativeWitnessNativePipeline360 (wire)
open GeneralDeclarativeWitnessModeCoverage357 (checkDecl)
open GeneralDeclarativeWitnessMixedDependency361 (exactGraph)
open GeneralDeclarativeWitnessNativeRelease360 (ReleaseAuthority)
open GeneralDeclarativeWitnessNativeNestedMatch361 (read)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralDeclarations (Declaration)

variable {negative : Bool} {r : Run negative} {s : Sequence r} {gate : ReleaseAuthority}
  {inputWire : GeneralDeclarativeWitnessNativeDirectSource361.Wire}

theorem actual_c361_inspect_follows_entered_child
    (_port : Port s gate inputWire)
    {row : Declaration} {pattern : Pattern}
    (written : row.head.map normalize = [pattern])
    (declared : checkDecl r.env row = true)
    (terminal : row.requirements = [] ∧ row.associated = [] ∧ s.receiver.outputs = [])
    (chosen : UnaryDispatch r.env (wire negative).route r.typed.write.code pattern) :
    (inspect r s.receiver row).isSome =
      (read r.env (writerSlots r) chosen.fromRoute chosen.fromCode chosen.fromPattern).isSome := by
  have entered := unary_dispatch_recursive_success_iff (locals := writerSlots r) chosen
  refine Eq.trans ?_ entered
  unfold inspect
  split
  · rename_i actual exactPattern
    have same := List.cons.inj (exactPattern.symm.trans written)
    obtain ⟨rfl,_⟩ := same
    cases checked : read r.env (writerSlots r) (wire negative).route r.typed.write.code actual <;>
      simp [declared,terminal]
  · rename_i impossible
    exact False.elim (impossible pattern written)

/-- The already-defined finite scanner opens neither candidate when
the existing scoped graph gate fails. This is not a general K2 result. -/
theorem actual_c361_graph_gate_precedes_both_reads
    (port : Port s gate inputWire) {a b : Declaration}
    (two : GeneralDeclarativeWitnessNativeLeafClassify361.visible s = [a,b]) (different : a.id ≠ b.id)
    (notSafe : exactGraph s = false) :
    compare port = none := by
  unfold GeneralDeclarativeWitnessNativeAmbiguity361.compare
  split
  · rename_i a' b' here
    have same := List.cons.inj (here.symm.trans two)
    obtain ⟨rfl,tail⟩ := same
    have eq := (List.cons.inj tail).1
    subst b'
    simp [different,notSafe]
  · rfl

/-- The actual option continuation uses the second source row only
after a matched first row. A scanner miss is not a language verdict. -/
theorem actual_c361_scans_the_second_only_after_first
    (port : Port s gate inputWire) {a b : Declaration}
    (two : GeneralDeclarativeWitnessNativeLeafClassify361.visible s = [a,b]) (different : a.id ≠ b.id)
    (safe : exactGraph s = true) :
    (compare port).isSome =
      ((inspect r s.receiver a).isSome && (inspect r s.receiver b).isSome) := by
  unfold GeneralDeclarativeWitnessNativeAmbiguity361.compare
  split
  · rename_i a' b' here
    have same := List.cons.inj (here.symm.trans two)
    obtain ⟨rfl,tail⟩ := same
    have eq := (List.cons.inj tail).1
    subst b'
    cases first : inspect r s.receiver a' <;> cases second : inspect r s.receiver b <;>
      simp [different,safe]
  · rename_i impossible
    exact False.elim (impossible a b two)

/-- Join the actual checked physical input and literal first candidate
to the concrete scanner's real child precondition. Neither a possible
port nor a whole returned dictionary is used as proof of entry. -/
theorem first_authored_unary_entry_before_second_candidate
    (port : Port s gate inputWire) {a b : Declaration} {pat : Pattern}
    (listed : GeneralDeclarativeWitnessNativeLeafClassify361.visible s = [a,b])
    (different : a.id ≠ b.id) (graph : exactGraph s = true)
    (written : a.head.map normalize = [pat]) (declared : checkDecl r.env a = true)
    (bodyShape : a.requirements = [] ∧ a.associated = [] ∧ s.receiver.outputs = [])
    (entered : UnaryDispatch r.env (wire negative).route r.typed.write.code pat) :
    s.receiver.arguments[inputWire.operandPosition]? = some s.place ∧
      port.release.released.stored = r.typed.write ∧
      (compare port).isSome =
        ((read r.env (writerSlots r) entered.fromRoute entered.fromCode entered.fromPattern).isSome &&
          (inspect r s.receiver b).isSome) := by
  refine ⟨port.atInput,port.release.same,?_⟩
  rw [actual_c361_scans_the_second_only_after_first port listed different graph,
    actual_c361_inspect_follows_entered_child port written declared bodyShape entered]

end Yulang.GeneralDeclarativeI65
