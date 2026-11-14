import Yulang.GeneralDictionaryNominalPair178
import Yulang.GeneralNominalMergeResidual178

/-! Expose the terminal pair residual as two finite extrema equations per
linear binder. Each binder occurs twice, once at each nominal endpoint. -/
namespace Yulang.GeneralDictionaryNominalPairExtrema178
open GeneralNominalRecursiveInspection GeneralNominalRecursiveCandidates
open GeneralNominalLinearCaptureFacts GeneralDictionaryNominalPair178
open GeneralDeclarations GeneralNominalAllocation CommonNominalFullCarrier

 theorem bindings_exact (state : GeneralNominalState.State)
    (lower upper : Fin state.base.slots) (name : Nat) {n : Nat} (names : Fin n → Nat)
    (low high : Fin n → GeneralNominalInspection.Bounds state) :
    bindings state (pairReport state lower upper name names low high) =
    (List.ofFn fun i => (names i,(state.base.source (low i).1,state.base.source (low i).2))) ++
    (List.ofFn fun i => (names i,(state.base.source (high i).1,state.base.source (high i).2))) := by
  simp [bindings,pairReport,variablesReport,Report.append,List.map_append,List.map_ofFn,Function.comp_def]

 theorem occurrences_pair (state : GeneralNominalState.State)
    (lower upper : Fin state.base.slots) (name : Nat) {n : Nat} (names : Fin n → Nat)
    (distinct : Function.Injective names) (low high : Fin n → GeneralNominalInspection.Bounds state)
    (i : Fin n) :
    occurrences (bindings state (pairReport state lower upper name names low high)) (names i) =
      [(state.base.source (low i).1,state.base.source (low i).2),
       (state.base.source (high i).1,state.base.source (high i).2)] := by
  rw [bindings_exact]
  simp only [occurrences,List.filter_append,List.map_append]
  rw [filter_binding names distinct (fun j => (state.base.source (low j).1,state.base.source (low j).2)) i,
    filter_binding names distinct (fun j => (state.base.source (high j).1,state.base.source (high j).2)) i]
  rfl

/-- The fresh names themselves are fixed by the invocation and binder, not
by a chosen model or registry enumeration. -/
 theorem capture_pair (state : GeneralNominalState.State) (registry : Registry)
    (invocation key : Nat) (lower upper : Fin state.base.slots) (name : Nat)
    {n : Nat} (names : Fin n → Nat) (distinct : Function.Injective names)
    (low high : Fin n → GeneralNominalInspection.Bounds state) (i : Fin n) :
    (capture state registry invocation key
      (bindings state (pairReport state lower upper name names low high))).inputs (names i) =
    (source state registry invocation (origin invocation key 0 (names i) 0),
     source state registry invocation (origin invocation key 1 (names i) 0)) := by
  unfold capture
  dsimp only
  rw [occurrences_pair state lower upper name names distinct low high i]

/-- Explicit finite form: each fresh lower denotes the union of the two lower
bounds, and each fresh upper denotes the intersection of the two upper bounds. -/
 theorem merges_iff_pair_extrema (state : GeneralNominalState.State) (registry : Registry)
    (invocation : Nat) (declaration : Declaration)
    (lower upper : Fin state.base.slots) (name : Nat) {n : Nat} (names : Fin n → Nat)
    (distinct : Function.Injective names) (inputs : declaration.inputNames = List.ofFn names)
    (low high : Fin n → GeneralNominalInspection.Bounds state)
    (model : GeneralNominalCommonBridge.Assignment) :
    PresenceNormalForm.All CommonNominalFullCarrier.model model
      (merges state registry invocation declaration
        (bindings state (pairReport state lower upper name names low high))) ↔
    ∀ i, Equivalent
      (model (source state registry invocation (origin invocation declaration.id 0 (names i) 0))).1
      (.union (model (state.base.source (low i).1)).1 (model (state.base.source (high i).1)).1) ∧
      Equivalent
      (model (source state registry invocation (origin invocation declaration.id 1 (names i) 0))).1
      (.inter (model (state.base.source (low i).2)).1 (model (state.base.source (high i).2)).1) := by
  rw [GeneralNominalMergeResidual178.merges_iff_extrema]
  constructor
  · intro valid i
    have result := valid (names i) (by rw [inputs]; exact List.mem_ofFn.mpr ⟨i,rfl⟩)
      _ (occurrences_pair state lower upper name names distinct low high i) (by intro pair; simp)
    rw [capture_pair state registry invocation declaration.id lower upper name names distinct low high i] at result
    exact result
  · intro valid binder member bs observed nonsingle
    rw [inputs] at member
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp member
    have same := (occurrences_pair state lower upper name names distinct low high i).symm.trans observed
    rw [← same,capture_pair state registry invocation declaration.id lower upper name names distinct low high i]
    exact valid i

def Extrema (context : Context) (registry : Registry) (invocation : Nat)
    (declaration : Declaration) (shape : Shape context declaration)
    (model : GeneralNominalCommonBridge.Assignment) : Prop :=
  ∀ i, Equivalent
    (model (source context.state registry invocation (origin invocation declaration.id 0 (shape.names i) 0))).1
    (.union (model (context.state.base.source (shape.low i).1)).1
      (model (context.state.base.source (shape.high i).1)).1) ∧
    Equivalent
    (model (source context.state registry invocation (origin invocation declaration.id 1 (shape.names i) 0))).1
    (.inter (model (context.state.base.source (shape.low i).2)).1
      (model (context.state.base.source (shape.high i).2)).1)

 theorem branch_models_iff_extrema (context : Context) (registry : Registry)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : Shape context declaration)
    (inputs : declaration.inputNames = List.ofFn shape.names)
    (terminal : declaration.requirements = []) (outputs : root.demand.outputs = [])
    (model : GeneralNominalCommonBridge.Assignment)
    (models : GeneralNominalState.Models context.state model)
    (below : Subtype (model (context.state.base.source shape.lower)).1
      (model (context.state.base.source shape.upper)).1) :
    BranchModels registry context root declaration checked [(shape.lower,shape.upper)] model ↔
    Extrema context registry root.identity declaration shape model := by
  rw [branch_models_iff_merges context registry root declaration checked shape terminal outputs model models below,
    report_exact context declaration shape.lower shape.upper shape.different shape.left shape.right
      shape.recorded shape.recordedRight shape.same shape.names shape.low shape.high shape.parameters shape.parametersRight shape.query]
  exact merges_iff_pair_extrema context.state registry root.identity declaration shape.lower shape.upper
    shape.left.declaration.name shape.names shape.distinct inputs shape.low shape.high model

end Yulang.GeneralDictionaryNominalPairExtrema178
