import Yulang.GeneralDeclarativeI65I74OpenTailObservations414

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.OpenTail414
open GeneralDeclarativeI65
open GeneralDeclarationPatterns (normalize)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeOutputs320 (bodyPattern)

private theorem variable_receipt_eval414 {s slots} (m : I72.Model) {c p}
    (tree : NamedMixedTree401 s slots c p) {name : Nat} {cap : Capture}
    (literal : p = .var name) (slot : slots name = some cap) :
    evaluateMixedRhs401 (actualNamedMixedRead401 m) tree = some (m.assignment cap.center).1 := by
  subst p
  cases tree with
  | binder _ direct =>
    have found := Option.some.inj (direct.property.symm.trans slot)
    simp only [evaluateMixedRhs401,actualNamedMixedRead401,Option.map_some,found]

/-- In the exact X4 input no selected event anywhere in this State can
gain a newly shaped tail through a retained output. Typed staged outputs
need an unavailable actual row; a retained variable target can only
read the very same tail center, and thus says nothing new. -/
theorem a_selected_target_at_the_open_tail_is_reflexive414 {s q child t e}
    (a : OpenInput s q) (trace : SourceTrace R6 s child t (some e))
    (i : Fin child.demand.outputs.length) (target : child.demand.outputs[i].target = a.tail)
    (m : I72.Model) :
    (e.outputs i).receipt.actualEquation m = some (a.tail,(m.assignment a.tail).1) := by
  cases trace with
  | selected _ _ selectedRule _ _ =>
    rcases (WhereCycle411.R3_local_evidence411 s child e _ selectedRule).2 with vars|typed
    · obtain ⟨n,cap,literal,slot,bound,_⟩ := vars i
      have center := (bounds_on_exact_input_are_reflexive414 a bound).symm.trans target
      have actual := variable_receipt_eval414 (s := s.core) m (e.outputs i).rhs literal slot
      simp only [NamedMixedReceipt401.actualEquation,NamedMixedOutput401.receipt,actual,
        Option.map_some,target,center]
    · obtain ⟨rhs,_,retained⟩ := typed i
      exact (no_row_for_actual_tail414 a _ retained target).elim

/-- A genuinely smaller completed support proof, if addressed at this
tail, is no source of a shaped residual either. This follows from the
actual original output receipt and does not discard the proof or any
raw equation. -/
theorem actual_completed_support_to_the_open_tail_is_only_reflexive414 {s q need rest}
    (a : OpenInput s q) (support : SupportForest R6 s (need::rest))
    (target : need.expected.original.target = a.tail) (m : I72.Model) :
    need.expected.actualEquation m = some (a.tail,(m.assignment a.tail).1) := by
  cases support with
  | cons tr _ receipt _ =>
    have addressed := (congrArg (fun e : NamedMixedReceipt401 s.core => e.original.target) receipt).trans target
    rw [← receipt]
    exact a_selected_target_at_the_open_tail_is_reflexive414 a tr _ addressed m

/-- A completed proof pointed at this open slot cannot be used as a
model-independent computation of a fixed residual: the exact same
receipt reads the different real assignments of two fitting models. -/
theorem completed_support_does_not_compute_a_fixed_residual414 {s q need rest}
    (a : OpenInput s q) (onlyOriginal : s.core.origins = [a.origin])
    (support : SupportForest R6 s (need::rest))
    (target : need.expected.original.target = a.tail) (fresh : Nat) :
    ¬ ∃ v : CommonNominalFullCarrier.Ty, ∀ m : I72.Model, Fits s m →
      need.expected.actualEquation m = some (a.tail,v) := by
  rintro ⟨v,fixed⟩
  let empty : CommonNominalFullCarrier.Ty := .emptyRecord
  let filled := CommonNominalFullCarrier.record fresh (.base .int) .emptyRecord
  have model_at (tail : CommonNominalFullCarrier.Ty) : tail = v := by
    let m := modelWithTail414 a tail
    have exact := actual_completed_support_to_the_open_tail_is_only_reflexive414 a support target m
    have same := exact.symm.trans (fixed m (any_model_tail_fits_original_input414 a onlyOriginal tail))
    exact (model_tail_is_exact414 a tail).symm.trans (Prod.mk.inj (Option.some.inj same)).2
  have impossible : empty = filled := (model_at empty).trans (model_at filled).symm
  change (.emptyRecord : CommonNominalFullCarrier.Ty) = CommonNominalFullCarrier.record fresh (.base .int) .emptyRecord at impossible
  unfold CommonNominalFullCarrier.record at impossible
  cases impossible

end Yulang.GeneralDeclarativeI65.I72.OpenTail414
