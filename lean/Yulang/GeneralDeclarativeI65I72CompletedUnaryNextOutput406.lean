import Yulang.GeneralDeclarativeI65I72CompletedUnaryExactRhs406

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72
open GeneralDeclarativeI65
open CommonRoleOutermostResolver (Tree Summarizes Result Dictionary classification_exact)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeWhere319 (Capture)

/-- The precise B6 output was reached at an ordinal of this very
selected source trace. Do not identify a completed producer merely
by a dictionary key, receipt value or independent old derivation.
This retains both the old Event and the new completed-native root
without trying to erase the latter to an authored ModeWindow. -/
inductive ScopedOutputRead406 (s : State) (q : Request) :
    {t : Tree} → ScopedSource406 s q t → Fin q.demand.outputs.length →
      NamedMixedReceipt401 s.core → Type where
  | prior {i : Fin q.demand.outputs.length} {e : Event s q}
      (trace : SourceTrace PriorSource406 s q t (some e)) :
      ScopedOutputRead406 s q (.prior trace) i (e.outputs i).receipt
  | completed {i : Fin q.demand.outputs.length}
      (event : CompletedInvocation406 s q trees) :
      ScopedOutputRead406 s q (.completed event) i (event.body.output i).receipt

theorem read_exact_output_of_actual_selected_trace406 {s q t d} (trace : ScopedSource406 s q t)
    (done : Summarizes t (.selected d)) (i : Fin q.demand.outputs.length) :
    ∃ receipt, Nonempty (ScopedOutputRead406 s q trace i receipt) := by
  cases trace with
  | prior given =>
    cases given with
    | rootK2 => cases done
    | other v _ _ _ => cases v <;> cases done
    | selected e raw rule forest children =>
      exact ⟨(e.outputs i).receipt,⟨.prior (.selected e raw rule forest children)⟩⟩
  | completed event => exact ⟨(event.body.output i).receipt,⟨.completed event⟩⟩

theorem exact_scoped_receipt_keeps_its_request_and_ordinal406 {s q t}
    {trace : ScopedSource406 s q t} {i : Fin q.demand.outputs.length} {r}
    (found : ScopedOutputRead406 s q trace i r) :
    r.occurrence = q.occurrence ∧ r.outputOrdinal = i.val ∧ r.original = q.demand.outputs[i] := by
  cases found <;> exact ⟨rfl,rfl,rfl⟩

/-- This makes an already built completed-native rule an exact
candidate producer for a future source extension. The new raw
retained equation is proved directly from its original typed body;
actual repeated new-native selection is not claimed by this theorem. -/
theorem even_new_completed_trace_protects_an_original_nominal_output406 {s q t d}
    {trace : ScopedSource406 s q t} (done : Summarizes t (.selected d))
    {i : Fin q.demand.outputs.length} {r} (found : ScopedOutputRead406 s q trace i r)
    {a : Capture} {key : Nat} {args : List Expr}
    (target : r.original.target = a.lower)
    (head : DeclaredHead404 key r.rhs)
    (value : fixedValueCode403 r.rhs = some (.nominal key args)) :
    (⟨a.lower,.nominal key args⟩ : Equation) ∈ s.core.current.ordinary.equations := by
  cases found with
  | prior earlier =>
    rename_i e
    let need : OutputNeed s := needOfSelected404 e d i
    let literal : LiteralInputNeed404 s a need := ⟨key,args,target,head,value⟩
    have complete : ExactOutputSupport PriorSource406 s need := ⟨_,_,earlier,done,rfl⟩
    exact completed_input_owns_retained_nominal404 authored_native_source_keeps_own_fixed_rows405 literal complete
  | completed event =>
    obtain ⟨ordinary,encoded,retained⟩ := event.fixed i
    have same := Option.some.inj (encoded.symm.trans value)
    have nominalTarget : q.demand.outputs[i].target = a.lower := target
    rw [same,nominalTarget] at retained
    exact retained

theorem scoped_actual_completion_does_not_use_a_pending_trace406 {s q t d}
    (_source : ScopedSource406 s q t) (done : Summarizes t (.selected d)) :
    ¬Summarizes t .pending := by
  intro waits
  have same := (classification_exact t (.selected d)).mpr done
  have different := (classification_exact t .pending).mpr waits
  rw [same] at different
  cases different

end Yulang.GeneralDeclarativeI65.I72
