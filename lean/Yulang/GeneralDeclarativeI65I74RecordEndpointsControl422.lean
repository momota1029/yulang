import Yulang.GeneralDeclarativeI65I74RecordEndpointsRuleBoundary422

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RecordEndpoints422
open GeneralDeclarativeI65
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeWitnessDeclaredState357 (point)
open GeneralDeclarativeHead320 (byMode)
open GeneralDeclarativeBounds319 (Bound)
open GeneralDeclarativeSubstitution320 (logical)
open GeneralNominalExpressionIntervals237 (reads)
open ExplicitPick419 (pickSyntax pickCode)
open OpenTail414 (openRow)

def Read.pointCaptures {p} (r : Read p) : Nat → Capture :=
  fun n => if n = r.fieldBinder then point r.low.field
    else if n = r.residualBinder then point r.low.residual else emptyCapture403

/-- A positive old-kernel control, not a C14 implementation:
when both observations literally use the same field and residual
operands, the record is a *semantic point*. The actual lower/upper
record names may be distinct and no center row is needed. The
genuinely varying fields/tail case is not replaced by this proof. -/
theorem old_kernel_reads_distinct_root_names_at_semantic_point422 {p}
    (r : Read p) (sameField : r.high.field = r.low.field)
    (sameTail : r.high.residual = r.low.residual) :
    Nonempty (SourceHead p.state.core p.root r.decl) := by
  have capturedField : r.pointCaptures r.fieldBinder = point r.low.field := by
    simp [Read.pointCaptures]
  have capturedTail : r.pointCaptures r.residualBinder = point r.low.residual := by
    simp [Read.pointCaptures, Ne.symm r.distinct]
  have code : GeneralNominalCenteredHeadMatExpressions.translate
      (GeneralDeclarativeWitnessDeclaredState357.authoredRegistry p.state.core.current).constructors
      (GeneralSourceMetadataRows291.interpretation p.state.core.current.environment.source.snapshot)
      (pickSyntax r.low.label r.fieldBinder r.residualBinder) =
        some (pickCode r.low.label r.fieldBinder r.residualBinder) := rfl
  refine ⟨.ordered r.pointCaptures ?_⟩
  rw [r.request,r.literal]
  refine .cons (.ordinary ⟨r.ranged,_,code,.endpoints r.ranged ?_ (.whole ?_) (.whole ?_)⟩) .nil
  · intro n present
    have fields : n = r.fieldBinder ∨ n = r.residualBinder := by
      simpa [pickCode,reads] using present
    rcases fields with rfl|rfl <;>
      simp only [capturedField,capturedTail,point] <;>
      exact ⟨⟨Bound.refl _,Bound.refl _⟩,Bound.refl _,Bound.refl _⟩
  · simpa [openRow,pickCode,logical,byMode,capturedField,capturedTail,point] using r.low.row
  · simpa [openRow,pickCode,logical,byMode,capturedField,capturedTail,point,r.sameLabel,sameField,sameTail] using r.high.row

end Yulang.GeneralDeclarativeI65.I72.RecordEndpoints422
