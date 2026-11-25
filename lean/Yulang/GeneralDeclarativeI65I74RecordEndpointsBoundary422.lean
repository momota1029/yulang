import Yulang.GeneralDeclarativeI65I74RecordEndpointsProjection422

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RecordEndpoints422
open GeneralDeclarativeI65
open GeneralDeclarativeHead320 (Equation Models)
open GeneralDeclarativeWhere319 (Capture)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralDeclarativePoint320 (semantic_point)
open GeneralDeclarativeSubstitution320 (equation_read)
open CommonNominalFullCarrier (Equivalent)
open ExplicitPick419 (pickSyntax pickCode)

def NoCenterRecord {p} (r : Read p) : Prop :=
  ∀ label field tail, (⟨r.arg.center,.record label field tail⟩ : Equation) ∉
    p.state.core.current.ordinary.equations

/-- In the existing fixed Center judgment, a record at an address
without any retained record equation can only be justified by frozen
endpoint reads. Freezing is an actual semantic equality of the root
endpoints in every fitting model, not merely a name convention. -/
theorem old_record_center_without_a_row_forces_equal_endpoints422 {p}
    (r : Read p) (absent : NoCenterRecord r) (capt : Nat → Capture) {label a rest}
    (legacy : GeneralDeclarativeNormalized320.Center p.state.core.current.ordinary capt r.arg
      (pickCode label a rest))
    (m : I72.Model) (fit : Models p.state.core.current.ordinary m.assignment) :
    Equivalent (m.assignment r.arg.lower).1 (m.assignment r.arg.upper).1 := by
  change GeneralDeclarativeNormalized320.Center _ _ _ (.record label (.variable a) (.variable rest)) at legacy
  cases legacy with
  | direct source =>
    cases source with
    | structural read =>
      cases read with
      | record stored _ _ => exact False.elim (absent _ _ _ stored)
    | whole stored =>
      exact False.elim (absent _ _ _ stored)
  | endpoints _ frozen lo hi =>
    have low := equation_read lo m.assignment fit
    have high := equation_read hi m.assignment fit
    have both := semantic_point frozen m.assignment fit
    exact eqv_trans low (eqv_trans both.1
      (eqv_trans ⟨both.2.2,both.2.1⟩ ⟨high.2,high.1⟩))

/-- This inversion covers *all* cases of the fixed SourceHead for the
actual written record: nominal/deep and the special joined point
branch have incompatible written syntax. The legacy evidence cannot
be acquired just by supplying a different symbolic capture. -/
theorem original_fixed_record_source_head_forces_endpoint_equivalence422 {p}
    (r : Read p) (absent : NoCenterRecord r)
    (legacy : SourceHead p.state.core p.root r.decl)
    (m : I72.Model) (fit : Models p.state.core.current.ordinary m.assignment) :
    Equivalent (m.assignment r.arg.lower).1 (m.assignment r.arg.upper).1 := by
  cases legacy with
  | ordered capture reads =>
    rw [r.request,r.literal] at reads
    cases reads with
    | cons first _ =>
      cases first with
      | ordinary proof =>
        obtain ⟨_,expr,compiled,center⟩ := proof
        have code : GeneralNominalCenteredHeadMatExpressions.translate
            (GeneralDeclarativeWitnessDeclaredState357.authoredRegistry p.state.core.current).constructors
            (GeneralSourceMetadataRows291.interpretation p.state.core.current.environment.source.snapshot)
            (pickSyntax r.low.label r.fieldBinder r.residualBinder) =
              some (pickCode r.low.label r.fieldBinder r.residualBinder) := rfl
        have eq := Option.some.inj (compiled.symm.trans code)
        cases eq
        exact old_record_center_without_a_row_forces_equal_endpoints422 r absent capture center m fit
      | declared window _ =>
        have impossible := window.syntaxHead
        change Pattern.record r.low.label (.var r.fieldBinder) (.var r.residualBinder) =
          Pattern.app window.name window.arguments at impossible
        cases impossible
  | joined join =>
    have same := (List.cons.inj (join.head.symm.trans r.literal)).1
    have impossible := join.normalized
    rw [same] at impossible
    change Pattern.record r.low.label (.var r.fieldBinder) (.var r.residualBinder) =
      Pattern.variant join.tag
        (.join (.app join.name [.var join.firstBinder]) (.app join.name [.var join.lastBinder])) at impossible
    cases impossible

theorem genuine_nonpoint_endpoint_record_has_no_fixed_source_head422 {p}
    (r : Read p) (absent : NoCenterRecord r)
    (m : I72.Model) (fit : Models p.state.core.current.ordinary m.assignment)
    (different : ¬ Equivalent (m.assignment r.arg.lower).1 (m.assignment r.arg.upper).1) :
    ¬ Nonempty (SourceHead p.state.core p.root r.decl) := by
  rintro ⟨legacy⟩
  exact different (original_fixed_record_source_head_forces_endpoint_equivalence422 r absent legacy m fit)

end Yulang.GeneralDeclarativeI65.I72.RecordEndpoints422
