import Yulang.GeneralDeclarativeI65I74NestedInvariantEntry440

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.NestedInvariant440
open GeneralDeclarativeI65
open GeneralDeclarativeWhere319 (Capture)
open CommonNominalFullCarrier (Equivalent nominal nominal_regular_invariant_exact)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_symm eqv_trans)
open CommonRecursiveNominalIntervals (Endpoint Bounds)
open GeneralDeclarations (Declaration)
open GeneralDeclarationPatterns (Pattern)
open Checker408 (Problem Result)

theorem original_nested_same_visible_selection440 {s q d e}
    (a : Original s q d) (b : Original s q e) :
    d = e ∧ a.arg = b.arg ∧ a.binder = b.binder := by
  have dEq := (List.cons.inj (a.only.symm.trans b.only)).1
  have argEq := (List.cons.inj (a.asked.symm.trans b.asked)).1
  cases dEq
  have same := (List.cons.inj (a.written.symm.trans b.written)).1
  have bind := (Pattern.app.inj same).2
  have inside := (Pattern.app.inj (List.cons.inj bind).1).2
  exact ⟨rfl,argEq,Pattern.var.inj (List.cons.inj inside).1⟩

theorem original_nested_same_fitting_bounds440 {s q d e}
    (a : Original s q d) (b : Original s q e) (m : I72.Model) (fit : I72.Fits s m) :
    a.low = b.low ∧ a.high = b.high := by
  have arg := (original_nested_same_visible_selection440 a b).2.1
  have first := (a.allOriginalOrigins m fit).1
  have last := (b.allOriginalOrigins m fit).1
  rw [arg] at first
  have endpoint := Option.some.inj (first.symm.trans last)
  change Endpoint.nominal a.outer [.inl (.point (nestedInner a.inner a.low a.high))] =
    .nominal b.outer [.inl (.point (nestedInner b.inner b.low b.high))] at endpoint
  have inner := Bounds.point.inj (Sum.inl.inj (List.cons.inj (Endpoint.nominal.inj endpoint).2).1)
  change Endpoint.nominal a.inner [.inl (.interval (loTerm a.low) (loTerm a.high))] =
    .nominal b.inner [.inl (.interval (loTerm b.low) (loTerm b.high))] at inner
  have leaves := Bounds.interval.inj (Sum.inl.inj (List.cons.inj (Endpoint.nominal.inj inner).2).1)
  exact ⟨Core.PresenceGeneration.TyTerm.var.inj (Endpoint.ordinary.inj leaves.1),
    Core.PresenceGeneration.TyTerm.var.inj (Endpoint.ordinary.inj leaves.2)⟩

private theorem unary_payload_equiv440 {first last : Nat} {a b : CommonNominalFullCarrier.Ty}
    (h : Equivalent (nominal first [.inl a]) (nominal last [.inl b])) :
    Equivalent a b :=
  ((nominal_regular_invariant_exact _ _ _ _).mp h.1).2.2 0 _ _ rfl rfl

/-- The input rules still read exact original raw rows. Two different
    eligible locators may name distinct centers, but either is constrained
    by the same fitting original nominal data. No premise equates names. -/
theorem original_nested_fitting_center_values_agree440 {s q d e}
    (a : Original s q d) (b : Original s q e) (m : I72.Model) (fit : I72.Fits s m) :
    Equivalent (m.assignment a.center).1 (m.assignment b.center).1 := by
  have arg := (original_nested_same_visible_selection440 a b).2.1
  have outA : Equivalent (m.assignment a.arg.lower).1
      (nominal a.outer [.inl (m.assignment a.site).1]) := fit.1.1.2 _ a.rawOuter
  have outB : Equivalent (m.assignment b.arg.lower).1
      (nominal b.outer [.inl (m.assignment b.site).1]) := fit.1.1.2 _ b.rawOuter
  rw [arg] at outA
  have inner := unary_payload_equiv440 (eqv_trans (eqv_symm outA) outB)
  have inA : Equivalent (m.assignment a.site).1
      (nominal a.inner [.inl (m.assignment a.center).1]) := fit.1.1.2 _ a.rawInner
  have inB : Equivalent (m.assignment b.site).1
      (nominal b.inner [.inl (m.assignment b.center).1]) := fit.1.1.2 _ b.rawInner
  exact unary_payload_equiv440 (eqv_trans (eqv_symm inA) (eqv_trans inner inB))

theorem two_accepted_nested_wires_agree440 {p : Problem} {r t : Result} {w v : Wire}
    (checked : check p r (.nested w) = true) (again : check p t (.nested v) = true) :
    r = t ∧ ∃ (d e : Declaration) (a : Original p.state p.root d) (b : Original p.state p.root e),
      a.binder = b.binder ∧
      ∀ (m : I72.Model), I72.Fits p.state m →
        a.low = b.low ∧ a.high = b.high ∧
        Equivalent (m.assignment a.center).1 (m.assignment b.center).1 := by
  obtain ⟨d,_,a,_,rOriginal⟩ := checked_nested_returns_original_report440 checked
  obtain ⟨e,_,b,_,tOriginal⟩ := checked_nested_returns_original_report440 again
  have same := original_nested_same_visible_selection440 a b
  refine ⟨rOriginal.trans ((congrArg leafReport same.1).trans tOriginal.symm),
    ⟨d,e,a,b,same.2.2,fun m fit => ?_⟩⟩
  have bounds := original_nested_same_fitting_bounds440 a b m fit
  exact ⟨bounds.1,bounds.2,original_nested_fitting_center_values_agree440 a b m fit⟩

end Yulang.GeneralDeclarativeI65.I72.NestedInvariant440
