import Yulang.GeneralDeclarativeI65I74RoleDefaultLocator420

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RoleDefault420
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration Equation)
open GeneralDictionaryAssociatedProvenance (Body)
open GeneralDeclarativeWitnessDeclaredState357 (point authoredRegistry)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralNominalCenteredHeadMatExpressions (Expr value)
open GeneralDeclarativeHead320 (environment)
open GeneralDeclarativeWhere319 (Capture)
open ExplicitPick419 (exactlyOneOutput original_binder_tree_carries_exact_three_names419
  pick_binder_fields_do_not_look_inside_the_original_value419 pickCode)
open CommonNominalFullCarrier (Equivalent)
open GeneralDeclarativeInspect321 (PatternK2)
open Checker408 (Problem Result)

def DefaultPacket.requestedName {p} (a : DefaultPacket p) : Nat :=
  p.root.demand.outputs[exactlyOneOutput p a.single].name

theorem selected_role_really_owns_the_requested_default420 {p} (a : DefaultPacket p) :
    a.declaration.decl.role = p.root.demand.role := by
  have seen : a.declaration.decl ∈ visible p.state.core p.root := by simp [a.declaration.theOnlyOne]
  exact ((visible_exact _ _ _).mp seen).2

/-- Absence is checked for the requested name, not for all equations. The
body is the one stored in the owning role's actual declaration table. -/
theorem original_default_requires_no_matching_explicit_equation420 {p} (a : DefaultPacket p) :
    (∀ e ∈ a.declaration.decl.associated, e.name ≠ a.requestedName) ∧
      ((authoredRegistry p.state.core.current).roles p.root.demand.role).assoc a.requestedName =
        some (some a.term) := by
  have fromSource := a.retained.output.supplied
  rw [a.actualBody] at fromSource
  cases fromSource with
  | default _ absent there =>
    exact ⟨absent,selected_role_really_owns_the_requested_default420 a ▸ there⟩

/-- An original explicit equation makes the affirmative default branch
impossible even when the role has a stored default and B6 evidence for it. -/
theorem successful_default_cannot_override_actual_explicit420
    {p : Problem} {r : Result} {w : DefaultWire} (accept : check p r (.roleDefault w) = true) :
    ∃ a : DefaultPacket p, r = defaultReport a ∧
      ¬ ∃ eq ∈ a.declaration.decl.associated, eq.name = a.requestedName := by
  obtain ⟨a,_,report⟩ := checked_report_uses_original_default420 accept
  refine ⟨a,report,?_⟩
  rintro ⟨eq,member,same⟩
  exact (original_default_requires_no_matching_explicit_equation420 a).1 eq member same

/-- Position zero reads the whole original argument. It does not look up
implementation head variable zero, the first field, or the residual tail. -/
theorem positional_default_reads_the_original_whole_argument420 {p} (a : DefaultPacket p) :
    a.declaration.frame.slots a.retained.output.body 0 = some (point a.rows.root) := by
  have args : p.root.demand.arguments = [point a.rows.root] := a.rows.requested
  rw [a.actualBody]
  simp [AuthoredBodyFrame393.slots,args,point]

private theorem positional_syntax420 {p} (a : DefaultPacket p) (h : a.term = .var 0) :
    normalize (GeneralDeclarativeOutputs320.bodyPattern a.retained.output.body) = .var 0 := by
  rw [a.actualBody,h]
  rfl

theorem original_typed_default_wire_preserves_all_three_point_names420 {p}
    (a : DefaultPacket p) (h : a.term = .var 0) :
    a.retained.write.typedRhs = .node 0 [0,a.rows.root,a.rows.root,a.rows.root] [] :=
  original_binder_tree_carries_exact_three_names419 a.retained.output.rhs (positional_syntax420 a h)
    (positional_default_reads_the_original_whole_argument420 a)

private theorem binder_code_uses_original_center420
    {s slots c pat n} (tree : NamedMixedTree401 s slots c pat)
    (shape : pat = .var n) {cap : Capture} (slot : slots n = some cap) :
    fixedValueCode403 tree = some (.variable cap.center) := by
  cases tree with
  | binder name stored =>
    have same := Pattern.var.inj shape
    subst n
    have ident := Option.some.inj (stored.property.symm.trans slot)
    simp [fixedValueCode403,ident]
  | record _ _ _ => cases shape
  | variant _ _ => cases shape
  | join _ _ => cases shape
  | declaredApp _ _ _ _ _ => cases shape
  | scalar _ _ _ _ => cases shape
  | emptyRecord _ _ _ => cases shape
  | exactEmpty _ _ _ => cases shape
  | pair _ _ _ _ _ => cases shape

theorem original_position_zero_reifies_the_whole_argument420 {p}
    (a : DefaultPacket p) (h : a.term = .var 0) :
    a.retained.expr = .variable a.rows.root := by
  have decoded := binder_code_uses_original_center420 a.retained.output.rhs (positional_syntax420 a h)
    (positional_default_reads_the_original_whole_argument420 a)
  exact Option.some.inj (a.retained.code.symm.trans decoded)

theorem same_fitting_model_uses_original_default_rhs420 {p}
    (a : DefaultPacket p) (m : I72.Model) (fit : Fits p.state m) :
    a.retained.output.receipt.actualEquation m =
      some (p.root.demand.outputs[exactlyOneOutput p a.single].target,
        value (environment m.assignment) .actual a.retained.expr) ∧
    Equivalent (m.assignment p.root.demand.outputs[exactlyOneOutput p a.single].target).1
      (value (environment m.assignment) .actual a.retained.expr) := by
  have reads := fixed_value_code_same_model403 a.retained.output.rhs m a.retained.expr a.retained.code
  constructor
  · simp only [NamedMixedReceipt401.actualEquation,reads,NamedMixedOutput401.receipt]
    rfl
  · exact fit.1.1.2 _ a.retained.atRow

theorem same_fitting_model_uses_whole_argument_as_default_value420 {p}
    (a : DefaultPacket p) (h : a.term = .var 0) (m : I72.Model) (fit : Fits p.state m) :
    a.retained.output.receipt.actualEquation m =
      some (p.root.demand.outputs[exactlyOneOutput p a.single].target,(m.assignment a.rows.root).1) ∧
    Equivalent (m.assignment p.root.demand.outputs[exactlyOneOutput p a.single].target).1
      (m.assignment a.rows.root).1 := by
  have exact := same_fitting_model_uses_original_default_rhs420 a m fit
  simp only [original_position_zero_reifies_the_whole_argument420 a h] at exact
  exact exact

theorem default_rhs_does_not_authorize_extra_pattern_visits420 {p} (a : DefaultPacket p) :
    ¬ PatternK2 p.state.core.current.ordinary a.rows.root
      (pickCode a.rows.x a.declaration.fieldBinder a.declaration.tailBinder) := by
  rintro ⟨site,path,cyclic⟩
  have atRoot := pick_binder_fields_do_not_look_inside_the_original_value419 path
  have args : p.root.demand.arguments = [point a.rows.root] := a.rows.requested
  exact a.rawSafe ⟨point a.rows.root,by simp [args],atRoot ▸ cyclic⟩

end Yulang.GeneralDeclarativeI65.I72.RoleDefault420
