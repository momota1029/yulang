import Yulang.GeneralDeclarativeI65I74PlainMergedEntry416

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.PlainMerged416
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeSubstitution320 (EquationRead logical)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry point)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans variant_congr)
open CommonNominalFullCarrier (Equivalent variant)

/-- A model-sound fact about the same whole payload. The extra
literal read witness is not a special condition on this equality. -/
theorem canonical_head_meaning_without_redundant_read_row416 {s : I72.State}
    {root tag payload : Nat} (row : variantRow416 root tag payload ∈ s.core.current.ordinary.equations)
    (m : I72.Model) (fit : Fits s m) :
    Equivalent (m.assignment root).1
      (variant tag (.union (m.assignment payload).1 (m.assignment payload).1)) := by
  have head := fit.1.1.2 _ row
  change Equivalent (m.assignment root).1 (variant tag (m.assignment payload).1) at head
  exact eqv_trans head (variant_congr tag (self_join_is_semantically_idempotent416 _))

def HasOriginalJoin (s : GeneralDeclarativeHead320.State) (slot : Nat) : Prop :=
  ∃ l r : Expr, (⟨slot,.join l r⟩ : Equation) ∈ s.equations

theorem original_join_read_needs_a_literal_join_row416 {s capture mode slot first last}
    (read : EquationRead s capture mode slot (.join first last)) :
    HasOriginalJoin s slot := by
  cases read with
  | whole recorded => exact ⟨logical capture mode first,logical capture mode last,recorded⟩
  | structural derivation =>
    cases derivation with
    | join recorded _ _ => exact ⟨_,_,recorded⟩

/-- The fixed original-head carrier consumes an actual raw join row for this
written head even though all models already know the idempotence. It
cannot quietly use the covariant nominal Joined case instead. -/
theorem exact_plain_source_head_needs_a_real_join416 {s : GeneralDeclarativeI65.State}
    {q : I72.Request} {d : Declaration} {root tag a b : Nat} (different : a ≠ b)
    (args : q.demand.arguments = [point root])
    (literal : d.head = [sourceX6 tag a b])
    (head : SourceHead s q d) : HasOriginalJoin s.current.ordinary root := by
  have normalized := two_literal_plain_arms_normalize_to_one_actual_tag416 tag a b different
  cases head with
  | ordered captures reads =>
    rw [args,literal] at reads
    cases reads with
    | cons one _ =>
      cases one with
      | declared view _ =>
        have clash := normalized.symm.trans view.syntaxHead
        cases clash
      | ordinary proof =>
        obtain ⟨_,exp,compiled,actual⟩ := proof
        have original : translate (authoredRegistry s.current).constructors
            (interpretation s.current.environment.source.snapshot) (sourceX6 tag a b) =
            some (.join (.variant tag (.variable a)) (.variant tag (.variable b))) := rfl
        have computed := Option.some.inj (compiled.symm.trans original)
        subst exp
        cases actual with
        | direct read => exact original_join_read_needs_a_literal_join_row416 read
        | endpoints _ _ lower _ => exact original_join_read_needs_a_literal_join_row416 lower
  | joined aligned =>
    have wrote := (List.cons.inj (literal.symm.trans aligned.head)).1
    have known := normalized.symm.trans ((congrArg normalize wrote).trans aligned.normalized)
    have clash := Pattern.variant.inj known
    have arm := Pattern.join.inj clash.2
    cases arm.1

end Yulang.GeneralDeclarativeI65.I72.PlainMerged416
