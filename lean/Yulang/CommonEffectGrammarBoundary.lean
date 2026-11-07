import Yulang.CommonEffectDeclarationInterpretation
import Yulang.PresenceGeneratedChildGrammar

/-! A finite well-kinded operation signature can exceed the old presence
solver's generated child grammar. This is not a counterexample to B3; it
prevents silently using the old grammar theorem for all declarations. -/
namespace Yulang.CommonEffectGrammarBoundary
open Core.PresenceGeneration
open CommonEffectRequestGeneration

/-- A legal value-kind signature with no operation-local variables. -/
def acceptsAny : Declaration α where
  locals := 0
  key := 7
  extra := []
  input := .top
  output := .base .unit

@[simp] theorem acceptsAny_wellKinded : (acceptsAny : Declaration α).wellKinded = true := rfl

/-- The old syntactic invariant lifted through the new finite binders. -/
def OldChildGrammar : Constraint scopes α → Prop
  | .core body => PresenceGeneratedChildGrammar.GoodFormula body
  | .rowLe _ _ => True
  | .and first last => OldChildGrammar first ∧ OldChildGrammar last
  | .existsSlot body => OldChildGrammar body
  | .existsTypes _ body => OldChildGrammar body
  | .forallTypes _ body => OldChildGrammar body

/-- Every scope count, every ambient variable type and every output. The
literal payload's generated upper endpoint is top, outside the old grammar. -/
theorem generated_request_not_old_child_grammar (out : CompTerm α) :
    ¬ OldChildGrammar (generateRequest (scopes := scopes) [] acceptsAny (.lit .unit) out) := by
  simp [OldChildGrammar, generateRequest, requestBody, acceptsAny, generate,
    Formula.compLe, PresenceGeneratedChildGrammar.GoodFormula,
    PresenceGeneratedChildGrammar.lower, PresenceGeneratedChildGrammar.upper,
    TyTerm.rename]

private theorem unit_le_top : Common.Subtype (.base .unit) .top := by
  intro depth
  apply (CommonFinite.producerLe_iff_probe _ _).mpr
  intro rank environment observation accepted
  cases rank <;> cases observation <;>
    simp_all [Common.observeTy, CommonSyntax.Layer.evalAt, CommonFinite.ProbeAt,
      CommonFinite.ProbeStep, CommonFinite.MaskedProbeStep]

/-- The grammar failure is not a type error: the independent request rule
accepts the unit payload at top, with exactly its required operation row. -/
theorem acceptsAny_request_typable (assignment : α → Computation) :
    RequestTyping scopes assignment acceptsAny [] (.lit .unit)
      (.base .unit, (CommonSignedRows.commonAlgebra scopes).head 7) := by
  apply RequestTyping.intro (fun index => Fin.elim0 index) Common.rowEmpty
  · apply Typing.lit
    exact ⟨unit_le_top, Common.rowLe_refl _⟩
  · exact Common.subtype_refl _
  · intro occurrence present
    change False ∨ ((CommonSignedRows.commonAlgebra scopes).head 7 occurrence ∨ False) at present
    exact present.elim False.elim (fun present => present.elim id False.elim)

/-- Same example at the actual finite constraint interpretation. -/
theorem acceptsAny_request_satisfiable (assignment : α → Computation) (out : CompTerm α)
    (result : out.eval Common.model assignment =
      (.base .unit, (CommonSignedRows.commonAlgebra scopes).head 7)) :
    (generateRequest (scopes := scopes) [] acceptsAny (.lit .unit) out).Holds assignment := by
  apply (generate_request_exact [] [] assignment (EnvRel.nil _ _) acceptsAny (.lit .unit) out).mpr
  rw [result]
  exact acceptsAny_request_typable assignment
end Yulang.CommonEffectGrammarBoundary
