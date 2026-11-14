import Yulang.GeneralNominalCenteredHeadMatStepChildReadback

/-! The old inspection-label domain is narrower than total materialization.
These are syntax and representation statements, not operational traces. -/
namespace Yulang.GeneralNominalCenteredHeadMatLabelDomain
open GeneralDeclarationPatterns GeneralNominalGroundAccessibility
open GeneralNominalOriginTerms GeneralNominalCompoundReadback
open GeneralNominalCenteredHeadWFSource

def exactTail (label scalarKey emptyKey : Nat) : Pattern :=
  .record label (.app scalarKey []) (.app emptyKey [])

theorem covered (label scalarKey emptyKey : Nat) :
    GeneralDeclarationPatterns.covered (normalize (exactTail label scalarKey emptyKey)) = true := rfl

theorem quote_not_deferred (term : Expr Nat) (pattern : Pattern) :
    quote term ≠ .deferred pattern := by
  cases term with
  | leaf => simp [quote]
  | node test children => cases test <;> simp [quote]

theorem no_old_closed_term (context : GeneralNominalCandidates.Context)
    (primitive : context.interpretation.primitives emptyKey = some .exactEmpty) (label scalarKey) :
    ¬ ∃ term, ClosedTerm context (exactTail label scalarKey emptyKey) term := by
  rintro ⟨term,closed,_,_⟩
  have deferred : GeneralNominalInspection.translate context.state.constructors context.interpretation
      (normalize (exactTail label scalarKey emptyKey)) = .deferred (exactTail label scalarKey emptyKey) := by
    simp only [exactTail,normalize,normalizeArgs,hide,GeneralNominalInspection.translate,primitive]
  exact quote_not_deferred term _ (closed.symm.trans deferred)

theorem total_of_covered
    (source : PatternCovered catalogue interpretation (exactTail label scalarKey emptyKey)) :
    ∃ expression, GeneralNominalCenteredHeadMatExpressions.translate catalogue interpretation
      (exactTail label scalarKey emptyKey) = some expression :=
  GeneralNominalCenteredHeadMatExpressions.translate_complete source

end Yulang.GeneralNominalCenteredHeadMatLabelDomain
