import Yulang.GeneralDeclarativeWitnessCovariant352

namespace Yulang.GeneralDeclarativeWitnessCovariantBoundary352
open GeneralNominalCenteredHeadMatExpressions
open GeneralDeclarationPatterns (Constructors)
open GeneralNominalInspection (Interpretation)

theorem no_covariant_as_invariant_application (cat : Constructors) (int : Interpretation)
    (name : Nat) (es : List Expr)
    (declaredNotInvariant : int.invariantNominal name = false)
    (notPrimitive : int.primitives name = none) :
    application cat int name es = none := by
  unfold application
  cases h : cat name <;> simp [declaredNotInvariant,notPrimitive]

theorem existing_tagged_source_reader_cannot_encode (cat : Constructors) (int : Interpretation)
    (tag name payload : Nat)
    (declaredNotInvariant : int.invariantNominal name = false)
    (notPrimitive : int.primitives name = none) :
    translate cat int (.variant tag (.app name [.var payload])) = none := by
  simp [translate,translateMany,no_covariant_as_invariant_application cat int name
    [.variable payload] declaredNotInvariant notPrimitive]

end Yulang.GeneralDeclarativeWitnessCovariantBoundary352
