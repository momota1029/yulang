import Yulang.CommonEffectKindedGeneration
import Yulang.CommonEffectOutputWeakening

/-!
Elimination of a checked, rigid rank-2 field. The field expression and captured
environment are kept fixed while each use chooses fresh value and row locals.
This is pure field introduction: strict construction effects, nominal struct
subtyping, generalization and source declaration lowering remain separate.
-/
namespace Yulang.CommonEffectFieldInstances
open Core.PresenceGeneration (Comp CompTerm TyTerm RowTerm)
open CommonEffectRequestGeneration (Computation Declarations)
open CommonEffectKindedFormula
open CommonEffectKindedGeneration
open CommonEffectRecursiveSource
open CommonEffectRecursiveGeneration (ContextRel)

variable {scopes : Nat}

/-- Every independently chosen use of a checked rigid field is sound for the
same source body and the same captured environment. No local assignment is
selected at construction time or shared between different uses. -/
theorem construct_use_sound (signatures : List SemanticSignature) (declarations : Declarations α)
    (environment : CommonEffectFormula.SchemeEnv scopes α) (bindings : List (Binding scopes))
    (assignment : α → Computation) (related : ContextRel signatures declarations assignment environment bindings)
    (field : FieldScheme α) (body : Expr scopes) (out : CompTerm α)
    (constructed : (constructCheckedField declarations environment field body).Holds assignment)
    (used : (useCheckedField (scopes := scopes) field out).Holds assignment) :
    Typing signatures bindings body (out.eval Common.model assignment) := by
  have rigid := (construct_checked_field_exact signatures declarations environment bindings assignment related field body).mp constructed
  have instantiated := (use_checked_field_exact assignment field out).mp used
  cases instantiated.2 with
  | intro locals below =>
    exact CommonEffectOutputWeakening.typing_weaken (rigid.2 locals) _ below

end Yulang.CommonEffectFieldInstances
