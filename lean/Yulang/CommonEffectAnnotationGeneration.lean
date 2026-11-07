import Yulang.CommonEffectAnnotations
import Yulang.CommonEffectNormalHandler

/-! Concrete finite annotation masks feed the real recursive generator;
frozen positive observations feed a computed finite gate. Neither interface
accepts an arbitrary semantic permission function or a Typing atom. Source
location extraction and construction of the completed snapshot remain open. -/
namespace Yulang.CommonEffectAnnotationGeneration
open Core.PresenceGeneration (CompTerm)
open CommonEffectRequestGeneration (Computation Declarations)
open CommonEffectFormula
open CommonEffectAnnotations (Annotation Permits Frozen)
open CommonEffectRecursiveSource (SemanticSignature Binding Expr Typing)
open CommonEffectRecursiveGeneration (ContextRel generate)

variable {scopes : Nat}

def generateAnnotatedHandler (declarations : Declarations α) (schemes : SchemeEnv scopes α)
    (annotation : Annotation) (operation : Nat) (action onReturn onOperation : Expr scopes) (out : CompTerm α) :
    Formula scopes α :=
  CommonEffectNormalHandler.generateHandler declarations schemes annotation.incoming operation action onReturn onOperation out

theorem generate_annotated_handler_exact (signatures : List SemanticSignature) {declarations : Declarations α}
    (schemes : SchemeEnv scopes α) (environment : List (Binding scopes)) (assignment : α → Computation)
    (related : ContextRel signatures declarations assignment schemes environment)
    (annotation : Annotation) (operation : Nat) (action onReturn onOperation : Expr scopes) (out : CompTerm α) :
    (generateAnnotatedHandler declarations schemes annotation operation action onReturn onOperation out).Holds assignment ↔
      Typing signatures environment (.handler annotation.incoming operation action onReturn onOperation) (out.eval Common.model assignment) :=
  CommonEffectNormalHandler.generate_handler_exact signatures schemes environment assignment related
    annotation.incoming operation action onReturn onOperation out

/-- Static permission comes from this incoming annotation, not a global
restriction on effects raised by arbitrary bodies elsewhere. -/
theorem annotated_handler_permission (signatures : List SemanticSignature) (environment : List (Binding scopes))
    (annotation : Annotation) (operation : Nat) (action onReturn onOperation : Expr scopes) (out : Computation)
    (typed : Typing signatures environment (.handler annotation.incoming operation action onReturn onOperation) out) :
    ∃ signature, signatures[operation]? = some signature ∧ Permits annotation signature.key := by
  obtain ⟨signature, found, allowed, _⟩ := (Typing.handler_iff _ _ _ _ _ _ _ _).mp typed
  exact ⟨signature, found, (CommonEffectAnnotations.incoming_exact annotation signature.key).mp allowed⟩

theorem generated_frozen_check_exact (snapshot : Frozen scopes) (signatures : List SemanticSignature)
    {declarations : Declarations α} (schemes : SchemeEnv scopes α) (environment : List (Binding scopes))
    (assignment : α → Computation) (related : ContextRel signatures declarations assignment schemes environment)
    (body : Expr scopes) (out : CompTerm α) :
    (snapshot.emit (generate declarations schemes body out)).Holds assignment ↔
      snapshot.CommonAdmissible ∧ Typing signatures environment body (out.eval Common.model assignment) :=
  (snapshot.emit_exact _ assignment).trans
    (and_congr Iff.rfl (CommonEffectRecursiveExact.generate_recursive_effect_exact signatures body schemes environment assignment out related))
end Yulang.CommonEffectAnnotationGeneration
