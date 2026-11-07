import Yulang.CommonEffectPresence
import Yulang.CoreEffectTyping

/-! Finite declarations retain their captured slots under computation/local
binders. Semantic signature functions below are interpretations of finite
syntax, never input contracts or generated formula atoms. -/
namespace Yulang.CommonEffectDeclarationInterpretation
open Core.PresenceGeneration
open CommonEffectRequestGeneration (Declaration Declarations Computation localEnv)

/-- Captured names change; operation-local value variables keep their identity. -/
def rename (names : α → β) (declaration : Declaration α) : Declaration β where
  locals := declaration.locals
  key := declaration.key
  extra := declaration.extra
  input := declaration.input.rename (Sum.map names id)
  output := declaration.output.rename (Sum.map names id)

/-- No arbitrary semantic signature is an input of the finite generator. -/
def interpret (assignment : α → Computation) (declaration : Declaration α) :
    Core.EffectTyping.OperationSignature Common.model.toModel Nat where
  locals := declaration.locals
  input := fun locals => declaration.input.eval Common.model (localEnv assignment locals)
  output := fun locals => declaration.output.eval Common.model (localEnv assignment locals)
  key := declaration.key
  extra := declaration.extra

theorem localEnv_names (names : α → β) (assignment : β → Computation)
    (locals : Fin count → Common.Ty) :
    localEnv assignment locals ∘ Sum.map names id = localEnv (assignment ∘ names) locals := by
  funext name
  cases name <;> rfl

/-- Entire signatures, including all possible local value assignments, agree. -/
theorem interpret_rename (names : α → β) (assignment : β → Computation) (declaration : Declaration α) :
    interpret assignment (rename names declaration) = interpret (assignment ∘ names) declaration := by
  cases declaration with
  | mk count key extra input output =>
    simp [interpret, rename, TyTerm.eval_rename]
    constructor
    · funext locals
      exact congrArg (fun env => input.eval Common.model env) (localEnv_names names assignment locals)
    · funext locals
      exact congrArg (fun env => output.eval Common.model env) (localEnv_names names assignment locals)

def renameAll (names : α → β) (declarations : Declarations α) : Declarations β :=
  declarations.map (rename names)

def interpretAll (assignment : α → Computation) (declarations : Declarations α) :
    List (Core.EffectTyping.OperationSignature Common.model.toModel Nat) :=
  declarations.map (interpret assignment)

theorem interpretAll_rename (names : α → β) (assignment : β → Computation) (declarations : Declarations α) :
    interpretAll assignment (renameAll names declarations) = interpretAll (assignment ∘ names) declarations := by
  simp [interpretAll, renameAll, List.map_map, interpret_rename, Function.comp_def]

/-- Real finite table lookup commutes with interpretation, including absence. -/
theorem lookup_interpretAll (assignment : α → Computation) (declarations : Declarations α) (index : Nat) :
    (interpretAll assignment declarations)[index]? = (declarations[index]?).map (interpret assignment) := by
  simp [interpretAll]

/-- Adding a computation witness never freshens an operation's captured rows. -/
theorem interpretAll_extend (assignment : α → Computation) (declarations : Declarations α) (value : Computation) :
    interpretAll (extend assignment value) (renameAll some declarations) = interpretAll assignment declarations := by
  rw [interpretAll_rename, extend_comp_some]

/-- Nested operation-local binders are disjoint from all captured slots. -/
theorem interpretAll_local (assignment : α → Computation) (declarations : Declarations α)
    (locals : Fin count → Common.Ty) :
    interpretAll (localEnv assignment locals) (renameAll Sum.inl declarations) = interpretAll assignment declarations := by
  rw [interpretAll_rename, CommonEffectRequestGeneration.localEnv_comp_inl]

theorem rowWellKinded_names (names : α → β) (row : RowTerm (α ⊕ Fin count)) :
    CommonEffectRequestGeneration.rowWellKinded (row.rename (Sum.map names id)) =
      CommonEffectRequestGeneration.rowWellKinded row := by
  induction row with
  | var name => cases name <;> rfl
  | empty => rfl
  | join first last firstIH lastIH =>
    simp [RowTerm.rename, CommonEffectRequestGeneration.rowWellKinded, firstIH, lastIH]

theorem typeWellKinded_names (names : α → β) (value : TyTerm (α ⊕ Fin count)) :
    CommonEffectRequestGeneration.typeWellKinded (value.rename (Sum.map names id)) =
      CommonEffectRequestGeneration.typeWellKinded value := by
  induction value <;> simp_all [TyTerm.rename, CommonEffectRequestGeneration.typeWellKinded, rowWellKinded_names]

theorem wellKinded_rename (names : α → β) (declaration : Declaration α) :
    (rename names declaration).wellKinded = declaration.wellKinded := by
  simp [Declaration.wellKinded, rename, typeWellKinded_names]

theorem wellKinded_renameAll (names : α → β) (declarations : Declarations α) :
    (renameAll names declarations).wellKinded = declarations.wellKinded := by
  simp [Declarations.wellKinded, renameAll, List.all_map, Function.comp_def, wellKinded_rename]
end Yulang.CommonEffectDeclarationInterpretation
