import Yulang.CommonEffectKindedHandler

/-!
Finite operation tables whose local binders retain both value and row kinds.
The declarations are the already checked kinded syntax, not semantic function
inputs. Interpretation preserves all captured slots under every recursive
computation and mixed-local binder. Family keys here are already resolved;
family argument reconciliation and source visibility lowering remain separate.
-/
namespace Yulang.CommonEffectMixedDeclarations
open Core.PresenceGeneration
open CommonEffectRequestGeneration (Computation)
open CommonEffectKindedFormula (Names Locals localEnv localEnv_comp_inl localEnv_names
  rowWellKinded typeWellKinded)

abbrev Declaration := CommonEffectKindedHandler.Declaration
abbrev Declarations (α : Type) := List (Declaration α)

structure SemanticSignature where
  types : Nat
  rows : Nat
  input : Locals types rows → Common.Ty
  output : Locals types rows → Common.Ty
  key : Nat
  extra : List Nat

def rename (names : α → β) (declaration : Declaration α) : Declaration β where
  types := declaration.types
  rows := declaration.rows
  key := declaration.key
  extra := declaration.extra
  input := declaration.input.rename (Sum.map names id)
  output := declaration.output.rename (Sum.map names id)

def interpret (assignment : α → Computation) (declaration : Declaration α) : SemanticSignature where
  types := declaration.types
  rows := declaration.rows
  input := fun locals => declaration.input.eval Common.model (localEnv assignment locals)
  output := fun locals => declaration.output.eval Common.model (localEnv assignment locals)
  key := declaration.key
  extra := declaration.extra

/-- Captured types and rows stay fixed through a mixed local binder; each
operation's two local namespaces and its declared keys remain unchanged. -/
theorem interpret_rename (names : α → β) (assignment : β → Computation)
    (declaration : Declaration α) :
    interpret assignment (rename names declaration) = interpret (assignment ∘ names) declaration := by
  cases declaration with
  | mk types rows key extra input output =>
    simp [interpret, rename, TyTerm.eval_rename, localEnv_names]

def renameAll (names : α → β) (declarations : Declarations α) : Declarations β :=
  declarations.map (rename names)

def interpretAll (assignment : α → Computation) (declarations : Declarations α) :
    List SemanticSignature := declarations.map (interpret assignment)

theorem interpretAll_rename (names : α → β) (assignment : β → Computation)
    (declarations : Declarations α) :
    interpretAll assignment (renameAll names declarations) = interpretAll (assignment ∘ names) declarations := by
  simp [interpretAll, renameAll, List.map_map, interpret_rename, Function.comp_def]

theorem lookup_interpretAll (assignment : α → Computation) (declarations : Declarations α)
    (index : Nat) :
    (interpretAll assignment declarations)[index]? = (declarations[index]?).map (interpret assignment) := by
  simp [interpretAll]

theorem interpretAll_extend (assignment : α → Computation) (declarations : Declarations α)
    (value : Computation) :
    interpretAll (extend assignment value) (renameAll some declarations) = interpretAll assignment declarations := by
  rw [interpretAll_rename, extend_comp_some]

theorem interpretAll_local (assignment : α → Computation) (declarations : Declarations α)
    (locals : Locals types rows) :
    interpretAll (localEnv assignment locals) (renameAll Sum.inl declarations) =
      interpretAll assignment declarations := by
  rw [interpretAll_rename, localEnv_comp_inl]

end Yulang.CommonEffectMixedDeclarations
