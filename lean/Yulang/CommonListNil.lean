import Yulang.CommonNominalSlotSolver
import Yulang.CoreExpr

/-!
# Invariant nominal list types and the nil leaf's complete parameter family

The declaration supplies the resolved nominal list ID; its single element
parameter is a value parameter. Nil has no sites and needs no cast. Its element
ranges over the full new regular carrier, including nested nominals and rows
inside arbitrary constructors. The finite constraints and independent source
rule are separate definitions.

This is the nil/empty-data leaf. Cons, nonempty data, deferred casts and module
weak-parameter finalization remain separate B1 obligations.
-/

namespace Yulang.CommonListNil

open CommonNominalCarrier
open Core.PresenceGeneration (Comp CompTerm TyTerm RowTerm extend)

structure Declaration where
  name : Nat

def listType (declaration : Declaration) (element : Ty) : Ty :=
  nominal declaration.name [.inl element]

/-- Arbitrary list identities and arbitrary regular element types. -/
theorem list_invariant_exact (first last : Declaration) (a b : Ty) :
    CommonNominalCarrier.Subtype (listType first a) (listType last b) ↔
      first.name = last.name ∧ Equivalent a b := by
  rw [listType, listType, nominal_regular_invariant_exact]
  simp only [List.length_cons, List.length_nil]
  constructor
  · rintro ⟨name, _, same⟩
    exact ⟨name, same 0 (.inl a) (.inl b) rfl rfl⟩
  · rintro ⟨name, same⟩
    refine ⟨name, trivial, ?_⟩
    intro index left right first last
    cases index with
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at first last
        subst left; subst right
        exact same
    | succ index => simp at first

inductive Typing (declaration : Declaration) (signature : Core.Signature)
    (Context : Type) : Context → Core.Expr signature → Comp model → Prop where
  | nil : Core.PresenceGeneration.Comp.le model
      (Core.PresenceGeneration.Comp.pure model (listType declaration element)) result →
      Typing declaration signature Context environment .nil result
  | emptyData : Core.PresenceGeneration.Comp.le model
      (Core.PresenceGeneration.Comp.pure model (listType declaration element)) result →
      Typing declaration signature Context environment (.data (.list [])) result

inductive TypeTerm (α : Type) where
  | ordinary : TyTerm α → TypeTerm α
  | list : Nat → TyTerm α → TypeTerm α

def TypeTerm.eval (assignment : α → Comp model) : TypeTerm α → Ty
  | .ordinary type => type.eval model assignment
  | .list name element => nominal name [.inl (element.eval model assignment)]

inductive Formula : Type → Type 1 where
  | tyLe : TypeTerm α → TypeTerm α → Formula α
  | rowLe : RowTerm α → RowTerm α → Formula α
  | and : Formula α → Formula α → Formula α
  | existsSlot : Formula (Option α) → Formula α

def Formula.Models : {α : Type} → (α → Comp model) → Formula α → Prop
  | _, assignment, .tyLe first last => CommonNominalCarrier.Subtype (first.eval assignment) (last.eval assignment)
  | _, assignment, .rowLe first last => Common.rowLe (first.eval model assignment) (last.eval model assignment)
  | _, assignment, .and first last => first.Models assignment ∧ last.Models assignment
  | _, assignment, .existsSlot body => ∃ fresh, body.Models (extend assignment fresh)

def generate (declaration : Declaration) (output : CompTerm α) : Formula α :=
  .existsSlot (.and
    (.tyLe (.list declaration.name (.var none)) (.ordinary (output.ty.rename some)))
    (.rowLe .empty (output.row.rename some)))

/-- A finite generated formula over real type/row atoms, with the original
ambient assignment kept fixed and one fresh element slot. -/
theorem generate_nil_exact (declaration : Declaration) (signature : Core.Signature)
    (Context : Type) (environment : Context) (output : CompTerm α) (assignment : α → Comp model) :
    (generate declaration output).Models assignment ↔
      Typing declaration signature Context environment .nil (output.eval model assignment) := by
  have outputType (fresh : Comp model) :
      (output.ty.rename some).eval model (extend assignment fresh) = output.ty.eval model assignment := by
    simp only [TyTerm.eval_rename, Core.PresenceGeneration.extend_comp_some]
  have outputRow (fresh : Comp model) :
      (output.row.rename some).eval model (extend assignment fresh) = output.row.eval model assignment := by
    simp only [RowTerm.eval_rename, Core.PresenceGeneration.extend_comp_some]
  simp only [generate, Formula.Models, TypeTerm.eval, TyTerm.eval,
    Core.PresenceGeneration.extend_none, RowTerm.eval, outputType, outputRow]
  constructor
  · rintro ⟨fresh, type, row⟩
    exact .nil ⟨type, row⟩
  · intro typed
    cases typed with
    | nil bounded =>
        rename_i element
        exact ⟨(element, Common.rowEmpty), bounded⟩

/-- Nil and the original empty-list data value have the same independent
judgment, with no signature or environment restriction. -/
theorem empty_data_exact (declaration : Declaration) (signature : Core.Signature)
    (Context : Type) (environment : Context) (result : Comp model) :
    Typing declaration signature Context environment (.data (.list [])) result ↔
      Typing declaration signature Context environment .nil result := by
  constructor
  · intro typed; cases typed with | emptyData bounded => exact .nil bounded
  · intro typed; cases typed with | nil bounded => exact .emptyData bounded

structure Scheme where
  declaration : Declaration

abbrev Scheme.Parameters (_scheme : Scheme) := Ty

def Scheme.instantiate (scheme : Scheme) (element : scheme.Parameters) : Comp model :=
  (listType scheme.declaration element, Common.rowEmpty)

def infer (declaration : Declaration) : List Scheme := [⟨declaration⟩]

theorem nil_all_parameters (declaration : Declaration) (signature : Core.Signature)
    (Context : Type) (environment : Context) (scheme : Scheme)
    (returned : scheme ∈ infer declaration) (parameters : scheme.Parameters) :
    Typing declaration signature Context environment .nil (scheme.instantiate parameters) := by
  have same : scheme = ⟨declaration⟩ := List.mem_singleton.mp returned
  subst scheme
  exact .nil ⟨subtype_refl _, Common.rowLe_refl _⟩

theorem nil_all_models (declaration : Declaration) (signature : Core.Signature)
    (Context : Type) (environment : Context) (result : Comp model) :
    Typing declaration signature Context environment .nil result ↔
      ∃ scheme ∈ infer declaration, ∃ parameters : scheme.Parameters,
        Core.PresenceGeneration.Comp.le model (scheme.instantiate parameters) result := by
  constructor
  · intro typed
    cases typed with
    | nil bounded =>
        rename_i element
        exact ⟨⟨declaration⟩, by simp [infer], element, bounded⟩
  · rintro ⟨scheme, returned, element, bounded⟩
    have same : scheme = ⟨declaration⟩ := List.mem_singleton.mp returned
    subst scheme
    exact .nil bounded

end Yulang.CommonListNil
