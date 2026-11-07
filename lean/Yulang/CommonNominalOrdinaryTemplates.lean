import Yulang.CommonNominalTemplateEquations
import Yulang.PresenceOpenTailGenerationLowering

/-!
# Actual presence-generation terms as full shared field templates

The existing finite collector allocates every original ordinary subterm and
every original ambient variable. Original rows and all payload references
are retained. Same-depth source syntax is expanded structurally, while every
guarded child references its original shared collector ID.

The independent original TyTerm interpretation is preserved for arbitrary
new regular ambient values, including nominal/float and negative children.
-/

namespace Yulang.CommonNominalOrdinaryTemplates

open CommonNominalCarrier
open Core.PresenceGeneration (Comp TyTerm RowTerm)
open PresenceOpenTailGenerationLowering (Pool subterms)
open CommonNominalFieldTemplates (Body Template TemplateRow)

def row : RowTerm (Fin inputs) → TemplateRow inputs
  | .var original => .var original
  | .empty => .empty
  | .join first last => .join (row first) (row last)

theorem row_eval (assignment : Fin inputs → Comp model) (original : RowTerm (Fin inputs)) :
    (row original).eval (fun index => (assignment index).2) = original.eval model assignment := by
  induction original <;> simp_all [row, TemplateRow.eval, RowTerm.eval, model]

def body (pool : Pool inputs) : (original : TyTerm (Fin inputs)) → original ∈ pool.terms → Body pool.size inputs inputs
  | .var original, _ => .parameter original
  | .base scalar, _ => .base scalar
  | .bottom, _ => .bottom
  | .top, _ => .top
  | .union first last, member =>
      .union (body pool first (pool.closed _ member first (by simp [subterms])))
        (body pool last (pool.closed _ member last (by simp [subterms])))
  | .inter first last, member =>
      .inter (body pool first (pool.closed _ member first (by simp [subterms])))
        (body pool last (pool.closed _ member last (by simp [subterms])))
  | .pair first last, member => .pair (.inl (pool.child _ member first (by simp [subterms])))
      (.inl (pool.child _ member last (by simp [subterms])))
  | .emptyRecord, _ => .emptyRecord
  | .exactEmpty, _ => .exactEmpty
  | .required label payload, member => .record label (.inl (pool.child _ member payload (by simp [subterms]))) .emptyRecord
  | .record label payload tail, member => .record label (.inl (pool.child _ member payload (by simp [subterms])))
      (body pool tail (pool.closed _ member tail (by simp [subterms])))
  | .recordDefault label source fallback, member => .recordDefault label
      (body pool source (pool.closed _ member source (by simp [subterms])))
      (.inl (pool.child _ member fallback (by simp [subterms])))
  | .variant label payload, member => .variant label (.inl (pool.child _ member payload (by simp [subterms])))
  | .arrow input incoming output outgoing, member => .arrow (.inl (pool.child _ member input (by simp [subterms])))
      (row incoming) (.inl (pool.child _ member output (by simp [subterms]))) (row outgoing)

def template (pool : Pool inputs) (original : TyTerm (Fin inputs)) (member : original ∈ pool.terms) : Template inputs inputs :=
  ⟨pool.size, fun index => body pool (pool.termAt index) (pool.at_mem index), .inl (pool.reference original member)⟩

def canonical (pool : Pool inputs) (assignment : Fin inputs → Comp model) : Fin pool.size → Ty :=
  fun index => (pool.termAt index).eval model assignment

@[simp] theorem canonical_reference (pool : Pool inputs) (assignment : Fin inputs → Comp model)
    (original : TyTerm (Fin inputs)) (member : original ∈ pool.terms) :
    canonical pool assignment (pool.reference original member) = original.eval model assignment := by
  simp only [canonical, Pool.termAt_reference]
  rfl

theorem body_evaluate (pool : Pool inputs) (assignment : Fin inputs → Comp model)
    (original : TyTerm (Fin inputs)) (member : original ∈ pool.terms) :
    CommonNominalTemplateEquations.evaluate (fun index => (assignment index).1) (fun index => (assignment index).2)
      (canonical pool assignment) (body pool original member) = original.eval model assignment := by
  induction original with
  | union first last ihFirst ihLast | inter first last ihFirst ihLast =>
      simp only [body, CommonNominalTemplateEquations.evaluate, TyTerm.eval, model, ihFirst, ihLast]
  | record label payload tail ihPayload ihTail | recordDefault label tail payload ihTail ihPayload =>
      simp only [body, CommonNominalTemplateEquations.evaluate, CommonNominalTemplateEquations.chosen,
        Sum.elim_inl, Pool.child, canonical_reference, TyTerm.eval, model, ihTail]
  | arrow input incoming output outgoing =>
      simp only [body, CommonNominalTemplateEquations.evaluate, CommonNominalTemplateEquations.chosen,
        Sum.elim_inl, Pool.child, canonical_reference, TyTerm.eval, model, row_eval]
  | _ =>
      simp only [body, CommonNominalTemplateEquations.evaluate, CommonNominalTemplateEquations.chosen,
        Sum.elim_inl, Pool.child, canonical_reference, TyTerm.eval, model,
        CommonNominalCarrier.required]

theorem canonical_models (pool : Pool inputs) (assignment : Fin inputs → Comp model)
    (original : TyTerm (Fin inputs)) (member : original ∈ pool.terms) :
    CommonNominalTemplateEquations.Models (template pool original member)
      (fun index => (assignment index).1) (fun index => (assignment index).2) (canonical pool assignment) := by
  intro index
  change Equivalent (CommonNominalTemplateEquations.evaluate _ _ _ (body pool _ _)) _
  rw [body_evaluate]
  exact equivalent_refl _

theorem template_eval (pool : Pool inputs) (assignment : Fin inputs → Comp model)
    (original : TyTerm (Fin inputs)) (member : original ∈ pool.terms) :
    Equivalent ((template pool original member).eval (fun index => (assignment index).1) (fun index => (assignment index).2))
      (original.eval model assignment) := by
  have recovered := CommonNominalTemplateEquations.model_root_recovery (template pool original member)
    (fun index => (assignment index).1) (fun index => (assignment index).2) (canonical pool assignment)
    (canonical_models pool assignment original member)
  change Equivalent ((template pool original member).eval (fun index => (assignment index).1)
    (fun index => (assignment index).2)) (canonical pool assignment (pool.reference original member)) at recovered
  simpa only [canonical_reference] using recovered

/-- Every original shared ordinary subterm and ambient variable is retained,
not only the requested root. -/
theorem all_nodes_exact (pool : Pool inputs) (assignment : Fin inputs → Comp model)
    (original : TyTerm (Fin inputs)) (member : original ∈ pool.terms) (values : Fin pool.size → Ty) :
    CommonNominalTemplateEquations.Models (template pool original member)
      (fun index => (assignment index).1) (fun index => (assignment index).2) values ↔
      ∀ index, Equivalent (values index) ((pool.termAt index).eval model assignment) := by
  have canonicalSame := (CommonNominalTemplateEquations.models_exact _ _ _ _).mp
    (canonical_models pool assignment original member)
  constructor
  · intro actual index
    have recovered := (CommonNominalTemplateEquations.models_exact (template pool original member)
      (fun index => (assignment index).1) (fun index => (assignment index).2) values).mp actual
    exact equivalent_trans (equivalent_symm (recovered index)) (canonicalSame index)
  · intro recovered
    apply (CommonNominalTemplateEquations.models_exact (template pool original member)
      (fun index => (assignment index).1) (fun index => (assignment index).2) values).mpr
    intro index
    exact equivalent_trans (canonicalSame index) (equivalent_symm (recovered index))

end Yulang.CommonNominalOrdinaryTemplates
