import Yulang.CommonNominalTemplateEquations

/-!
# Disjoint template-node allocation with the same shared arguments

All original internal nodes of both operands receive disjoint IDs, while the
entire type/row argument vectors remain shared. The independent models are
exactly the product of both original full template models. Both original
roots remain available, including parameter roots.
-/

namespace Yulang.CommonNominalTemplateAllocation

open CommonNominalCarrier
open CommonNominalFieldTemplates (Body Template)
open CommonNominalTemplateEquations (chosen evaluate Models)

def rename (injection : Fin before → Fin after) : Body before types rows → Body after types rows
  | .parameter index => .parameter index
  | .base scalar => .base scalar
  | .float => .float
  | .bottom => .bottom
  | .top => .top
  | .union first last => .union (rename injection first) (rename injection last)
  | .inter first last => .inter (rename injection first) (rename injection last)
  | .pair first last => .pair (Sum.map injection id first) (Sum.map injection id last)
  | .emptyRecord => .emptyRecord
  | .exactEmpty => .exactEmpty
  | .record label payload tail => .record label (Sum.map injection id payload) (rename injection tail)
  | .recordDefault label source fallback => .recordDefault label (rename injection source) (Sum.map injection id fallback)
  | .variant label payload => .variant label (Sum.map injection id payload)
  | .arrow input incoming output outgoing => .arrow (Sum.map injection id input) incoming (Sum.map injection id output) outgoing
  | .mask hidden source => .mask hidden (rename injection source)
  | .nominal name args => .nominal name (args.map (Sum.map (Sum.map injection id) id))

@[simp] theorem chosen_rename (injection : Fin before → Fin after) (values : Fin after → Ty)
    (arguments : Fin types → Ty) (reference : Fin before ⊕ Fin types) :
    chosen values arguments (Sum.map injection id reference) = chosen (values ∘ injection) arguments reference := by
  cases reference <;> rfl

theorem evaluate_rename (injection : Fin before → Fin after) (values : Fin after → Ty)
    (arguments : Fin types → Ty) (rowValues : Fin rows → Row) (body : Body before types rows) :
    evaluate arguments rowValues values (rename injection body) = evaluate arguments rowValues (values ∘ injection) body := by
  induction body with
  | nominal name args =>
      simp only [rename, evaluate, nominal, List.map_map]
      congr 1
      apply List.map_congr_left
      intro argument _
      cases argument <;> simp [chosen_rename]
  | _ => simp_all [rename, evaluate]

def merge (first last : Template types rows) : Template types rows where
  nodes := first.nodes + last.nodes
  body := Fin.addCases
    (fun index => rename (Fin.castAdd last.nodes) (first.body index))
    (fun index => rename (Fin.natAdd first.nodes) (last.body index))
  root := Sum.map (Fin.castAdd last.nodes) id first.root

def rightRoot (first last : Template types rows) : Fin (first.nodes + last.nodes) ⊕ Fin types :=
  Sum.map (Fin.natAdd first.nodes) id last.root

def mergedValues (first : Fin before → Ty) (last : Fin after → Ty) : Fin (before + after) → Ty := Fin.addCases first last

@[simp] theorem merged_left (first : Fin before → Ty) (last : Fin after → Ty) :
    mergedValues first last ∘ Fin.castAdd after = first := by funext index; simp [mergedValues]

@[simp] theorem merged_right (first : Fin before → Ty) (last : Fin after → Ty) :
    mergedValues first last ∘ Fin.natAdd before = last := by funext index; simp [mergedValues]

/-- No copied or fresh shared argument parameters are introduced. Every
original internal model is retained on both sides, including recursive ones. -/
theorem models_merge (first last : Template types rows) (arguments : Fin types → Ty) (rowValues : Fin rows → Row)
    (firstValues : Fin first.nodes → Ty) (lastValues : Fin last.nodes → Ty) :
    Models (merge first last) arguments rowValues (mergedValues firstValues lastValues) ↔
      Models first arguments rowValues firstValues ∧ Models last arguments rowValues lastValues := by
  constructor
  · intro model
    constructor
    · intro index
      have original := model (Fin.castAdd last.nodes index)
      simpa [merge, evaluate_rename, mergedValues] using original
    · intro index
      have original := model (Fin.natAdd first.nodes index)
      simpa [merge, evaluate_rename, mergedValues] using original
  · rintro ⟨firstModel, lastModel⟩ index
    refine Fin.addCases ?_ ?_ index
    · intro index
      simpa [merge, evaluate_rename, mergedValues] using firstModel index
    · intro index
      simpa [merge, evaluate_rename, mergedValues] using lastModel index

theorem chosen_left_root (first last : Template types rows) (arguments : Fin types → Ty)
    (firstValues : Fin first.nodes → Ty) (lastValues : Fin last.nodes → Ty) :
    chosen (mergedValues firstValues lastValues) arguments (merge first last).root =
      chosen firstValues arguments first.root := by
  simp only [merge, chosen_rename, merged_left]

theorem chosen_right_root (first last : Template types rows) (arguments : Fin types → Ty)
    (firstValues : Fin first.nodes → Ty) (lastValues : Fin last.nodes → Ty) :
    chosen (mergedValues firstValues lastValues) arguments (rightRoot first last) =
      chosen lastValues arguments last.root := by
  simp only [rightRoot, chosen_rename, merged_right]

theorem model_roots_recovered (first last : Template types rows) (arguments : Fin types → Ty) (rowValues : Fin rows → Row)
    (firstValues : Fin first.nodes → Ty) (lastValues : Fin last.nodes → Ty)
    (model : Models (merge first last) arguments rowValues (mergedValues firstValues lastValues)) :
    Equivalent (first.eval arguments rowValues)
        (chosen (mergedValues firstValues lastValues) arguments (merge first last).root) ∧
      Equivalent (last.eval arguments rowValues)
        (chosen (mergedValues firstValues lastValues) arguments (rightRoot first last)) := by
  have parts := (models_merge first last arguments rowValues firstValues lastValues).mp model
  rw [chosen_left_root, chosen_right_root]
  exact ⟨CommonNominalTemplateEquations.model_root_recovery first arguments rowValues firstValues parts.1,
    CommonNominalTemplateEquations.model_root_recovery last arguments rowValues lastValues parts.2⟩

end Yulang.CommonNominalTemplateAllocation
