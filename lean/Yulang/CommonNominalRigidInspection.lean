import Yulang.CommonNominalRigidHeadInspection
import Yulang.CommonNominalCarrierConstraints

/-!
# Actual finite inspection of nominal/float/structural rigid constructors

Inspection receives only constructor syntax and original shared child/row IDs.
It emits existing first-order presence atoms, including both invariant
directions at every nominal argument. A mismatch rejects statically. The
independent meaning uses arbitrary new regular child types and arbitrary rows.
No whole-constructor compatibility oracle or semantic guard is emitted.
-/

namespace Yulang.CommonNominalRigidInspection

open CommonNominalCarrier
open Core.PresenceGeneration (Comp TyTerm RowTerm)
open PresenceNormalForm (Atom All)

inductive Node (Rows Child : Type) where
  | bottom | top | float
  | base : Inference.Base → Node Rows Child
  | pair : Child → Child → Node Rows Child
  | variant : Nat → Child → Node Rows Child
  | arrow : Child → Rows → Child → Rows → Node Rows Child
  | nominal : Nat → List (Child ⊕ Rows) → Node Rows Child

def Node.eval (rows : Rows → Row) (children : Child → Ty) : Node Rows Child → Ty
  | .bottom => .bottom
  | .top => .top
  | .float => .float
  | .base scalar => .base scalar
  | .pair first last => CommonNominalCarrier.pair (children first) (children last)
  | .variant label payload => CommonNominalCarrier.variant label (children payload)
  | .arrow input incoming output outgoing => CommonNominalCarrier.arrow (children input) (rows incoming) (children output) (rows outgoing)
  | .nominal name arguments => CommonNominalCarrier.nominal name (arguments.map (Sum.map children rows))

def assignment (rows : Rows → Row) (children : Child → Ty) : Child ⊕ Rows → Comp model
  | .inl child => (children child, Common.rowEmpty)
  | .inr row => (.bottom, rows row)

def argumentTerm : Child ⊕ Rows → CommonNominalCarrierConstraints.ArgumentTerm (Child ⊕ Rows)
  | .inl child => .value (.var (.inl child))
  | .inr row => .row (.var (.inr row))

def headTerm (name : Nat) (arguments : List (Child ⊕ Rows)) : CommonNominalCarrierConstraints.HeadTerm (Child ⊕ Rows) :=
  ⟨name, arguments.map argumentTerm⟩

theorem head_term_eval (rows : Rows → Row) (children : Child → Ty) (name : Nat) (arguments : List (Child ⊕ Rows)) :
    (headTerm name arguments).eval (assignment rows children) = nominal name (arguments.map (Sum.map children rows)) := by
  simp only [CommonNominalCarrierConstraints.HeadTerm.eval, headTerm, List.map_map]
  congr 1
  apply List.map_congr_left
  intro argument _
  cases argument <;> rfl

def typeAtom (first last : Child) : Atom (Child ⊕ Rows) := .tyLe (.var (.inl first)) (.var (.inl last))
def rowAtom (first last : Rows) : Atom (Child ⊕ Rows) := .rowLe (.var (.inr first)) (.var (.inr last))

def inspect : Node Rows Child → Node Rows Child → Option (List (Atom (Child ⊕ Rows)))
  | .bottom, _ => some []
  | _, .top => some []
  | .float, .float => some []
  | .base first, .base last => if first = last then some [] else none
  | .pair first last, .pair first' last' => some [typeAtom first first', typeAtom last last']
  | .variant first payload, .variant last payload' => if first = last then some [typeAtom payload payload'] else none
  | .arrow input incoming output outgoing, .arrow input' incoming' output' outgoing' =>
      some [typeAtom input' input, rowAtom incoming' incoming, typeAtom output output', rowAtom outgoing outgoing']
  | .nominal first arguments, .nominal last arguments' =>
      CommonNominalCarrierConstraints.compile (headTerm first arguments) (headTerm last arguments')
  | _, _ => none

def Satisfied (rows : Rows → Row) (children : Child → Ty) (result : Option (List (Atom (Child ⊕ Rows)))) : Prop :=
  ∃ atoms, result = some atoms ∧ All model (assignment rows children) atoms

@[simp] theorem satisfied_none (rows : Rows → Row) (children : Child → Ty) :
    ¬ Satisfied rows children none := by simp [Satisfied]

@[simp] theorem satisfied_some (rows : Rows → Row) (children : Child → Ty) (atoms : List (Atom (Child ⊕ Rows))) :
    Satisfied rows children (some atoms) ↔ All model (assignment rows children) atoms := by simp [Satisfied]

/-- All new regular child types, including nominal/float/default/mask/arrow
children, and all signed occurrence-set rows. Only finite syntax is inspected. -/
theorem inspect_exact (rows : Rows → Row) (children : Child → Ty) (source target : Node Rows Child) :
    Satisfied rows children (inspect source target) ↔ Subtype (source.eval rows children) (target.eval rows children) := by
  cases source <;> cases target
  case nominal.nominal first arguments last arguments' =>
    change CommonNominalCarrierConstraints.Satisfied (assignment rows children)
      (CommonNominalCarrierConstraints.compile (headTerm first arguments) (headTerm last arguments')) ↔ _
    have compiled := CommonNominalCarrierConstraints.compile_nominal_comparison_exact
      (headTerm first arguments) (headTerm last arguments') (assignment rows children)
    simpa only [CommonNominalCarrierConstraints.Satisfied, head_term_eval, Node.eval] using compiled
  all_goals simp only [inspect, Node.eval, satisfied_some, PresenceNormalForm.all_nil]
  all_goals try exact (iff_true_intro (CommonNominalTypeFlow.bottom_below _)).symm
  all_goals try exact (iff_true_intro (CommonNominalTypeBounds.type_below_top _)).symm
  case float.float =>
    simp only [true_iff]
    exact subtype_refl _
  case base.base first last =>
    rw [CommonNominalRigidHeadInspection.base_iff]
    by_cases same : first = last <;> simp [same]
  case pair.pair =>
    simpa [Satisfied, All, Atom.Holds, typeAtom, assignment, TyTerm.eval, model] using
      (common_pair_iff _ _ _ _).symm
  case variant.variant first payload last payload' =>
    rw [CommonNominalRigidHeadInspection.variant_iff]
    by_cases same : first = last <;> simp [same, Satisfied, All, Atom.Holds, typeAtom, assignment, TyTerm.eval, model]
  case arrow.arrow =>
    simpa [Satisfied, All, Atom.Holds, typeAtom, rowAtom, assignment, TyTerm.eval, RowTerm.eval, model] using
      (common_arrow_iff _ _ _ _ _ _ _ _).symm
  all_goals
    simp only [satisfied_none]
    exact (iff_false_intro (CommonNominalRigidHeadInspection.rigid_mismatch rfl rfl
      (by simp [CommonNominalRigidHeadInspection.head, pair, arrow, variant, nominal])
      (by simp [CommonNominalRigidHeadInspection.head, pair, arrow, variant, nominal])
      (by simp [CommonNominalRigidHeadInspection.head, pair, arrow, variant, nominal]))).symm

def unionLeft (first last target : Child) : List (Atom (Child ⊕ Rows)) :=
  [typeAtom first target, typeAtom last target]

theorem union_left_exact (rows : Rows → Row) (children : Child → Ty) (first last target : Child) :
    All model (assignment rows children) (unionLeft first last target) ↔
      Subtype (.union (children first) (children last)) (children target) := by
  simpa [All, Atom.Holds, typeAtom, assignment, TyTerm.eval, unionLeft, model] using
    (common_union_is_join (children first) (children last) (children target)).symm

def interRight (source first last : Child) : List (Atom (Child ⊕ Rows)) :=
  [typeAtom source first, typeAtom source last]

theorem inter_right_exact (rows : Rows → Row) (children : Child → Ty) (source first last : Child) :
    All model (assignment rows children) (interRight source first last) ↔
      Subtype (children source) (.inter (children first) (children last)) := by
  simpa [All, Atom.Holds, typeAtom, assignment, TyTerm.eval, interRight, model] using
    (common_inter_is_meet (children first) (children last) (children source)).symm

end Yulang.CommonNominalRigidInspection
