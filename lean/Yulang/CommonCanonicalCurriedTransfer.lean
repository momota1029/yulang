import Yulang.CommonCanonicalArrowFamilies

/-!
# Simultaneous transfer for finitely many shared arrow arguments

Each argument is a generalized variable; the same variable may occur at any
number of argument positions and in the scalar result. To satisfy required
arguments, its least admissible assignment is the union of those arguments
which share its ID. Unused generalized result variables receive bottom.

The argument count is fixed for each comparison but otherwise arbitrary,
including zero. Captured values and every arrow's two row IDs remain shared.
The exact-instance theorem below computes the simultaneous transfer for all
argument/output values and rows, without a supplied successful solution.
-/

namespace Yulang.CommonCanonicalCurriedTransfer

open Common (Ty Row Subtype Equivalent)
open ProducerCanonicalOpen (Expr)
open CommonBoundCoalescing (joinTypes joinTypes_le_iff member_le_joinTypes)

variable {fixed rowSlots arguments generalized : Nat}

structure Scheme (fixed rowSlots arguments generalized : Nat) where
  incoming : Fin arguments → Fin rowSlots
  outgoing : Fin arguments → Fin rowSlots
  input : Fin arguments → Fin generalized
  output : Expr (fixed + generalized)

def spine : (count : Nat) → (Fin count → Ty) → (Fin count → Row) → (Fin count → Row) → Ty → Ty
  | 0, _, _, _, output => output
  | count + 1, inputs, incoming, outgoing, output =>
      Common.arrow (inputs 0) (incoming 0)
        (spine count (fun index => inputs index.succ) (fun index => incoming index.succ)
          (fun index => outgoing index.succ) output) (outgoing 0)

theorem spine_below_iff (count : Nat) (inputs inputs' : Fin count → Ty)
    (incoming incoming' outgoing outgoing' : Fin count → Row) (output output' : Ty) :
    Subtype (spine count inputs incoming outgoing output) (spine count inputs' incoming' outgoing' output') ↔
      (∀ index, Subtype (inputs' index) (inputs index) ∧
        Common.rowLe (incoming' index) (incoming index) ∧ Common.rowLe (outgoing index) (outgoing' index)) ∧
      Subtype output output' := by
  induction count with
  | zero => exact ⟨fun below => ⟨fun index => Fin.elim0 index, below⟩, And.right⟩
  | succ count ih =>
      constructor
      · intro below
        obtain ⟨argument, incomingBelow, remaining, outgoingBelow⟩ :=
          (Common.common_arrow_iff _ _ _ _ _ _ _ _).mp below
        obtain ⟨rest, outputBelow⟩ := (ih _ _ _ _ _ _).mp remaining
        refine ⟨?_, outputBelow⟩
        intro index
        exact Fin.cases ⟨argument, incomingBelow, outgoingBelow⟩ rest index
      · rintro ⟨argumentsBelow, outputBelow⟩
        apply (Common.common_arrow_iff _ _ _ _ _ _ _ _).mpr
        exact ⟨(argumentsBelow 0).1, (argumentsBelow 0).2.1,
          (ih _ _ _ _ _ _).mpr ⟨fun index => argumentsBelow index.succ, outputBelow⟩, (argumentsBelow 0).2.2⟩

def occurrences (scheme : Scheme fixed rowSlots arguments generalized) (index : Fin generalized) : List (Fin arguments) :=
  (List.finRange arguments).filter fun position => decide (scheme.input position = index)

@[simp] theorem mem_occurrences (scheme : Scheme fixed rowSlots arguments generalized)
    (index : Fin generalized) (position : Fin arguments) :
    position ∈ occurrences scheme index ↔ scheme.input position = index := by
  simp [occurrences]

def selected (scheme : Scheme fixed rowSlots arguments generalized) (inputs : Fin arguments → Ty) : Fin generalized → Ty :=
  fun index => joinTypes ((occurrences scheme index).map inputs)

theorem input_le_selected (scheme : Scheme fixed rowSlots arguments generalized)
    (inputs : Fin arguments → Ty) (position : Fin arguments) :
    Subtype (inputs position) (selected scheme inputs (scheme.input position)) := by
  apply member_le_joinTypes
  apply List.mem_map.mpr
  exact ⟨position, (mem_occurrences _ _ _).mpr rfl, rfl⟩

theorem selected_le (scheme : Scheme fixed rowSlots arguments generalized)
    (inputs : Fin arguments → Ty) (parameters : Fin generalized → Ty)
    (below : ∀ position, Subtype (inputs position) (parameters (scheme.input position))) (index : Fin generalized) :
    Subtype (selected scheme inputs index) (parameters index) := by
  apply (joinTypes_le_iff _ _).mpr
  intro value member
  obtain ⟨position, present, rfl⟩ := List.mem_map.mp member
  have same := (mem_occurrences scheme index position).mp present
  simpa only [same] using below position

def joinExpressions : List (Expr n) → Expr n
  | [] => .bottom
  | expression :: rest => .union expression (joinExpressions rest)

theorem instantiate_joinExpressions (expressions : List (Expr n)) (parameters : Fin n → Ty) :
    CommonCanonicalOpen.instantiate parameters (joinExpressions expressions) =
      joinTypes (expressions.map (CommonCanonicalOpen.instantiate parameters)) := by
  induction expressions with
  | nil => rfl
  | cons expression rest ih =>
      simp only [joinExpressions, CommonCanonicalOpen.instantiate, List.map_cons, joinTypes, ih]

def replacements (scheme : Scheme fixed rowSlots arguments generalized) : Fin (fixed + generalized) → Expr (fixed + arguments) :=
  Fin.addCases (fun index => .atom (.var (index.castAdd arguments)))
    (fun index => joinExpressions ((occurrences scheme index).map fun position =>
      .atom (.var (Fin.natAdd fixed position))))

def transfer (scheme : Scheme fixed rowSlots arguments generalized) : Expr (fixed + arguments) :=
  CommonCanonicalParameters.substituteExpr (replacements scheme) scheme.output

def applyTransfer (scheme : Scheme fixed rowSlots arguments generalized)
    (captured : Fin fixed → Ty) (inputs : Fin arguments → Ty) : Ty :=
  CommonCanonicalOpen.instantiate (Fin.addCases captured inputs) (transfer scheme)

theorem applyTransfer_eq (scheme : Scheme fixed rowSlots arguments generalized)
    (captured : Fin fixed → Ty) (inputs : Fin arguments → Ty) :
    applyTransfer scheme captured inputs =
      CommonCanonicalOpen.instantiate (Fin.addCases captured (selected scheme inputs)) scheme.output := by
  rw [applyTransfer, transfer, CommonCanonicalParameters.instantiate_substituteExpr]
  congr 1
  funext index
  refine Fin.addCases (fun index => ?_) (fun index => ?_) index
  · simp [replacements, CommonCanonicalOpen.instantiate, CommonCanonicalOpen.atomType]
  · simp [replacements, instantiate_joinExpressions, selected, List.map_map, Function.comp_def,
      CommonCanonicalOpen.instantiate, CommonCanonicalOpen.atomType]

theorem transfer_le_output (scheme : Scheme fixed rowSlots arguments generalized)
    (captured : Fin fixed → Ty) (inputs : Fin arguments → Ty) (parameters : Fin generalized → Ty)
    (below : ∀ position, Subtype (inputs position) (parameters (scheme.input position))) :
    Subtype (applyTransfer scheme captured inputs)
      (CommonCanonicalOpen.instantiate (Fin.addCases captured parameters) scheme.output) := by
  rw [applyTransfer_eq]
  apply CommonCanonicalIntervals.instantiate_mono
  intro index
  refine Fin.addCases (fun index => ?_) (fun index => ?_) index
  · simpa only [Fin.addCases_left] using Common.subtype_refl (captured index)
  · simpa only [Fin.addCases_right] using selected_le scheme inputs parameters below index

def instantiate (scheme : Scheme fixed rowSlots arguments generalized) (rows : Fin rowSlots → Row)
    (captured : Fin fixed → Ty) (parameters : Fin generalized → Ty) : Ty :=
  spine arguments (fun position => parameters (scheme.input position))
    (fun position => rows (scheme.incoming position)) (fun position => rows (scheme.outgoing position))
    (CommonCanonicalOpen.instantiate (Fin.addCases captured parameters) scheme.output)

def Instances (scheme : Scheme fixed rowSlots arguments generalized) (rows : Fin rowSlots → Row)
    (captured : Fin fixed → Ty) (target : Ty) : Prop :=
  ∃ parameters : Fin generalized → Ty, Subtype (instantiate scheme rows captured parameters) target

/-- The finite union assignment solves all shared argument lower bounds at
once. Every remaining target comparison reduces to the computed transfer. -/
theorem instances_spine_exact (scheme : Scheme fixed rowSlots arguments generalized) (rows : Fin rowSlots → Row)
    (captured : Fin fixed → Ty) (inputs : Fin arguments → Ty) (incoming outgoing : Fin arguments → Row) (output : Ty) :
    Instances scheme rows captured (spine arguments inputs incoming outgoing output) ↔
      (∀ position, Common.rowLe (incoming position) (rows (scheme.incoming position)) ∧
        Common.rowLe (rows (scheme.outgoing position)) (outgoing position)) ∧
      Subtype (applyTransfer scheme captured inputs) output := by
  constructor
  · rintro ⟨parameters, below⟩
    have parts := (spine_below_iff _ _ _ _ _ _ _ _ _).mp below
    exact ⟨fun position => (parts.1 position).2,
      Common.subtype_trans (transfer_le_output scheme captured inputs parameters
        (fun position => (parts.1 position).1)) parts.2⟩
  · rintro ⟨rowsBelow, outputBelow⟩
    refine ⟨selected scheme inputs, (spine_below_iff _ _ _ _ _ _ _ _ _).mpr ?_⟩
    exact ⟨fun position => ⟨input_le_selected scheme inputs position, rowsBelow position⟩,
      (applyTransfer_eq scheme captured inputs) ▸ outputBelow⟩

end Yulang.CommonCanonicalCurriedTransfer
