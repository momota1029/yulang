import Yulang.CommonPresenceInspection
import Yulang.PresenceSourceConstraintSupport

/-!
# Row-shape preservation by common presence inspection

Inspection copies the two arrow annotations and the queried row. It creates
no row joins. The preservation theorem is polymorphic in the chosen property
of row syntax, so it applies before interpreting symbolic row variables.

The final theorem sends the actual emitted row atoms to `RowFlowSchemes`.
It does not identify arbitrary target-observation tests with a complete
subtype saturation or claim that source-to-graph lowering is finished.
-/

namespace Yulang.CommonPresenceInspectionRows

open CommonPresenceInspection
open CommonSyntax (Layer)
open CommonFinite (Observation)

universe u v
variable {Row : Type u} {Index : Type v}

def LayerRows (property : Row → Prop) : Layer Row Index → Prop
  | .union first last | .inter first last => LayerRows property first ∧ LayerRows property last
  | .record _ _ rest | .recordDefault _ rest _ | .mask _ rest => LayerRows property rest
  | .arrow _ incoming _ outgoing => property incoming ∧ property outgoing
  | _ => True

def ObservationRows (property : Row → Prop) : Observation Row → Prop
  | .arrowInputRow row | .arrowOutputRow row => property row
  | _ => True

def ObligationRows (property : Row → Prop) : Obligation Row Index → Prop
  | .rowBelow first last => property first ∧ property last
  | _ => True

def AllRows (property : Row → Prop) (alternatives : Alternatives Row Index) : Prop :=
  ∀ branch ∈ alternatives, ∀ obligation ∈ branch, ObligationRows property obligation

@[simp] theorem allRows_truth (property : Row → Prop) : AllRows (Index := Index) property truth := by
  simp [AllRows, truth]

@[simp] theorem allRows_falsity (property : Row → Prop) : AllRows (Index := Index) property falsity := by
  simp [AllRows, falsity]

@[simp] theorem allRows_atom (property : Row → Prop) (obligation : Obligation Row Index) :
    AllRows property (atom obligation) ↔ ObligationRows property obligation := by
  simp [AllRows, atom]

@[simp] theorem allRows_constant (property : Row → Prop) (value : Bool) :
    AllRows (Index := Index) property (constant value) := by
  cases value <;> simp [constant]

@[simp] theorem allRows_disjoin (property : Row → Prop) (first last : Alternatives Row Index) :
    AllRows property (disjoin first last) ↔ AllRows property first ∧ AllRows property last := by
  simp only [AllRows, disjoin, List.mem_append, or_imp, forall_and]

@[simp] theorem allRows_conjoin (property : Row → Prop) (first last : Alternatives Row Index)
    (firstRows : AllRows property first) (lastRows : AllRows property last) :
    AllRows property (conjoin first last) := by
  intro branch member obligation present
  simp only [conjoin, List.mem_flatMap, List.mem_map] at member
  obtain ⟨left, leftMember, right, rightMember, rfl⟩ := member
  exact (List.mem_append.mp present).elim
    (firstRows left leftMember obligation) (lastRows right rightMember obligation)

/-- Every emitted row operand has the input row property, for any mask,
constructor cutoff and observation. Record/default recursion cannot create
an additional row shape. Child obligations retain their original references. -/
theorem inspect_preserves_rows (property : Row → Prop) (depth : Nat) (hidden : List Nat)
    (source : Layer Row Index) (obs : Observation Row)
    (sourceRows : LayerRows property source) (observationRows : ObservationRows property obs) :
    AllRows property (inspect depth hidden source obs) := by
  induction source generalizing depth hidden obs with
  | record current payload rest ih =>
      simp only [LayerRows] at sourceRows
      cases obs <;> simp [inspect, ObligationRows]
      all_goals split <;> try simp [ObligationRows]
      all_goals exact ih _ _ _ sourceRows trivial
  | recordDefault current rest fallback ih =>
      simp only [LayerRows] at sourceRows
      cases depth <;> cases obs <;> simp [inspect, ObligationRows]
      all_goals split <;> try simp
      all_goals try exact ih _ _ _ sourceRows trivial
      all_goals
        apply allRows_conjoin
        · exact ih _ _ _ sourceRows trivial
        · apply (allRows_disjoin _ _ _).mpr
          exact ⟨ih _ _ _ sourceRows trivial, by simp [ObligationRows]⟩
  | _ =>
      cases obs <;> simp_all [LayerRows, ObservationRows, inspect, ObligationRows]
      all_goals split <;> simp_all [ObligationRows]

def emittedRows : Branch (Core.PresenceGeneration.RowTerm (Fin n)) Index → RowFlowSchemes.Problem n
  | [] => []
  | .rowBelow first last :: rest =>
      (PresenceSourceConstraintSupport.originalRow first,
        PresenceSourceConstraintSupport.originalRow last) :: emittedRows rest
  | _ :: rest => emittedRows rest

theorem emittedRows_supported (branch : Branch (Core.PresenceGeneration.RowTerm (Fin n)) Index)
    (valid : ∀ obligation ∈ branch,
      ObligationRows (fun row => PresenceSourceConstraintSupport.simpleRow row = true) obligation) :
    RowFlowSchemes.supported (emittedRows branch) = true := by
  induction branch with
  | nil => rfl
  | cons obligation rest ih =>
      have first := valid obligation List.mem_cons_self
      have remaining := ih (fun actual member => valid actual (List.mem_cons_of_mem _ member))
      cases obligation with
      | child | argument | role => exact remaining
      | rowBelow firstRow lastRow =>
          simpa only [emittedRows, RowFlowSchemes.supported, List.all_cons,
            PresenceSourceConstraintSupport.originalRow_supported, Bool.and_eq_true]
            using And.intro first.2 remaining

/-- Actual finite inspection produces a row problem accepted by the existing
row solver whenever source arrow annotations and the compared row are simple
variables or empty. No successful type-solver run is supplied. -/
theorem inspected_rows_supported (depth : Nat) (hidden : List Nat)
    (source : Layer (Core.PresenceGeneration.RowTerm (Fin n)) Index)
    (obs : Observation (Core.PresenceGeneration.RowTerm (Fin n)))
    (sourceRows : LayerRows (fun row => PresenceSourceConstraintSupport.simpleRow row = true) source)
    (observationRows : ObservationRows (fun row => PresenceSourceConstraintSupport.simpleRow row = true) obs)
    (branch : Branch (Core.PresenceGeneration.RowTerm (Fin n)) Index)
    (member : branch ∈ inspect depth hidden source obs) :
    RowFlowSchemes.supported (emittedRows branch) = true :=
  emittedRows_supported branch
    (inspect_preserves_rows _ depth hidden source obs sourceRows observationRows branch member)

end Yulang.CommonPresenceInspectionRows
