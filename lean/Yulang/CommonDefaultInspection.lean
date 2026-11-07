import Yulang.CommonDefaultTargetSplit
import Yulang.CommonRecordTailFinite

/-!
# Complete finite outer inspection of whole-record default subtyping

Every outer default comparison, with an arbitrary common target, compiles to
a finite list of proper-child subtype comparisons. Executable head, presence
and initial-cutoff checks are evaluated by the inspector; a failed Boolean
check produces no branch. Remaining record labels are covered by their actual
finite support and one fresh representative.

The original outer whole-default comparison, optional observation obligation
and record-tail relation are not retained as atoms. Payload projections retain
the actual shared regular children, which may themselves contain nested
defaults or return to a regular graph state. Solving those child comparisons
across an entire input graph is a separate saturation/compiler theorem.
-/

namespace Yulang.CommonDefaultInspection

open CommonPayloadProjection
open CommonRecordTailProfiles
open CommonDefaultTargetSplit

/-- Intermediate inspection checks. Boolean checks are discharged before
the final alternatives are returned. -/
inductive Check where
  | flag : Bool → Check
  | childBelow : Common.Ty → Common.Ty → Check

def Check.Holds : Check → Prop
  | .flag value => value = true
  | .childBelow source target => Common.Subtype source target

def ChecksHold (checks : List Check) : Prop := ∀ check ∈ checks, check.Holds

@[simp] theorem checksHold_nil : ChecksHold [] := by simp [ChecksHold]

@[simp] theorem checksHold_cons (check : Check) (checks : List Check) :
    ChecksHold (check :: checks) ↔ check.Holds ∧ ChecksHold checks := by
  simp only [ChecksHold, List.mem_cons, or_imp, forall_and, forall_eq]

@[simp] theorem checksHold_append (first last : List Check) :
    ChecksHold (first ++ last) ↔ ChecksHold first ∧ ChecksHold last := by
  simp only [ChecksHold, List.mem_append, or_imp, forall_and]

theorem checksHold_flatMap (labels : List Nat) (checks : Nat → List Check) :
    ChecksHold (labels.flatMap checks) ↔ ∀ label ∈ labels, ChecksHold (checks label) := by
  constructor
  · intro holds label member check included
    exact holds check (List.mem_flatMap.mpr ⟨label, member, included⟩)
  · intro holds check member
    obtain ⟨label, included, present⟩ := List.mem_flatMap.mp member
    exact holds label included check present

def compileProfile : Option Common.Ty → Option Common.Ty → List Check
  | _, none => []
  | none, some _ => [.flag false]
  | some source, some target => [.childBelow source target]

theorem compileProfile_exact (source target : Option Common.Ty) :
    ChecksHold (compileProfile source target) ↔ ProfileLe source target := by
  cases source <;> cases target <;>
    simp [compileProfile, ProfileLe, ProfileBelow, Check.Holds]

theorem implication_flag (source target : Bool) :
    ((!target) || source) = true ↔ (target = true → source = true) := by
  cases source <;> cases target <;> simp

def compileLabel (source target : Common.Ty) (label : Nat) : List Check :=
  [.flag ((!initialField [] label target) || initialField [] label source),
   .flag ((!initialOptional [] label target) || initialOptional [] label source)] ++
  compileProfile (fieldType [] label source) (fieldType [] label target) ++
  [.childBelow ((optionalType [] label source).getD .top) ((optionalType [] label target).getD .top)]

theorem compileLabel_exact (source target : Common.Ty) (label : Nat) :
    ChecksHold (compileLabel source target label) ↔ AtLabel source target label := by
  simp only [compileLabel, checksHold_append, checksHold_cons, Check.Holds, checksHold_nil,
    and_true, compileProfile_exact, implication_flag, AtLabel, and_assoc]

def compileTail (hidden : List Nat) (source target : Common.Ty) : List Check :=
  (CommonRecordTailFinite.inspectLabels hidden source target).flatMap fun label =>
    if label ∈ hidden then [] else compileLabel source target label

theorem compileTail_exact (hidden : List Nat) (source target : Common.Ty) :
    ChecksHold (compileTail hidden source target) ↔ Common.RecordTailLe hidden source target := by
  rw [compileTail, checksHold_flatMap, CommonRecordTailFinite.tail_finite_exact]
  apply forall_congr'
  intro label
  apply imp_congr_right
  intro _
  by_cases member : label ∈ hidden
  · simp [member]
  · simpa only [member, ↓reduceIte, not_false_eq_true, true_implies] using
      compileLabel_exact source target label

def compileDefault (label : Nat) (source fallback target : Common.Ty) : List Check :=
  [.flag (!CommonRecordEnvelope.outsideRecords target)] ++
  compileProfile (selectedField label source fallback) (fieldType [] label target) ++
  compileProfile (selectedOptional label source fallback) (optionalType [] label target) ++
  compileTail [label] source target

theorem compileDefault_exact (label : Nat) (source fallback target : Common.Ty) :
    ChecksHold (compileDefault label source fallback target) ↔
      Common.Subtype (Common.recordDefault label source fallback) target := by
  rw [default_target_split]
  simp only [compileDefault, checksHold_append, checksHold_cons, Check.Holds, checksHold_nil,
    and_true, compileProfile_exact, compileTail_exact, and_assoc]
  cases CommonRecordEnvelope.outsideRecords target <;> simp

/-- A final atom is exactly one ordinary subtype comparison between extracted
proper children. All Boolean and record-tail obligations have been removed. -/
abbrev Obligation := Common.Ty × Common.Ty
abbrev Branch := List Obligation

def IndependentObligationsHold (branch : Branch) : Prop :=
  ∀ obligation ∈ branch, Common.Subtype obligation.1 obligation.2

@[simp] theorem independent_nil : IndependentObligationsHold [] := by
  simp [IndependentObligationsHold]

@[simp] theorem independent_cons (source target : Common.Ty) (branch : Branch) :
    IndependentObligationsHold ((source, target) :: branch) ↔
      Common.Subtype source target ∧ IndependentObligationsHold branch := by
  simp only [IndependentObligationsHold, List.mem_cons, or_imp, forall_and, forall_eq]

/-- Execute the finite checks and retain only proper-child comparisons. -/
def discharge : List Check → Option Branch
  | [] => some []
  | .flag false :: _ => none
  | .flag true :: rest => discharge rest
  | .childBelow source target :: rest => (discharge rest).map ((source, target) :: ·)

theorem discharge_exact (checks : List Check) :
    ChecksHold checks ↔
      ∃ branch, discharge checks = some branch ∧ IndependentObligationsHold branch := by
  induction checks with
  | nil => simp [discharge]
  | cons check rest ih =>
      cases check with
      | flag value =>
          cases value <;> simp [discharge, Check.Holds, ih]
      | childBelow source target =>
          rw [checksHold_cons, Check.Holds, ih]
          cases remaining : discharge rest <;>
            simp [discharge, remaining, independent_cons]

def inspectDefault (label : Nat) (source fallback target : Common.Ty) : List Branch :=
  match discharge (compileDefault label source fallback target) with
  | none => []
  | some branch => [branch]

/-- Complete finite outer inspector for arbitrary common source, fallback
and target types, including masks, mixed heads and regular graphs. The
returned obligations are ordinary proper-child subtype comparisons only. -/
theorem default_inspect_exact (label : Nat) (source fallback target : Common.Ty) :
    Common.Subtype (Common.recordDefault label source fallback) target ↔
      ∃ branch ∈ inspectDefault label source fallback target, IndependentObligationsHold branch := by
  rw [← compileDefault_exact, discharge_exact]
  cases outcome : discharge (compileDefault label source fallback target) <;>
    simp [inspectDefault, outcome]

end Yulang.CommonDefaultInspection
