import Yulang.CommonRoleCanonicalPayloadCandidates
import Yulang.CommonGroundScalarCasts
import Yulang.CommonNominalHeads

/-! Finite case analysis for the non-variable nominal question. `cover` is
an explicitly proposed finite alternative relation, not the language's
unapproved operational capture. The nominal invariance facts use the actual
API. No nested union/nominal Common carrier or full source bridge is claimed. -/
namespace Yulang.CommonRoleNominalCoverBoundary

inductive ArgumentCode where
  | integer
  | boolean
  | joined
  deriving DecidableEq, Repr

def ArgumentCode.scalar : ArgumentCode → CommonGroundScalarCasts.Scalar
  | .integer => .atom (.base .int)
  | .boolean => .atom (.base .bool)
  | .joined => .union (.atom (.base .int)) (.atom (.base .bool))

def ArgumentCode.meaning (argument : ArgumentCode) : Common.Ty :=
  CommonGroundScalarCasts.meaning argument.scalar

theorem argument_equivalent_exact (first last : ArgumentCode) :
    Common.Equivalent first.meaning last.meaning ↔ first = last := by
  rw [ArgumentCode.meaning, ArgumentCode.meaning, CommonGroundScalarCasts.scalar_canonical_exact]
  cases first <;> cases last <;> decide +kernel

def box (argument : Common.Ty) : CommonNominalHeads.Head := ⟨0, [.value argument]⟩

theorem box_invariant (first last : Common.Ty) :
    CommonNominalHeads.Subtype (box first) (box last) ↔ Common.Equivalent first last := by
  simp [CommonNominalHeads.nominal_head_invariant_exact, box,
    CommonNominalHeads.ArgumentsEquivalent, CommonNominalHeads.Argument.equivalent_value]

theorem coded_box_exact (first last : ArgumentCode) :
    CommonNominalHeads.Subtype (box first.meaning) (box last.meaning) ↔ first = last :=
  (box_invariant _ _).trans (argument_equivalent_exact _ _)

theorem boxes_distinct : ¬ CommonNominalHeads.Subtype
    (box ArgumentCode.integer.meaning) (box ArgumentCode.boolean.meaning) := by
  rw [coded_box_exact]
  decide +kernel

theorem joined_not_integer : ¬ CommonNominalHeads.Subtype
    (box ArgumentCode.joined.meaning) (box ArgumentCode.integer.meaning) := by
  rw [coded_box_exact]
  decide +kernel

theorem joined_not_boolean : ¬ CommonNominalHeads.Subtype
    (box ArgumentCode.joined.meaning) (box ArgumentCode.boolean.meaning) := by
  rw [coded_box_exact]
  decide +kernel

theorem no_single_box_upper (argument : Common.Ty) :
    ¬ (CommonNominalHeads.Subtype (box ArgumentCode.integer.meaning) (box argument) ∧
      CommonNominalHeads.Subtype (box ArgumentCode.boolean.meaning) (box argument)) := by
  rintro ⟨integer, boolean⟩
  have equal := Common.equivalent_trans ((box_invariant _ _).mp integer)
    (Common.equivalent_symm ((box_invariant _ _).mp boolean))
  exact CommonRoleAssociatedObstructions.int_not_bool equal

def cover (source target : List ArgumentCode) : Bool :=
  source.all (fun argument => target.contains argument) &&
    target.all (fun argument => source.contains argument)

/-- Only a finite alternative-support experiment. It does not define the
Common semantics of a nominal nested inside a union or variant. -/
def Covers (source target : List ArgumentCode) : Prop :=
  (∀ argument ∈ source, ∃ expected ∈ target,
    CommonNominalHeads.Subtype (box argument.meaning) (box expected.meaning)) ∧
  (∀ expected ∈ target, ∃ argument ∈ source,
    CommonNominalHeads.Subtype (box expected.meaning) (box argument.meaning))

theorem cover_exact (source target : List ArgumentCode) : cover source target = true ↔ Covers source target := by
  simp [cover, Covers, List.all_eq_true, coded_box_exact]

def goalAlternatives : List ArgumentCode := [.integer, .boolean]
def codes : List ArgumentCode := [.integer, .boolean, .joined]

def finiteCovers : List (ArgumentCode × ArgumentCode) :=
  (codes.flatMap (fun first => codes.map (fun last => (first, last)))).filter
    (fun pair => cover [pair.1, pair.2] goalAlternatives)

theorem covers_enumerated : finiteCovers = [(.integer, .boolean), (.boolean, .integer)] := by decide +kernel

theorem forward_cover : Covers [.integer, .boolean] goalAlternatives :=
  (cover_exact _ _).mp (by decide +kernel)

theorem reverse_cover : Covers [.boolean, .integer] goalAlternatives :=
  (cover_exact _ _).mp (by decide +kernel)

theorem joined_fails : ¬ Covers [.joined, .joined] goalAlternatives := by
  rw [← cover_exact]
  decide +kernel

theorem covers_change_child : ¬ Common.Equivalent
    ArgumentCode.integer.meaning ArgumentCode.boolean.meaning := by
  rw [argument_equivalent_exact]
  decide +kernel

/-- Size-only representation of a normalized single-tag frame with two
invariant unary nominal alternatives. Argument terms are supplied as-is;
only identical alternatives are contracted. This is not a full nominal
lowering or a new operational capture rule. -/
def nominalFrame (constructor : Nat) (first last : Roles.Term) : Roles.Term :=
  if first = last then .app 3 [.app constructor [first]]
  else .app 3 [.app 4 [.app constructor [first], .app constructor [last]]]

theorem private_child_decreases (constructor : Nat) (first last : Roles.Term) :
    first.size < (nominalFrame constructor first last).size ∧
      ∀ name, first.occurrences name ≤ (nominalFrame constructor first last).occurrences name := by
  constructor
  · by_cases same : first = last <;>
      simp [nominalFrame, same, Roles.Term.size, Roles.argsSize] <;> omega
  · intro name
    by_cases same : first = last <;>
      simp [nominalFrame, same, Roles.Term.occurrences, Roles.argsOccurrences]

theorem all_term_substitutions_decrease (constructor : Nat) (image : Roles.Subst) :
    (image 0).size < (nominalFrame constructor (image 0) (image 1)).size ∧
      ∀ name, (image 0).occurrences name ≤
        (nominalFrame constructor (image 0) (image 1)).occurrences name := private_child_decreases _ _ _

def proposedCandidateKeys (permitCover : Bool) : List Nat :=
  (if permitCover && !finiteCovers.isEmpty then [0] else []) ++ [1]

theorem allow_cover_two_candidates : proposedCandidateKeys true = [0, 1] := by decide +kernel
theorem forbid_cover_one_candidate : proposedCandidateKeys false = [1] := by decide +kernel

end Yulang.CommonRoleNominalCoverBoundary
