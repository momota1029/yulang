import Yulang.CommonSymbolicRecordProfiles

/-!
# Independent finite child, row and record-profile constraints

These are the residual atoms produced by symbolic outer inspection. Their
syntax contains only shared child/node IDs, symbolic rows, finite lattice
payloads and finite mask/presence/profile expressions. There is no atom for
the original comparison between two whole rigid source constructors.

Compilation and static discharge do not receive a row or value assignment.
Only the independent interpretation reads those assignments. Profile
primitives inspect an original unknown node; known outer constructors have
already been expanded by the symbolic profile compiler.
-/

namespace Yulang.CommonSymbolicConstraints

open Common (Ty Row)
open CommonPayloadProjection (Payload)
open CommonSymbolicRecordProfiles (BoolExpr ProfileExpr)

universe u v w

inductive Check (Rows : Type u) (Node : Type v) (Child : Type w) where
  | childBelow : Payload Child → Payload Child → Check Rows Node Child
  | rowBelow : Rows → Rows → Check Rows Node Child
  | flag : BoolExpr Node → Check Rows Node Child
  | profileBelow : ProfileExpr Node Child → Payload Child → Check Rows Node Child

def Check.Holds (rows : Rows → Row) (nodes : Node → Ty) (children : Child → Ty) :
    Check Rows Node Child → Prop
  | .childBelow source target => Common.Subtype (source.evalLayer children) (target.evalLayer children)
  | .rowBelow source target => Common.rowLe (rows source) (rows target)
  | .flag expression => expression.eval nodes = true
  | .profileBelow profile target =>
      CommonPayloadProjection.ProfileBelow (profile.eval nodes children) (target.evalLayer children)

abbrev Branch (Rows : Type u) (Node : Type v) (Child : Type w) := List (Check Rows Node Child)
abbrev Alternatives (Rows : Type u) (Node : Type v) (Child : Type w) := List (Branch Rows Node Child)

def Branch.Holds (rows : Rows → Row) (nodes : Node → Ty) (children : Child → Ty)
    (branch : Branch Rows Node Child) : Prop := ∀ check ∈ branch, check.Holds rows nodes children

def Alternatives.Holds (rows : Rows → Row) (nodes : Node → Ty) (children : Child → Ty)
    (alternatives : Alternatives Rows Node Child) : Prop :=
  ∃ branch ∈ alternatives, Branch.Holds rows nodes children branch

@[simp] theorem holds_nil (rows : Rows → Row) (nodes : Node → Ty) (children : Child → Ty) :
    Branch.Holds rows nodes children [] := by simp [Branch.Holds]

@[simp] theorem holds_cons (rows : Rows → Row) (nodes : Node → Ty) (children : Child → Ty)
    (check : Check Rows Node Child) (rest : Branch Rows Node Child) :
    Branch.Holds rows nodes children (check :: rest) ↔
      check.Holds rows nodes children ∧ Branch.Holds rows nodes children rest := by
  simp only [Branch.Holds, List.mem_cons, forall_eq_or_imp]

@[simp] theorem holds_append (rows : Rows → Row) (nodes : Node → Ty) (children : Child → Ty)
    (first last : Branch Rows Node Child) :
    Branch.Holds rows nodes children (first ++ last) ↔
      Branch.Holds rows nodes children first ∧ Branch.Holds rows nodes children last := by
  simp only [Branch.Holds, List.mem_append, or_imp, forall_and]

theorem holds_flatMap {Index : Type} (rows : Rows → Row) (nodes : Node → Ty) (children : Child → Ty)
    (entries : List Index) (checks : Index → Branch Rows Node Child) :
    Branch.Holds rows nodes children (entries.flatMap checks) ↔
      ∀ entry ∈ entries, Branch.Holds rows nodes children (checks entry) := by
  constructor
  · intro valid entry member check included
    exact valid check (List.mem_flatMap.mpr ⟨entry, member, included⟩)
  · intro valid check member
    obtain ⟨entry, included, present⟩ := List.mem_flatMap.mp member
    exact valid entry included check present

@[simp] theorem alternatives_nil (rows : Rows → Row) (nodes : Node → Ty) (children : Child → Ty) :
    ¬ Alternatives.Holds rows nodes children [] := by simp [Alternatives.Holds]

@[simp] theorem alternatives_singleton (rows : Rows → Row) (nodes : Node → Ty) (children : Child → Ty)
    (branch : Branch Rows Node Child) :
    Alternatives.Holds rows nodes children [branch] ↔ Branch.Holds rows nodes children branch := by
  simp [Alternatives.Holds]

@[simp] theorem alternatives_prepend (rows : Rows → Row) (nodes : Node → Ty) (children : Child → Ty)
    (check : Check Rows Node Child) (alternatives : Alternatives Rows Node Child) :
    Alternatives.Holds rows nodes children (alternatives.map (check :: ·)) ↔
      check.Holds rows nodes children ∧ Alternatives.Holds rows nodes children alternatives := by
  constructor
  · rintro ⟨branch, member, valid⟩
    obtain ⟨original, included, rfl⟩ := List.mem_map.mp member
    have accepted := (holds_cons rows nodes children check original).mp valid
    exact ⟨accepted.1, original, included, accepted.2⟩
  · rintro ⟨accepted, original, included, valid⟩
    exact ⟨check :: original, List.mem_map.mpr ⟨original, included, rfl⟩,
      (holds_cons rows nodes children check original).mpr ⟨accepted, valid⟩⟩

/-- Statically false branches disappear before any parameter is supplied.
Unknown Boolean/profile primitives stay as explicit symbolic constraints. -/
def discharge : Branch Rows Node Child → Alternatives Rows Node Child
  | [] => [[]]
  | .flag (.literal false) :: _ => []
  | .flag (.literal true) :: rest => discharge rest
  | check :: rest => (discharge rest).map (check :: ·)

/-- The computation uses no interpreter, success certificate or fuel. -/
theorem discharge_exact (rows : Rows → Row) (nodes : Node → Ty) (children : Child → Ty)
    (checks : Branch Rows Node Child) :
    Alternatives.Holds rows nodes children (discharge checks) ↔
      Branch.Holds rows nodes children checks := by
  induction checks with
  | nil => simp [discharge]
  | cons check rest ih =>
      cases check with
      | childBelow | rowBelow | profileBelow => simp only [discharge, alternatives_prepend, ih, holds_cons]
      | flag expression =>
          cases expression with
          | literal value => cases value <;> simp [discharge, Check.Holds, BoolExpr.eval, ih]
          | atom | and | or | not => simp only [discharge, alternatives_prepend, ih, holds_cons]

end Yulang.CommonSymbolicConstraints
