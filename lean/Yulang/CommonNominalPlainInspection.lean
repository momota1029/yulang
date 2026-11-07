import Yulang.CommonNominalFiniteRigidInspection

/-!
# Ordinary shared-node/row outputs of the executable nominal inspector

This finite representation contains only child-ID inequalities and row-ID
inequalities. Its encoding is literally the already proved inspector output,
including nominal invariant comparisons. No type comparison, profile,
assignment or semantic certificate is stored in a returned check.
-/

namespace Yulang.CommonNominalPlainInspection

open CommonNominalCarrier (Ty Row)
open CommonNominalRigidInspection (Node)
open Core.PresenceGeneration (Comp)

inductive Check (Rows Child : Type) where
  | type : Child → Child → Check Rows Child
  | row : Rows → Rows → Check Rows Child
  deriving DecidableEq

def Check.encode : Check Rows Child → PresenceNormalForm.Atom (Child ⊕ Rows)
  | .type first last => CommonNominalRigidInspection.typeAtom first last
  | .row first last => CommonNominalRigidInspection.rowAtom first last

def Check.Holds (rows : Rows → Row) (children : Child → Ty) : Check Rows Child → Prop
  | .type first last => CommonNominalCarrier.Subtype (children first) (children last)
  | .row first last => Common.rowLe (rows first) (rows last)

def Check.At (depth : Nat) (rows : Rows → Row) (children : Child → Ty) : Check Rows Child → Prop
  | .type first last => CommonNominalFiniteRigidInspection.GuardedAt depth (children first) (children last)
  | .row first last => Common.rowLe (rows first) (rows last)

def append (first last : Option (List (Check Rows Child))) : Option (List (Check Rows Child)) := do
  let before ← first
  let after ← last
  return before ++ after

def arguments : List (Child ⊕ Rows) → List (Child ⊕ Rows) → Option (List (Check Rows Child))
  | [], [] => some []
  | .inl first :: rest, .inl last :: tail =>
      append (some [.type first last, .type last first]) (arguments rest tail)
  | .inr first :: rest, .inr last :: tail =>
      append (some [.row first last, .row last first]) (arguments rest tail)
  | _, _ => none

def inspect : Node Rows Child → Node Rows Child → Option (List (Check Rows Child))
  | .bottom, _ => some []
  | _, .top => some []
  | .float, .float => some []
  | .base first, .base last => if first = last then some [] else none
  | .pair first last, .pair first' last' => some [.type first first', .type last last']
  | .variant first payload, .variant last payload' => if first = last then some [.type payload payload'] else none
  | .arrow input incoming output outgoing, .arrow input' incoming' output' outgoing' =>
      some [.type input' input, .row incoming' incoming, .type output output', .row outgoing outgoing']
  | .nominal first args, .nominal last args' => if first = last then arguments args args' else none
  | _, _ => none

theorem encode_append (first last : Option (List (Check Rows Child))) :
    (append first last).map (List.map Check.encode) = CommonNominalCarrierConstraints.append
      (first.map (List.map Check.encode)) (last.map (List.map Check.encode)) := by
  cases first <;> cases last <;> simp [append, CommonNominalCarrierConstraints.append]

theorem encode_arguments (first last : List (Child ⊕ Rows)) :
    (arguments first last).map (List.map Check.encode) =
      CommonNominalCarrierConstraints.compileArguments
        (first.map CommonNominalRigidInspection.argumentTerm)
        (last.map CommonNominalRigidInspection.argumentTerm) := by
  induction first generalizing last with
  | nil => cases last <;> rfl
  | cons head tail ih =>
      cases last with
      | nil => cases head <;> rfl
      | cons head' tail' =>
          cases head <;> cases head'
          all_goals simp only [arguments, List.map_cons, CommonNominalRigidInspection.argumentTerm,
            CommonNominalCarrierConstraints.compileArguments, CommonNominalCarrierConstraints.compileArgument]
          all_goals first
            | exact rfl
            | rw [encode_append, ih]; rfl

/-- Literal identity of finite executable results, including failure. -/
theorem encode_inspect (source target : Node Rows Child) :
    (inspect source target).map (List.map Check.encode) = CommonNominalRigidInspection.inspect source target := by
  cases source <;> cases target
  case nominal.nominal first args last args' =>
    by_cases same : first = last
    · simp only [inspect, same, ↓reduceIte, CommonNominalRigidInspection.inspect,
        CommonNominalCarrierConstraints.compile, CommonNominalRigidInspection.headTerm]
      exact encode_arguments args args'
    · simp [inspect, same, CommonNominalRigidInspection.inspect,
        CommonNominalCarrierConstraints.compile, CommonNominalRigidInspection.headTerm]
  all_goals simp [inspect, CommonNominalRigidInspection.inspect, Check.encode]

@[simp] theorem check_encode_holds (rows : Rows → Row) (children : Child → Ty) (check : Check Rows Child) :
    check.encode.Holds CommonNominalCarrier.model (CommonNominalRigidInspection.assignment rows children) ↔
      check.Holds rows children := by cases check <;> rfl

@[simp] theorem check_encode_at (depth : Nat) (rows : Rows → Row) (children : Child → Ty)
    (check : Check Rows Child) :
    check.encode.Holds CommonNominalFiniteRigidInspection.finiteModel
      (CommonNominalFiniteRigidInspection.assignment rows
        (CommonNominalFiniteRigidInspection.guardedChildren depth children)) ↔ check.At depth rows children := by
  cases check <;> rfl

def Satisfied (rows : Rows → Row) (children : Child → Ty) (result : Option (List (Check Rows Child))) : Prop :=
  ∃ checks, result = some checks ∧ ∀ check ∈ checks, check.Holds rows children

theorem inspect_exact (rows : Rows → Row) (children : Child → Ty) (source target : Node Rows Child) :
    Satisfied rows children (inspect source target) ↔
      CommonNominalCarrier.Subtype (source.eval rows children) (target.eval rows children) := by
  rw [← CommonNominalRigidInspection.inspect_exact rows children source target, ← encode_inspect]
  cases inspect source target <;>
    simp [Satisfied, CommonNominalRigidInspection.Satisfied, PresenceNormalForm.All]

theorem inspect_at_sound (depth : Nat) (rows : Rows → Row) (children : Child → Ty)
    (source target : Node Rows Child) (checks : List (Check Rows Child))
    (returned : inspect source target = some checks) (valid : ∀ check ∈ checks, check.At depth rows children) :
    CommonNominalFiniteRigidInspection.BelowAt depth (source.eval rows children) (target.eval rows children) := by
  apply CommonNominalFiniteRigidInspection.inspect_at_sound depth rows children source target
  refine ⟨checks.map Check.encode, ?_, ?_⟩
  · rw [← encode_inspect, returned]; rfl
  · intro atom included
    obtain ⟨check, member, rfl⟩ := List.mem_map.mp included
    exact (check_encode_at depth rows children check).mpr (valid check member)

end Yulang.CommonNominalPlainInspection
