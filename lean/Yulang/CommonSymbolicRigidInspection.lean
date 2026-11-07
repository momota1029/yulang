import Yulang.CommonSymbolicConstraints
import Yulang.CommonRigidHeadInspection

/-!
# Symbolic non-record constructor inspection

Every compiler below consumes finite syntax only. Pair/variant/arrow
comparisons emit original child IDs and symbolic row comparisons; distinct
heads are discharged by the independent common role observation theorem.
All child assignments are arbitrary common types, with no restrictions on
negative arguments, masks, defaults, roles or regular graphs.

The two lattice eliminations are source union and target intersection.
Source intersection and target union are not asserted to be disjunctions of
child comparisons. The generated-endpoint theorem and the full source
dispatcher address which eliminations apply to actual first-pass inputs.
-/

namespace Yulang.CommonSymbolicRigidInspection

open Common (Ty Row)
open CommonSymbolicConstraints (Check Branch)
open CommonPayloadProjection (Payload)

universe u v

inductive Node (Rows : Type u) (Child : Type v) where
  | bottom | top
  | base : Inference.Base → Node Rows Child
  | pair : Child → Child → Node Rows Child
  | variant : Nat → Child → Node Rows Child
  | arrow : Child → Rows → Child → Rows → Node Rows Child

def Node.eval (rows : Rows → Row) (children : Child → Ty) : Node Rows Child → Ty
  | .bottom => .bottom
  | .top => .top
  | .base scalar => .base scalar
  | .pair first last => Common.pair (children first) (children last)
  | .variant label payload => Common.variant label (children payload)
  | .arrow input incoming output outgoing =>
      Common.arrow (children input) (rows incoming) (children output) (rows outgoing)

def inspect : Node Rows Child → Node Rows Child → Branch Rows NodeIndex Child
  | .bottom, _ => []
  | _, .top => []
  | .base first, .base last => [.flag (.literal (decide (first = last)))]
  | .pair first last, .pair first' last' =>
      [.childBelow (.ref first) (.ref first'), .childBelow (.ref last) (.ref last')]
  | .variant first payload, .variant last payload' =>
      [.flag (.literal (decide (first = last))), .childBelow (.ref payload) (.ref payload')]
  | .arrow input incoming output outgoing, .arrow input' incoming' output' outgoing' =>
      [.childBelow (.ref input') (.ref input), .rowBelow incoming' incoming,
        .childBelow (.ref output) (.ref output'), .rowBelow outgoing outgoing']
  | _, _ => [.flag (.literal false)]

/-- Exact at every independent row and common child assignment; the compiler
does not receive either assignment. No rigid comparison is retained as an atom. -/
theorem inspect_exact (rows : Rows → Row) (nodes : NodeIndex → Ty) (children : Child → Ty)
    (source target : Node Rows Child) :
    Branch.Holds rows nodes children (inspect source target) ↔
      Common.Subtype (source.eval rows children) (target.eval rows children) := by
  cases source <;> cases target
  all_goals simp only [inspect, CommonSymbolicConstraints.holds_nil,
    CommonSymbolicConstraints.holds_cons, Check.Holds, CommonSymbolicRecordProfiles.BoolExpr.eval,
    Payload.evalLayer, Node.eval, and_true, Bool.false_eq_true, decide_eq_true_eq]
  all_goals try exact (iff_true_intro (CommonBoundCoalescing.bottom_le _)).symm
  all_goals try exact (iff_true_intro (CommonBoundCoalescing.le_top _)).symm
  case base.base first last => exact (CommonRigidHeadInspection.base_iff first last).symm
  case pair.pair => exact (Common.common_pair_iff _ _ _ _).symm
  case variant.variant => exact (CommonRigidHeadInspection.variant_iff _ _ _ _).symm
  case arrow.arrow => exact (Common.common_arrow_iff _ _ _ _ _ _ _ _).symm
  all_goals
    exact (iff_false_intro (CommonRigidHeadInspection.rigid_mismatch rfl rfl
      (by simp [CommonRigidHeadInspection.head, Common.pair, Common.arrow, Common.variant])
      (by simp [CommonRigidHeadInspection.head, Common.pair, Common.arrow, Common.variant])
      (by simp [CommonRigidHeadInspection.head, Common.pair, Common.arrow, Common.variant]))).symm

def unionLeft (first last target : Child) : Branch Rows NodeIndex Child :=
  [.childBelow (.ref first) (.ref target), .childBelow (.ref last) (.ref target)]

theorem union_left_exact (rows : Rows → Row) (nodes : NodeIndex → Ty) (children : Child → Ty)
    (first last target : Child) :
    Branch.Holds rows nodes children (unionLeft first last target) ↔
      Common.Subtype (.union (children first) (children last)) (children target) := by
  simpa only [unionLeft, CommonSymbolicConstraints.holds_cons, CommonSymbolicConstraints.holds_nil,
    Check.Holds, Payload.evalLayer, and_true] using
      (Common.common_union_is_join (children first) (children last) (children target)).symm

def interRight (source first last : Child) : Branch Rows NodeIndex Child :=
  [.childBelow (.ref source) (.ref first), .childBelow (.ref source) (.ref last)]

theorem inter_right_exact (rows : Rows → Row) (nodes : NodeIndex → Ty) (children : Child → Ty)
    (source first last : Child) :
    Branch.Holds rows nodes children (interRight source first last) ↔
      Common.Subtype (children source) (.inter (children first) (children last)) := by
  simpa only [interRight, CommonSymbolicConstraints.holds_cons, CommonSymbolicConstraints.holds_nil,
    Check.Holds, Payload.evalLayer, and_true] using
      (Common.common_inter_is_meet (children first) (children last) (children source)).symm

end Yulang.CommonSymbolicRigidInspection
