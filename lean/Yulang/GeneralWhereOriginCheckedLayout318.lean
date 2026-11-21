import Yulang.GeneralWhereOriginLayout318
import Yulang.GeneralWhereOriginFixture318

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 25000
set_option maxHeartbeats 12000000
namespace Yulang.GeneralWhereOriginCheckedLayout318
open GeneralWhereOriginFixture318 (lowerCell upperCell initial_trace)
open GeneralLiveCompoundPostFrames316 (rootPlan)
open GeneralLiveCompoundRegistry316 (sourceRegistry otherChild)
open GeneralLiveCompoundPost316 (raw)
open GeneralWhereVersionSnapshot317 (snap context)
open GeneralWhereVersionBase317 (source_old source_lo source_hi loSlot hiSlot lower_fresh upper_fresh new_cases)
open GeneralWhereVersionCase317 (expr lower upper)
open GeneralWhereOriginLayout318 (matchSlots check_spec mem_fresh)
open GeneralWhereOriginDelta318 (Cell)
open GeneralWhereOriginTrace318 (Trace)
open GeneralWhereVersionInstall317 (fixed)

theorem only_cells (c : Cell rootPlan) : c = lowerCell ∨ c = upperCell := by
  rcases c with ⟨clause,index,side,pattern,expression,listed,hit,good,compiled⟩
  have named : clause = otherChild := List.mem_singleton.mp listed
  subst clause
  have inRange := (List.getElem?_eq_some_iff.mp hit).1
  have i : index = 0 := by
    change index < 1 at inRange
    omega
  subst index
  have existsAt : otherChild.arguments[0]? = some (.variant 0 (.var 0)) := rfl
  have exactPat := Option.some.inj (hit.symm.trans existsAt)
  subst pattern
  have known : GeneralNominalCenteredHeadMatExpressions.translate rootPlan.packet.registry.constructors
    rootPlan.packet.context.interpretation (.variant 0 (.var 0)) = some expr := rfl
  have exactExpr := Option.some.inj (compiled.symm.trans known)
  subst expression
  cases side
  · exact .inl rfl
  · exact .inr rfl

/-- The actual C317 allocated layout passes the finite source-ID
checker tied to its checked compiler, not a handpicked provenance table. -/
theorem validates : matchSlots raw snap rootPlan = true := by
  apply (check_spec rootPlan).mpr
  constructor
  · intro c _
    rcases only_cells c with rfl|rfl
    · exact ⟨loSlot,source_lo⟩
    · exact ⟨hiSlot,source_hi⟩
  · intro i
    refine Fin.addCases (m := 8) (n := 2) ?_ ?_ i
    · intro j
      exact Or.inl ⟨j,source_old j⟩
    · intro j
      rcases new_cases j with rfl|rfl
      · exact Or.inr ⟨lowerCell,(mem_fresh lowerCell).mpr lower_fresh,source_lo⟩
      · exact Or.inr ⟨upperCell,(mem_fresh upperCell).mpr upper_fresh,source_hi⟩

theorem enumerated_trace : Trace sourceRegistry fixed :=
  .placed context rootPlan initial_trace GeneralWhereVersionInstall317.step
    (GeneralWhereOriginLayout318.checkedDelta GeneralWhereVersionRefine317.refines rfl validates)

end Yulang.GeneralWhereOriginCheckedLayout318
