import Yulang.GeneralDeclarativeWitnessOpenSpine359
import Yulang.GeneralDeclarativeWitnessRecordWidthFixture359

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessOpenFixture359
open GeneralDeclarativeWitnessOpenSpine359 (Read Head Path check check_exact sem interval_of_open_heads)
open GeneralDeclarativeWitnessAuthoredProjection358 (Source)
open GeneralDeclarativeHead320 (Equation State Models)
open GeneralDeclarativeWhere319 (Capture)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeExactDelete337 (subtract)
open CommonNominalFullCarrier (Equivalent Subtype subtype_refl exactEmpty)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open GeneralDeclarativeBounds319 (Bound)
open GeneralDeclarativeWitnessRecordWindowFixture358 (strict_original_payload_bounds)

-- These are the actual retained C338 fixture equations, not generated from
-- the proposed path receipt. Keep its original source and interval names.
def c338source : Source := ⟨[GeneralDeclarativeCompoundOpenFixture338.lhs,
  GeneralDeclarativeCompoundOpenFixture338.rhs,GeneralDeclarativeCompoundOpenFixture338.scalar]⟩
def c338head : Head := ⟨7,.variable 3,[],4,.stop⟩

theorem actual_open_checks :
    check c338source GeneralDeclarativeCompoundOpenFixture338.s 0 c338head.path = true ∧
    check c338source GeneralDeclarativeCompoundOpenFixture338.s 2 c338head.path = true := by decide +kernel

theorem actual_open_without_tail_equation :
    (∀ code : Expr, (⟨4,code⟩ : Equation) ∉ c338source.authored) ∧
    Equivalent (subtract [7] (GeneralDeclarativeCompoundOpenFixture338.model 1).1) exactEmpty := by
  constructor
  · intro e seen
    change (⟨4,e⟩ : Equation) ∈ [GeneralDeclarativeCompoundOpenFixture338.lhs,
      GeneralDeclarativeCompoundOpenFixture338.rhs,GeneralDeclarativeCompoundOpenFixture338.scalar] at seen
    simp only [List.mem_cons,List.not_mem_nil,or_false] at seen
    rcases seen with impossible|impossible|impossible <;> cases impossible
  · exact eqv_refl _

theorem actual_c338_receipt_in_every_model (m)
    (fit : Models GeneralDeclarativeCompoundOpenFixture338.s m) :
    let arg := GeneralDeclarativeCompoundOpenFixture338.a
    Subtype (subtract [7] (m arg.lower).1) (subtract [7] (m arg.center).1) ∧
      Subtype (subtract [7] (m arg.center).1) (subtract [7] (m arg.upper).1) := by
  dsimp
  exact ⟨GeneralDeclarativeExactDelete337.monotone _ (fit.1.2 _ List.mem_cons_self),
    GeneralDeclarativeExactDelete337.monotone _ (fit.1.2 _ (List.mem_cons_of_mem _ List.mem_cons_self))⟩

def capture : Capture := ⟨60,61,62⟩
def low : Head := ⟨7,.variable 1,[(9,.variable 1)],0,.stop⟩
def high : Head := ⟨7,.variable 2,[(9,.variable 2)],3,.stop⟩

def lowAuthored : Equation := ⟨60,.record 7 (.variable 1) (.record 9 (.variable 1) (.variable 0))⟩
def highAuthored : Equation := ⟨62,.record 7 (.variable 2) (.record 9 (.variable 2) (.variable 3))⟩
def authored : Source := ⟨[lowAuthored,highAuthored]⟩
def current : State := ⟨⟨[],[(60,61),(61,62)]⟩,authored.authored⟩

open GeneralDeclarativeWitnessRecordWidthFixture359
  (model lowRest highRest endpoints_ordered rests_not_reversible)

theorem model_fits (pickUpper : Bool) : Models current (model pickUpper) := by
  refine ⟨⟨fun _ bad => False.elim (List.not_mem_nil bad),?_⟩,?_⟩
  · intro pair found
    simp only [current,List.mem_cons,List.not_mem_nil,or_false] at found
    rcases found with rfl|rfl <;> cases pickUpper
    · exact subtype_refl _
    · exact endpoints_ordered
    · exact endpoints_ordered
    · exact subtype_refl _
  · intro row member
    simp only [current,authored,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl <;> exact eqv_refl _

theorem reads_both_independent_inline_heads :
    check authored current capture.lower low.path = true ∧ check authored current capture.upper high.path = true := by
  decide +kernel
theorem current_without_tail_or_center_shapes :
    ∀ row ∈ current.equations,row.left ≠ 0 ∧ row.left ≠ 3 ∧ row.left ≠ 61 := by
  intro row member
  simp only [current,authored,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl <;> decide +kernel

def falseNamedSplit : Path := .chunk [(7,.variable 1)] 63 (.chunk [(9,.variable 1)] 0 .stop)
theorem equivalent_named_reassociation_not_authored :
    check authored current capture.lower falseNamedSplit = false := by decide +kernel

theorem actual_strict_inline_window (pickUpper : Bool) :
    Models current (model pickUpper) ∧
    Subtype ((model pickUpper 1).1) ((model pickUpper 2).1) ∧
    ¬Subtype ((model pickUpper 2).1) ((model pickUpper 1).1) ∧
    Subtype lowRest (subtract [7] (model pickUpper capture.center).1) ∧
    Subtype (subtract [7] (model pickUpper capture.center).1) highRest := by
  have fit := model_fits pickUpper
  have lo : Bound current.normal 60 61 := .interval List.mem_cons_self
  have hi : Bound current.normal 61 62 := .interval (List.mem_cons_of_mem _ List.mem_cons_self)
  obtain ⟨fields,projection⟩ := interval_of_open_heads (check_exact.mp reads_both_independent_inline_heads.1)
    (check_exact.mp reads_both_independent_inline_heads.2) rfl lo hi _ fit
  exact ⟨fit,fields,strict_original_payload_bounds,(projection [7]).2.2⟩

theorem inline_actual_remainder_does_not_follow_from_endpoints :
    ¬Equivalent (subtract [7] (model false capture.center).1) (subtract [7] (model true capture.center).1) :=
  fun same => rests_not_reversible same.2

end Yulang.GeneralDeclarativeWitnessOpenFixture359
