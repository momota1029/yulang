import Yulang.GeneralDeclarativeNormalized320
import Yulang.CommonNominalFullModelMap
import Yulang.CommonBoundCoalescing

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 3200000
namespace Yulang.GeneralDeclarativeRepeat320
open CommonNominalFullCarrier (Ty Subtype Equivalent subtype_refl)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeHead320 (State Models Read read_sound)
open GeneralDeclarativeDemand320 (Bounds bounds_sound)
open GeneralDeclarativeBounds319 (Bound)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans eqv_symm eqv_refl)

abbrev int : Ty := .base .int
abbrev left : Capture := ⟨0,1,3⟩
abbrev right : Capture := ⟨0,2,3⟩

/-- The two arguments have exactly the same lower and upper logical names.
Their actual centers are not equated by the interval facts. -/
def weak : State := ⟨⟨[],[(0,1),(1,3),(0,2),(2,3)]⟩,
  [⟨0,.primitive (.scalar .int) []⟩]⟩

def model (different : Bool) : Assignment := fun n =>
  (if n = 3 ∨ (different = true ∧ n = 2) then .top else int,Common.rowEmpty)

theorem int_top : Subtype int .top :=
  (CommonNominalFullModelMap.subtype_exact _ _).mpr (CommonBoundCoalescing.le_top (.base .int))

theorem top_not_int : ¬ Subtype (.top : Ty) int := by
  intro reverse
  let env : CommonNominalFullDemand.Environment Common.Row := ⟨fun _ => .bottom,fun _ => [.base .int]⟩
  exact (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (reverse 0) 0 env (.role 0)
    (List.mem_cons_self)

theorem fits (different : Bool) : Models weak (model different) := by
  refine ⟨⟨PresenceNormalForm.all_nil _ _,?_⟩,?_⟩
  · intro pair used
    change pair ∈ [(0,1),(1,3),(0,2),(2,3)] at used
    simp only [List.mem_cons,List.not_mem_nil,or_false] at used
    cases different <;> rcases used with rfl|rfl|rfl|rfl
    all_goals first | exact int_top | exact subtype_refl _
  · intro item used
    have exactEq := List.mem_singleton.mp used
    subst item
    cases different <;> exact eqv_refl _

theorem endpoints_compatible :
    left.lower = right.lower ∧ left.upper = right.upper ∧
    Bounds weak left ∧ Bounds weak right ∧
    Bound weak.normal left.lower right.upper ∧ Bound weak.normal right.lower left.upper := by
  have a : Bounds weak left := ⟨.interval (by decide +kernel),.interval (by decide +kernel)⟩
  have b : Bounds weak right := ⟨.interval (by decide +kernel),.interval (by decide +kernel)⟩
  exact ⟨rfl,rfl,a,b,.trans a.1 a.2,.trans b.1 b.2⟩

theorem known_lower (m : Assignment) (valid : Models weak m) :
    Equivalent (m left.lower).1 int := valid.2 _ (List.mem_cons_self)

theorem feasible_shared :
    ∃ m, Models weak m ∧ ∃ capture : Ty,
      Equivalent (m left.center).1 capture ∧ Equivalent (m right.center).1 capture :=
  ⟨model false,fits false,int,eqv_refl _,eqv_refl _⟩

/-- Exact obstruction to replacing shared actual capture by endpoint
compatibility and existence of a feasible assignment. This does not assert
that approved Classify selects this input. -/
theorem realization_not_universal :
    ¬ ∀ m, Models weak m → ∃ capture : Ty,
      Equivalent (m left.center).1 capture ∧ Equivalent (m right.center).1 capture := by
  intro all
  obtain ⟨capture,a,b⟩ := all (model true) (fits true)
  exact top_not_int (eqv_trans b (eqv_symm a)).1

theorem no_shared_read :
    ¬ ∃ capture : Nat → Capture,
       Read weak capture .actual left.center (.variable 7) ∧
       Read weak capture .actual right.center (.variable 7) := by
  rintro ⟨capture,l,r⟩
  apply realization_not_universal
  intro m valid
  exact ⟨_,read_sound l m valid,read_sound r m valid⟩

end Yulang.GeneralDeclarativeRepeat320
