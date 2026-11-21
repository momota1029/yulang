import Yulang.GeneralDeclarativeExistingLocal322
import Yulang.GeneralDeclarativeExampleSource320

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeExistingFixture322
open GeneralDeclarativeExampleSource320 (registry interp checked input point root leaf)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeDemand320 (Demand Bounds)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open CommonNominalFullCarrier (Ty pair nominal subtype_refl)

def product : Expr := .primitive .pair [.variable 16,.variable 17]
def nominalCode (arg : Expr) : Expr := .nominal 0 [arg]

abbrev equations : List Equation :=
  [⟨0,nominalCode (.variable 3)⟩,⟨1,nominalCode product⟩,⟨2,nominalCode (.variable 4)⟩,
   ⟨3,product⟩,⟨4,.variable 3⟩,⟨5,.variable 3⟩,
   ⟨8,.variable 3⟩,⟨9,.variable 4⟩,⟨10,.variable 3⟩,
   ⟨12,.variable 13⟩,⟨13,.variable 5⟩,
   ⟨6,.variable 14⟩,⟨14,nominalCode (.variable 15)⟩,⟨15,.variable 5⟩]

def state : State := ⟨⟨[],[(0,1),(1,2),(8,9),(9,10)]⟩,equations⟩

abbrev frame : Capture := ⟨8,9,10⟩
abbrev child : Demand := ⟨2,[frame],[⟨1,12⟩]⟩
def parentCapture (n : Nat) : Capture := if n = 0 then point 3 else point 5
abbrev leafCapture : Nat → Capture := fun _ => point 9

def inputOnly (n : Nat) : Prop := n ∈ ([0,2,3,4,8,9,10] : List Nat)

def supported : Supported state (fun _ => False) :=
  ⟨fun row origin => row ∈ equations ∧ origin = .source ∧ inputOnly row.left,fun h => h.1⟩

def productType : Ty := pair (.base .int) .top
def model : Assignment := fun n =>
  (if n ≤ 2 ∨ n = 6 ∨ n = 14 then nominal 0 [.inl productType]
   else if n = 16 then .base .int else if n = 17 then .top else productType, Common.rowEmpty)

theorem valid : Models state model := by
  refine ⟨⟨PresenceNormalForm.all_nil _ _,?_⟩,?_⟩
  · intro span found
    change span ∈ [(0,1),(1,2),(8,9),(9,10)] at found
    simp only [List.mem_cons,List.not_mem_nil,or_false] at found
    rcases found with rfl|rfl|rfl|rfl <;> exact subtype_refl _
  · intro eq found
    change eq ∈ equations at found
    simp only [equations,List.mem_cons,List.not_mem_nil,or_false] at found
    rcases found with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact eqv_refl _

theorem rootBounds : Bounds state input :=
  ⟨.interval List.mem_cons_self,.interval (List.mem_cons_of_mem _ List.mem_cons_self)⟩

theorem childBounds : Bounds state frame :=
  ⟨.interval (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),
    .interval (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self)))⟩

theorem pointBounds (n : Nat) : Bounds state (point n) := ⟨.refl _,.refl _⟩

end Yulang.GeneralDeclarativeExistingFixture322
