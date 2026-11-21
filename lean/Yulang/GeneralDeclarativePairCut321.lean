import Yulang.GeneralDeclarativeEndpointProbe321
import Yulang.GeneralDeclarativeRepeat320
import Yulang.GeneralDeclarationExamples

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativePairCut321
open CommonNominalFullCarrier (Ty pair Equivalent subtype_refl)
open CommonNominalFullCarrier (common_pair_iff)
open GeneralDeclarativeRepeat320 (int int_top top_not_int)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeEndpointProbe321 (Matches)
open GeneralDeclarativeTrace321 (Trace Occurrence)
open GeneralDeclarativeLowerKnown321 (alias_refl)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)

def pairCode (first second : Nat) : Expr := .primitive .pair [.variable first,.variable second]
abbrev arg : Capture := ⟨0,1,2⟩
def state : State := ⟨⟨[],[(0,1),(1,2)]⟩,
    [⟨0,pairCode 3 3⟩,⟨2,pairCode 4 4⟩,⟨3,.primitive (.scalar .int) []⟩]⟩
def interp : Interpretation := ⟨fun n => if n = 5 then some .pair else none,fun _ => false,fun _ bad => by cases bad⟩

def assignment (unequal : Bool) : Assignment := fun n =>
  ((if n = 0 then pair int int else if n = 1 then pair int (if unequal then .top else int)
    else if n = 2 then pair .top .top else if n = 4 then .top else int),Common.rowEmpty)

theorem model_fits (unequal : Bool) : Models state (assignment unequal) := by
  refine ⟨⟨PresenceNormalForm.all_nil _ _,?_⟩,?_⟩
  · intro pairNames there
    change pairNames ∈ [(0,1),(1,2)] at there
    rcases List.mem_cons.mp there with rfl|tail
    · cases unequal
      · exact subtype_refl _
      · exact (common_pair_iff ..).mpr ⟨subtype_refl _,int_top⟩
    · cases List.mem_singleton.mp tail
      cases unequal
      · exact (common_pair_iff ..).mpr ⟨int_top,int_top⟩
      · exact (common_pair_iff ..).mpr ⟨int_top,subtype_refl _⟩
  · intro row there
    change row ∈ ([⟨0,pairCode 3 3⟩,⟨2,pairCode 4 4⟩,⟨3,.primitive (.scalar .int) []⟩] : List Equation) at there
    simp only [List.mem_cons,List.not_mem_nil,or_false] at there
    rcases there with rfl|rfl|rfl <;> exact eqv_refl _

theorem endpoints_match :
    Matches state GeneralDeclarationExamples.constructors interp arg (.app 5 [.var 0,.var 0]) := by
  have span : Bounds state arg := ⟨.interval List.mem_cons_self,
    .interval (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  refine ⟨span,pairCode 0 0,[⟨0,.lower,3⟩,⟨0,.lower,3⟩],[⟨0,.upper,4⟩,⟨0,.upper,4⟩],rfl,?_,?_⟩
  · exact .primitive (args := [3,3]) (alias_refl _) List.mem_cons_self (.cons .capture (.cons .capture .nil))
  · exact .primitive (args := [4,4]) (alias_refl _) (List.mem_cons_of_mem _ List.mem_cons_self)
      (.cons .capture (.cons .capture .nil))

theorem diagonal_center_fails : ¬ ∃ chosen : Ty,
    Equivalent ((assignment true) arg.center).1 (pair chosen chosen) := by
  rintro ⟨chosen,forward,backward⟩
  have one := (common_pair_iff int .top chosen chosen).mp forward
  have two := (common_pair_iff chosen chosen int .top).mp backward
  exact top_not_int (CommonNominalFullCarrier.subtype_trans one.2 two.1)

/-- An actual compiled covariant constructor has the same repeated binder
in both endpoint walks, but the ordinary state still has a non-diagonal
actual pair model. This only refutes endpoint-only adequacy. -/
theorem probe_not_enough :
    Matches state GeneralDeclarationExamples.constructors interp arg (.app 5 [.var 0,.var 0]) ∧
    (∃ m, Models state m ∧ ∃ chosen : Ty, Equivalent (m arg.center).1 (pair chosen chosen)) ∧
    ∃ m, Models state m ∧ ¬∃ chosen : Ty, Equivalent (m arg.center).1 (pair chosen chosen) :=
  ⟨endpoints_match, ⟨assignment false,model_fits false,int,eqv_refl _⟩,
    ⟨assignment true,model_fits true,diagonal_center_fails⟩⟩

end Yulang.GeneralDeclarativePairCut321
