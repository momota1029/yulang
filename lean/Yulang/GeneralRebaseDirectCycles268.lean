import Yulang.GeneralNominalCycleK2
import Yulang.FiniteWorklist

namespace Yulang.GeneralRebaseDirectCycles268
open GeneralNominalState (State Parameter)
open GeneralNominalCycleK2 (DirectArgument DirectEdge DirectPath DirectCycle)
open FiniteWorklist (Path reachable)

def pointTarget : Parameter n → List (Fin n)
 | .type (a,b) => if a = b then [a] else []
 | .row _ => []

theorem pointTarget_exact (parameter : Parameter n) (target : Fin n) :
 target ∈ pointTarget parameter ↔ parameter = .type (target,target) := by
 cases parameter with
 | row _ => simp [pointTarget]
 | type pair =>
   rcases pair with ⟨a,b⟩
   by_cases same : a = b
   · subst b; simp [pointTarget,eq_comm]
   · simp only [pointTarget,ite_eq_right same,List.not_mem_nil,false_iff]
     intro h
     cases h
     exact same rfl

def points (state : State) (parent : Fin state.base.slots) : List (Fin state.base.slots) :=
 match state.nominals parent with
 | none => []
 | some descriptor => descriptor.arguments.flatMap pointTarget

theorem points_exact (state : State) (parent target : Fin state.base.slots) :
 target ∈ points state parent ↔ DirectArgument state parent target := by
 cases recorded : state.nominals parent with
 | none => simp [points,recorded,DirectArgument]
 | some descriptor =>
   simp only [points,recorded,List.mem_flatMap,DirectArgument,Option.some.injEq]
   constructor
   · rintro ⟨parameter,listed,included⟩
     cases (pointTarget_exact parameter target).mp included
     exact ⟨descriptor,rfl,List.mem_iff_getElem?.mp listed⟩
   · rintro ⟨found,rfl,index,loc⟩
     exact ⟨_,List.mem_iff_getElem?.mpr ⟨index,loc⟩,(pointTarget_exact _ _).mpr rfl⟩

def adj (state : State) (parent : Fin state.base.slots) : List (Fin state.base.slots) :=
 CommonRoleRegularGraph.successors state.view.graph parent ++ points state parent

theorem adj_exact (state : State) (parent target : Fin state.base.slots) :
 target ∈ adj state parent ↔ DirectEdge state parent target := by
 simp only [adj,DirectEdge,List.mem_append,←GeneralSourceK2.child_graph_iff,points_exact]

theorem path_exact (state : State) (first last : Fin state.base.slots) :
 Path (adj state) first last ↔ DirectPath state first last := by
 constructor <;> intro path
 · induction path with
   | nil _ => exact .nil _
   | cons e _ ih => exact .cons ((adj_exact ..).mp e) ih
 · induction path with
   | nil _ => exact .nil _
   | cons e _ ih => exact .cons ((adj_exact ..).mpr e) ih

def cycle (state : State) (root : Fin state.base.slots) : Bool :=
 (adj state root).any fun child => decide (root ∈ reachable (adj state) state.base.slots child)

theorem cycle_exact (state : State) (root : Fin state.base.slots) :
 cycle state root = true ↔ DirectCycle state root := by
 have reachable_exact (child : Fin state.base.slots) :
   root ∈ reachable (adj state) state.base.slots child ↔ DirectPath state child root :=
   (FiniteWorklist.reachable_exact (adj state) state.base.slots (List.finRange state.base.slots)
     (by simp) (by simp) child root).trans (path_exact state child root)
 simp only [cycle,List.any_eq_true,decide_eq_true_eq,adj_exact,reachable_exact,DirectCycle]

end Yulang.GeneralRebaseDirectCycles268
