import Yulang.GeneralDeclarativeOpaqueCapture328
import Yulang.GeneralDeclarativeAggregate324

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeOpaqueGroup328
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeOpaqueConserve328 (Retains chain refl)
open GeneralDeclarativeAggregate324 (span ready assembled aggregate_model now_bounds)
open GeneralDeclarativeGrowth327 (Extends trans ordinary restrict fits derives boundsOne)
open GeneralDeclarativeEqualities322 (Derives)
open GeneralDeclarativeMergeCenters324 (Linked)
open CommonNominalFullCarrier (Equivalent)

def group (key : Nat) (uses : List (Nat × Capture)) : List Capture :=
  uses.filterMap fun (n,arg) => if n = key then some arg else none

theorem group_exact (key : Nat) (uses : List (Nat × Capture)) {selected : Capture} :
    selected ∈ group key uses ↔ (key,selected) ∈ uses := by
  constructor
  · intro found
    obtain ⟨⟨n,arg⟩,stored,chosen⟩ := List.mem_filterMap.mp found
    by_cases eq : n = key
    · subst n
      have same : arg = selected := by simpa [eq_comm] using chosen
      subst arg
      exact stored
    · simp [eq] at chosen
  · intro found
    exact List.mem_filterMap.mpr ⟨(key,selected),found,by simp⟩

/-- Actual equality is a condition on the same model of the same
current ordinary state. Endpoint agreement cannot supply it. -/
def Sharing (s : State) (uses : List (Nat × Capture)) : Prop :=
  ∀ m, Models s m → ∀ key a b, (key,a) ∈ uses → (key,b) ∈ uses →
    Equivalent (m a.center).1 (m b.center).1

theorem linked_group {s : State} (sharing : Sharing s uses)
    (read : group key uses = seed :: rest) : Linked s seed rest := by
  intro m allowed a seen
  exact sharing m allowed key a seed ((group_exact _ _).mp (read ▸ seen))
    ((group_exact _ _).mp (read ▸ List.mem_cons_self))

theorem aggregate_grows (s : State) (extra : List Nat) (seed : Capture) (rest : List Capture) :
    Extends s (ready s extra seed rest) :=
  trans (ordinary _ _) (trans (ordinary _ _) (ordinary _ _))

theorem form_group {s : State} {seed : Capture} {rest : List Capture}
    (ranges : ∀ a ∈ seed :: rest, Bounds s a) (actual : Linked s seed rest) (keep : List Nat) :
    Retains s (ready s keep seed rest) keep := by
  refine ⟨aggregate_grows s keep seed rest,?_⟩
  intro m h
  obtain ⟨n,valid,retained⟩ := aggregate_model (extra := keep) ranges actual m h
  refine ⟨n,valid,fun k read => retained k ?_⟩
  rcases List.mem_append.mp read with former|protectedKey
  · exact List.mem_append_left _ former
  · exact List.mem_append_right _ (List.mem_append_left _ protectedKey)

theorem reading {s : State} {seed : Capture} {rest : List Capture}
    (ranges : ∀ a ∈ seed :: rest, Bounds s a) (keep : List Nat)
    (one : a ∈ seed :: rest) :
    Derives (ready s keep seed rest) (.variable a.center)
      (.variable (span s keep seed rest).center) := by
  have linked := (assembled (extra := keep) ranges).sameCenter a one
  exact .congruent (.variable (.bounds (boundsOne (ordinary _ _) linked.1)
    (boundsOne (ordinary _ _) linked.2)))

end Yulang.GeneralDeclarativeOpaqueGroup328
