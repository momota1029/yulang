import Yulang.CommonBoundCoalescing

/-!
# Pulling the bounds of one requested variable

The reference lower-bound collector starts a forward search at every lower
seed. The collector here starts one reverse worklist at the requested variable.
Only predecessors of that request are visited; cycles use the existing finite
visited-set algorithm. The upper collector starts one forward worklist at the
requested variable. Neither computation calls a solver or constructs all-node
bounds. The finite variable count is an internal capacity, not caller fuel.

The exactness theorems preserve the original bound list, including order and
duplicates. They hold for every finite template, even an inconsistent one.
They concern a fixed constraint snapshot. Rigid decomposition can add edges;
querying an earlier snapshot is not a claim about a later saturated snapshot.
-/

namespace Yulang.DemandBoundPropagation

open LayerBoundTemplates (Constraint Problem)

universe u
variable {n : Nat} {Bound : Type u}

/-- Edges followed while pulling a lower bound: the reverse of value flow. -/
def predecessors (problem : Problem n Bound) (target : Fin n) : List (Fin n) :=
  problem.filterMap fun
    | .flow source finish => if finish = target then some source else none
    | _ => none

theorem mem_predecessors (problem : Problem n Bound) (source target : Fin n) :
    source ∈ predecessors problem target ↔ .flow source target ∈ problem := by
  simp only [predecessors, List.mem_filterMap]
  constructor
  · rintro ⟨constraint, member, found⟩
    cases constraint with
    | flow start finish =>
        change (if finish = target then some start else none) = some source at found
        split at found
        · rename_i equal
          subst finish
          have equal : start = source := Option.some.inj found
          subst start
          exact member
        · cases found
    | _ => cases found
  · intro member
    exact ⟨.flow source target, member, by simp⟩

theorem mem_successors (problem : Problem n Bound) (source target : Fin n) :
    target ∈ LayerBoundTemplates.successors problem source ↔ .flow source target ∈ problem := by
  simp only [LayerBoundTemplates.successors, List.mem_filterMap]
  constructor
  · rintro ⟨constraint, member, found⟩
    cases constraint with
    | flow start finish =>
        change (if start = source then some finish else none) = some target at found
        split at found
        · rename_i equal
          subst start
          have equal : finish = target := Option.some.inj found
          subst finish
          exact member
        · cases found
    | _ => cases found
  · intro member
    exact ⟨.flow source target, member, by simp⟩

theorem reverse_path (problem : Problem n Bound) (source target : Fin n) :
    FiniteWorklist.Path (predecessors problem) target source ↔
      LayerBoundTemplates.Reaches problem source target := by
  constructor
  · intro path
    induction path with
    | nil => exact .nil _
    | @cons first middle last edge rest ih =>
        exact ih.append (.cons
          ((mem_successors problem middle first).mpr
            ((mem_predecessors problem middle first).mp edge)) (.nil first))
  · intro path
    induction path with
    | nil => exact .nil _
    | @cons first middle last edge rest ih =>
        exact ih.append (.cons
          ((mem_predecessors problem first middle).mpr
            ((mem_successors problem first middle).mp edge)) (.nil first))

/-- The only vertices visited for a lower-bound request at `target`. -/
def ancestors (problem : Problem n Bound) (target : Fin n) : List (Fin n) :=
  FiniteWorklist.reachable (predecessors problem) n target

theorem ancestors_exact (problem : Problem n Bound) (source target : Fin n) :
    source ∈ ancestors problem target ↔ LayerBoundTemplates.Reaches problem source target := by
  unfold ancestors
  rw [FiniteWorklist.reachable_exact (predecessors problem) n (List.finRange n)
    (by intro vertex; simp) (by simp)]
  exact reverse_path problem source target

theorem ancestors_eq_reachable (problem : Problem n Bound) (source target : Fin n) :
    source ∈ ancestors problem target ↔ target ∈ LayerBoundTemplates.reachable problem source := by
  rw [ancestors_exact, LayerBoundTemplates.reachable_exact]

/-- Pull exactly the lower contributions of one variable. Filtering retains
the reference order of seeds; it does not launch searches at unrelated seeds. -/
def lowerBounds (problem : Problem n Bound) (target : Fin n) : List Bound :=
  let visited := ancestors problem target
  (LayerBoundTemplates.lowerSeeds problem).filterMap fun entry =>
    if entry.2 ∈ visited then some entry.1 else none

/-- Pull upper contributions with one forward search from the requested node. -/
def upperBounds (problem : Problem n Bound) (source : Fin n) : List Bound :=
  let visited := LayerBoundTemplates.reachable problem source
  (LayerBoundTemplates.upperSeeds problem).filterMap fun entry =>
    if entry.1 ∈ visited then some entry.2 else none

theorem lowerBounds_exact (problem : Problem n Bound) (target : Fin n) :
    lowerBounds problem target = LayerBoundTemplates.lowerBounds problem target := by
  simp only [lowerBounds, LayerBoundTemplates.lowerBounds, ancestors_eq_reachable]

theorem upperBounds_exact (problem : Problem n Bound) (source : Fin n) :
    upperBounds problem source = LayerBoundTemplates.upperBounds problem source := rfl

/-- A request can ask either polarity without forcing the other bound. -/
inductive Direction where
  | lower
  | upper
  deriving DecidableEq, Repr

structure Root (n : Nat) where
  node : Fin n
  direction : Direction
  deriving DecidableEq, Repr

def request (problem : Problem n Bound) (root : Root n) : List Bound :=
  match root.direction with
  | .lower => lowerBounds problem root.node
  | .upper => upperBounds problem root.node

/-- The reference observation of a root, before rigid decomposition. -/
def reference (problem : Problem n Bound) (root : Root n) : List Bound :=
  match root.direction with
  | .lower => LayerBoundTemplates.lowerBounds problem root.node
  | .upper => LayerBoundTemplates.upperBounds problem root.node

/-- Every finite template and every requested variable/polarity; no support,
success, model, closed cache or externally chosen fuel is assumed. -/
theorem request_exact (problem : Problem n Bound) (root : Root n) :
    request problem root = reference problem root := by
  cases root with
  | mk node direction =>
      cases direction
      · exact lowerBounds_exact problem node
      · exact upperBounds_exact problem node

def lower (evaluate : Bound → Common.Ty) (problem : Problem n Bound)
    (target : Fin n) : Common.Ty :=
  CommonBoundCoalescing.joinTypes ((lowerBounds problem target).map evaluate)

def upper (evaluate : Bound → Common.Ty) (problem : Problem n Bound)
    (source : Fin n) : Common.Ty :=
  CommonBoundCoalescing.meetTypes ((upperBounds problem source).map evaluate)

/-- The bounds agree as Common types, not merely after one finite observation. -/
theorem lower_exact (evaluate : Bound → Common.Ty) (problem : Problem n Bound) (target : Fin n) :
    lower evaluate problem target = CommonBoundCoalescing.lower evaluate problem target := by
  simp only [lower, CommonBoundCoalescing.lower, lowerBounds_exact]

theorem upper_exact (evaluate : Bound → Common.Ty) (problem : Problem n Bound) (source : Fin n) :
    upper evaluate problem source = CommonBoundCoalescing.upper evaluate problem source := by
  simp only [upper, CommonBoundCoalescing.upper, upperBounds_exact]

end Yulang.DemandBoundPropagation
