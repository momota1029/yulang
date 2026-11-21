import Yulang.GeneralDeclarativeOpaquePair328
import Yulang.GeneralDeclarativePairNames326

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeOpaqueNames328
open GeneralDeclarativeHead320 (State Equation Models environment)
open GeneralDeclarativeDemand320 (Bounds bounds_sound)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativePairCenters326 (pair)
open GeneralDeclarativeEntailment320 (Entails Holds appendFacts model_append)
open GeneralDeclarativeFootprint321 (stateNames preserves_models)
open GeneralDeclarativeNewNames321 (after before_after)
open GeneralDeclarativeOpaqueChannel328 (project)
open GeneralDeclarativeEqualities322 (Derives)
open GeneralNominalCenteredHeadMatExpressions (Expr value)
open CommonNominalFullCarrier (Ty Subtype Equivalent subtype_trans common_pair_iff)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl eqv_symm eqv_trans)

def kept (s : State) (root : Nat) (protect : List Nat) : List Nat :=
  stateNames s ++ root :: protect

def first (s : State) (root : Nat) (protect : List Nat) : Nat := after (kept s root protect)
def second (s : State) (root : Nat) (protect : List Nat) : Nat := first s root protect + 1

def row (s : State) (root : Nat) (protect : List Nat) : Equation :=
  ⟨root,pair (.variable (first s root protect)) (.variable (second s root protect))⟩

def expose (s : State) (root : Nat) (protect : List Nat) : State :=
  appendFacts s [row s root protect]

def extend (s : State) (root : Nat) (protect : List Nat) (m : Assignment) (l r : Ty) : Assignment :=
  fun n => if n = first s root protect then (l,(m n).2)
    else if n = second s root protect then (r,(m n).2) else m n

theorem unchanged {s : State} {root : Nat} {protect : List Nat} (m : Assignment) (l r : Ty)
    (old : n ∈ kept s root protect) : extend s root protect m l r n = m n := by
  have earlier : n < first s root protect := before_after old
  have beforeSecond : n ≠ second s root protect := by unfold second; omega
  simp [extend,Nat.ne_of_lt earlier,beforeSecond]

theorem unchanged_root (s : State) (root : Nat) (protect : List Nat) (m : Assignment) (l r : Ty) :
    extend s root protect m l r root = m root :=
  unchanged m l r (List.mem_append_right _ List.mem_cons_self)

theorem left_value (s : State) (root : Nat) (protect : List Nat) (m : Assignment) (l r : Ty) :
    (extend s root protect m l r (first s root protect)).1 = l := by simp [extend]

theorem right_value (s : State) (root : Nat) (protect : List Nat) (m : Assignment) (l r : Ty) :
    (extend s root protect m l r (second s root protect)).1 = r := by
  have different : second s root protect ≠ first s root protect := by unfold second; omega
  simp [extend,different]

theorem spelling (s : State) (root : Nat) (protect : List Nat) :
    Derives (expose s root protect) (.variable root)
      (pair (.variable (first s root protect)) (.variable (second s root protect))) :=
  .row (List.mem_append_right _ List.mem_cons_self)

theorem model_extension {s : State} (root : Nat) (protect : List Nat) (m : Assignment)
    (old : Models s m) (paired : Equivalent (m root).1 (CommonNominalFullCarrier.pair l r)) :
    Models (expose s root protect) (extend s root protect m l r) ∧
      ∀ n ∈ kept s root protect, extend s root protect m l r n = m n := by
  let a := extend s root protect m l r
  have keptNames : ∀ n ∈ kept s root protect, a n = m n := fun _ h => unchanged m l r h
  refine ⟨(model_append a).mpr ⟨(preserves_models s
    (fun n before => keptNames n (List.mem_append_left _ before))).mpr old,?_⟩,keptNames⟩
  intro known added
  cases List.mem_singleton.mp added
  change Equivalent (a root).1 (CommonNominalFullCarrier.pair (a (first s root protect)).1
    (a (second s root protect)).1)
  dsimp only [a]
  rw [unchanged_root s root protect m l r,left_value,right_value]
  exact paired

/-- An arbitrary actual argument between two ordinary known pair ends
can be named conservatively in the existing declarative language:
two fresh names, one pair equation, and no new expression operator. -/
theorem conservative {s : State} {arg : Capture}
    (bounds : Bounds s arg)
    (lower : Entails s ⟨arg.lower,pair lowA lowB⟩)
    (upper : Entails s ⟨arg.upper,pair highA highB⟩)
    (protect : List Nat) (m : Assignment) :
    Models s m ↔ ∃ next, Models (expose s arg.center protect) next ∧
      ∀ n ∈ kept s arg.center protect, next n = m n := by
  constructor
  · intro current
    have low := lower m current
    have high := upper m current
    have between := bounds_sound bounds m current
    have lowerActual := subtype_trans low.2 between.1
    have upperActual := subtype_trans between.2 high.1
    obtain ⟨a,b,_,_,eq⟩ := GeneralDeclarativeOpaquePair328.reconstruction _ _ _ _ _
      lowerActual upperActual
    exact ⟨_,model_extension arg.center protect m current eq⟩
  · rintro ⟨next,valid,unchanged⟩
    exact (preserves_models s (fun n used => unchanged n (List.mem_append_left _ used))).mp
      ((model_append next).mp valid).1

end Yulang.GeneralDeclarativeOpaqueNames328
