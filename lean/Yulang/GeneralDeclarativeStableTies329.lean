import Yulang.GeneralDeclarativeOpaqueShared328
import Yulang.GeneralDeclarativeEntailment320

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeStableTies329
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeEntailment320 (Entails Holds appendFacts model_append)
open GeneralDeclarativeOpaqueGroup328 (Sharing)
open GeneralDeclarativeOpaqueNested328 (occurrences)
open GeneralDeclarativeTermWalk322 (Binds)
open GeneralDeclarativeEqualities322 (Derives)
open CommonNominalFullCarrier (Equivalent)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl eqv_symm eqv_trans)

abbrev Use := Nat × Nat
def pairOf (p : Nat × Capture) : Use := (p.1,p.2.center)

def row (selected : Nat → Capture) (u : Use) : Equation :=
  ⟨(selected u.1).center,.variable u.2⟩

/-- The selected representative is supplied by the actual source name
table. This star is an ordinary equality encoding, not an admission
test or a choice of the lexically smallest logical name. -/
def rows (selected : Nat → Capture) (uses : List Use) : List Equation :=
  (uses.filter fun u => u.2 != (selected u.1).center).map (row selected)

def Present (s : State) (selected : Nat → Capture) (uses : List Use) : Prop :=
  rows selected uses ⊆ s.equations

def Consequence (s : State) (selected : Nat → Capture) (uses : List Use) : Prop :=
  ∀ rowFact ∈ rows selected uses, Entails s rowFact

theorem present_entails {s : State} (h : Present s selected uses) :
    Consequence s selected uses :=
  fun _ found => GeneralDeclarativeEntailment320.literal (h found)

theorem from_use {s : State} (required : Consequence s selected uses) (listed : u ∈ uses)
    (m) (valid : Models s m) : Equivalent (m u.2).1 (m (selected u.1).center).1 := by
  by_cases same : u.2 = (selected u.1).center
  · rw [same]; exact eqv_refl _
  · have tracked : row selected u ∈ rows selected uses := by
      apply List.mem_map.mpr
      exact ⟨u,List.mem_filter.mpr ⟨listed,by simp [same]⟩,rfl⟩
    exact eqv_symm (required _ tracked m valid)

theorem as_derives {s : State} (required : Present s selected uses) (listed : u ∈ uses) :
    Derives s (.variable u.2) (.variable (selected u.1).center) := by
  by_cases same : u.2 = (selected u.1).center
  · rw [same]; exact .refl _
  · have tracked : row selected u ∈ rows selected uses := by
      apply List.mem_map.mpr
      exact ⟨u,List.mem_filter.mpr ⟨listed,by simp [same]⟩,rfl⟩
    exact .symm (.row (required tracked))

theorem model_batch {s : State} (selected : Nat → Capture) (uses : List Use) (m) :
    Models (appendFacts s (rows selected uses)) m ↔ Models s m ∧
      ∀ u ∈ uses, Equivalent (m u.2).1 (m (selected u.1).center).1 := by
  refine (model_append m).trans ⟨?_,?_⟩
  · intro ⟨old,applied⟩
    have valid := (model_append m).mpr ⟨old,applied⟩
    exact ⟨old,fun u h => from_use (present_entails
      (s := appendFacts s (rows selected uses)) (fun _ v => List.mem_append_right _ v)) h m valid⟩
  · rintro ⟨old,ties⟩
    refine ⟨old,?_⟩
    intro f ranged
    obtain ⟨u,inList,rfl⟩ := List.mem_map.mp ranged
    exact eqv_symm (ties u (List.mem_filter.mp inList).1)

theorem repeated_shares {s : State} (closed : Consequence s selected (spans.map pairOf)) :
    Sharing s spans := by
  intro m fits key a b first last
  have aa := from_use closed (List.mem_map.mpr ⟨(key,a),first,rfl⟩) m fits
  have bb := from_use closed (List.mem_map.mpr ⟨(key,b),last,rfl⟩) m fits
  exact eqv_trans aa (eqv_symm bb)

theorem repeated_binds {s : State} (closed : Present s selected (spans.map pairOf)) :
    Binds s selected (occurrences spans) := by
  intro o inList
  obtain ⟨⟨key,a⟩,member,rfl⟩ := List.mem_map.mp inList
  exact as_derives closed (List.mem_map.mpr ⟨_,member,rfl⟩)

theorem used_after {s : State} (selected : Nat → Capture) (uses : List Use) :
    Present (appendFacts s (rows selected uses)) selected uses :=
  fun _ present => List.mem_append_right _ present

/-- The selected equations can narrow, or make inconsistent, the
current state. This does not give a new priority or pending rule. -/
theorem no_model_after {s : State}
    (forced : ∀ m, Models s m → ¬(∀ u ∈ uses,
      Equivalent (m u.2).1 (m (selected u.1).center).1)) :
    ¬∃ m, Models (appendFacts s (rows selected uses)) m := by
  rintro ⟨m,valid⟩
  exact forced m ((model_batch selected uses m).mp valid).1 ((model_batch selected uses m).mp valid).2

end Yulang.GeneralDeclarativeStableTies329
