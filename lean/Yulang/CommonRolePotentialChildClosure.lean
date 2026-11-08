import Yulang.CommonRoleOpenProducerAccess

/-! All-candidate finite closure for fixed structural endpoints.
This includes children of alternatives not currently selected, but does not
implement endpoint narrowing or general state-dependent materialization. -/
namespace Yulang.CommonRolePotentialChildClosure
open CommonRoleSettledSyntax CommonRoleOpenProducer
open CommonRoleOpenProducerAccess
open CommonRoleOpenDescent (Step weight)

theorem scan_hit_complete (role : Nat) (lo hi : Ty) (visible : List Declaration)
    (d : Declaration) (lp hp : Ty) (member : d ∈ visible)
    (same : d.role = role) (low : Inspect d.head lo (.hit lp))
    (high : Inspect d.head hi (.hit hp)) :
    Trial.hit d lp hp ∈ scan role lo hi visible := by
  induction visible with
  | nil => cases member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with equal | member
    · subst first
      have observed : trial role lo hi d = some (.hit d lp hp) := by
        simp [trial, same, (inspect_exact ..).mpr low, (inspect_exact ..).mpr high, encode]
      simp [scan, observed]
    · exact List.mem_append_right _ (ih member)

def next (visible : List Declaration) (q : Request) : List Request :=
  (hits (scan q.role q.lower q.upper visible)).flatMap
    (fun hit => children q hit.1 hit.2.1 hit.2.2)

theorem mem_next (visible : List Declaration) (q child : Request) :
    child ∈ next visible q ↔ Step visible child q := by
  constructor
  · intro member
    obtain ⟨⟨d, lp, hp⟩, hit, requirement⟩ := List.mem_flatMap.mp member
    obtain ⟨present, same, low, high⟩ := scan_hit_origin _ _ _ _ d lp hp
      ((mem_hits _ d lp hp).mp hit)
    obtain ⟨r, required, equal⟩ := List.mem_map.mp requirement
    subst child
    exact .requirement present same low high required
  · intro edge
    cases edge with
    | @requirement d lp hp r parent present same low high required =>
      apply List.mem_flatMap.mpr
      exact ⟨(d, lp, hp), (mem_hits _ d lp hp).mpr
        (scan_hit_complete _ _ _ _ d lp hp present same low high),
        List.mem_map.mpr ⟨r, required, rfl⟩⟩

def closure (registry : Registry) (q : Request) : List Request :=
  q :: (next registry.declarations q).attach.flatMap (fun child => closure registry child.val)
termination_by weight q
decreasing_by
  exact CommonRoleOpenDescent.step_decreases _ registry.checked child.val q
    ((mem_next _ q child.val).mp child.property)

inductive Reach (registry : Registry) : Request → Request → Prop where
  | refl : Reach registry q q
  | step : Step registry.declarations child q →
      Reach registry child target → Reach registry q target

theorem closure_complete (registry : Registry) (q target : Request)
    (reachable : Reach registry q target) : target ∈ closure registry q := by
  induction reachable with
  | refl => rw [closure]; exact List.mem_cons_self
  | @step child q target edge _ ih =>
    rw [closure]
    apply List.mem_cons_of_mem
    exact List.mem_flatMap.mpr ⟨⟨child, (mem_next _ q child).mpr edge⟩,
      List.mem_attach _ _, ih⟩

theorem closure_sound (registry : Registry) (q target : Request)
    (member : target ∈ closure registry q) : Reach registry q target := by
  have all : ∀ measure, ∀ q : Request, weight q = measure →
      ∀ target, target ∈ closure registry q → Reach registry q target := by
    intro measure
    induction measure using Nat.strongRecOn with
    | ind measure ih =>
      intro q size target member
      rw [closure] at member
      rcases List.mem_cons.mp member with same | below
      · subst target; exact .refl
      · obtain ⟨child, _, member⟩ := List.mem_flatMap.mp below
        have edge := (mem_next _ q child.val).mp child.property
        exact .step edge (ih _ (by rw [← size]; exact
          CommonRoleOpenDescent.step_decreases _ registry.checked child.val q edge)
          child.val rfl target member)
  exact all _ q rfl target member

theorem closure_exact (registry : Registry) (q target : Request) :
    target ∈ closure registry q ↔ Reach registry q target :=
  ⟨closure_sound registry q target, closure_complete registry q target⟩

theorem reach_trans (registry : Registry) (q middle target : Request)
    (first : Reach registry q middle) (second : Reach registry middle target) :
    Reach registry q target := by
  induction first with
  | refl => exact second
  | step edge _ ih => exact .step edge (ih second)

theorem filtered_child_step (registry : Registry) (visible : List Declaration)
    (subset : ∀ d ∈ visible, d ∈ registry.declarations) (q child : Request)
    (edge : CommonRoleOutermostResolver.Child (Local visible) child q) :
    Step registry.declarations child q := by
  have step := child_step visible q child edge
  cases step with
  | requirement member same low high required =>
    exact .requirement (subset _ member) same low high required

/-- Filtering candidates can activate any alternative; its child still lies
in the original finite potential closure. Endpoints remain structural. -/
theorem filtered_children_closed (registry : Registry) (visible : List Declaration)
    (subset : ∀ d ∈ visible, d ∈ registry.declarations) (root q child : Request)
    (member : q ∈ closure registry root)
    (edge : CommonRoleOutermostResolver.Child (Local visible) child q) :
    child ∈ closure registry root := by
  apply closure_complete
  exact reach_trans registry root q child (closure_sound registry root q member)
    (.step (filtered_child_step registry visible subset q child edge) .refl)

end Yulang.CommonRolePotentialChildClosure
