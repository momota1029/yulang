import Yulang.CommonRoleChildTemplates

/-! Computed finite source-template closure, retaining source slots across states.
Int-only/unary/capture-bearing adapter only. The enumerator overapproximates
candidate production; its exactness is reachability, not candidate selection. -/
namespace Yulang.CommonRoleSourceTemplateClosure
open CommonRoleSettledSyntax CommonRoleOpenProducer CommonRoleCaptureOrigin
open CommonRoleMaterializedDomain CommonRoleChildTemplates
open CommonRoleSettledConstraints (State)

def declarationChildren (d : Declaration) (parent : SourceRequest n) : List (SourceRequest n) :=
  match captureDepth d.head with
  | none => []
  | some depth => match extract depth parent.lower, extract depth parent.upper with
    | some lo, some hi => d.requirements.map (fun r => childTemplate r lo hi)
    | _, _ => []

/-- All structural alternatives, filtered only by a derived termination measure.
This is not the language's candidate selection procedure. -/
def next (registry : Registry) (parent : SourceRequest n) : List (SourceRequest n) :=
  (registry.declarations.flatMap (fun d => declarationChildren d parent)).filter
    (fun child => sourceWeight child < sourceWeight parent)

theorem next_decreases (registry : Registry) (child parent : SourceRequest n)
    (member : child ∈ next registry parent) : sourceWeight child < sourceWeight parent := by
  exact of_decide_eq_true (List.mem_filter.mp member).2

/-- Every observed actual child edge, at any state, is in the computed enumerator. -/
theorem generated_present (registry : Registry) (child parent : SourceRequest n)
    (edge : Generated registry child parent) : child ∈ next registry parent := by
  have decrease := generated_decreases registry child parent edge
  cases edge with
  | step parent s d lp hp depth lo hi r produced located lf hf required =>
    have hit : (d, lp, hp) ∈ hits (scan parent.role
        (parent.lower.eval s) (parent.upper.eval s) registry.declarations) := by
      unfold production at produced
      cases hs : hits (scan (parent.eval s).role (parent.eval s).lower
          (parent.eval s).upper registry.declarations) with
      | nil => simp [hs] at produced
      | cons first rest =>
        have equal : first = (d, lp, hp) := by simpa [hs] using produced
        simp only [SourceRequest.eval] at hs
        rw [hs, equal]
        exact List.mem_cons_self
    obtain ⟨member, _, _, _⟩ := CommonRoleOpenProducerAccess.scan_hit_origin
      _ _ _ _ d lp hp ((CommonRoleOpenProducerAccess.mem_hits ..).mp hit)
    apply List.mem_filter.mpr
    refine ⟨List.mem_flatMap.mpr ⟨d, member, ?_⟩, by simpa using decrease⟩
    simp only [declarationChildren, located, lf, hf]
    exact List.mem_map.mpr ⟨r, required, rfl⟩

def closure (registry : Registry) (parent : SourceRequest n) : List (SourceRequest n) :=
  parent :: (next registry parent).attach.flatMap (fun child => closure registry child.val)
termination_by sourceWeight parent
decreasing_by exact next_decreases registry child.val parent child.property

/-- Independent path judgment over computed structural alternatives, not actual selection. -/
inductive Reach (registry : Registry) : SourceRequest n → SourceRequest n → Prop where
  | refl : Reach registry q q
  | step : child ∈ next registry q → Reach registry child target → Reach registry q target

theorem closure_complete (registry : Registry) (q target : SourceRequest n)
    (reachable : Reach registry q target) : target ∈ closure registry q := by
  induction reachable with
  | refl => rw [closure]; exact List.mem_cons_self
  | @step q child target edge _ ih =>
    rw [closure]
    apply List.mem_cons_of_mem
    exact List.mem_flatMap.mpr ⟨⟨child, edge⟩, List.mem_attach _ _, ih⟩

theorem closure_sound (registry : Registry) (q target : SourceRequest n)
    (member : target ∈ closure registry q) : Reach registry q target := by
  have all : ∀ measure, ∀ q : SourceRequest n, sourceWeight q = measure →
      ∀ target, target ∈ closure registry q → Reach registry q target := by
    intro measure
    induction measure using Nat.strongRecOn with
    | ind measure ih =>
      intro q size target member
      rw [closure] at member
      rcases List.mem_cons.mp member with same | below
      · subst target; exact .refl
      · obtain ⟨child, _, member⟩ := List.mem_flatMap.mp below
        have decrease : sourceWeight child.val < measure := by
          rw [← size]
          exact next_decreases registry child.val q child.property
        exact .step child.property (ih _ decrease child.val rfl target member)
  exact all _ q rfl target member

theorem closure_exact (registry : Registry) (q target : SourceRequest n) :
    target ∈ closure registry q ↔ Reach registry q target :=
  ⟨closure_sound registry q target, closure_complete registry q target⟩

theorem reach_trans (registry : Registry) (q middle target : SourceRequest n)
    (first : Reach registry q middle) (second : Reach registry middle target) :
    Reach registry q target := by
  induction first with
  | refl => exact second
  | step edge _ ih => exact .step edge (ih second)

theorem generated_closed (registry : Registry) (root parent child : SourceRequest n)
    (member : parent ∈ closure registry root) (edge : Generated registry child parent) :
    child ∈ closure registry root := by
  apply closure_complete
  exact reach_trans registry root parent child (closure_sound registry root parent member)
    (.step (generated_present registry child parent edge) .refl)

/-- A computed finite source domain contains every actual capture-bearing child
of every member, even when the state changes arbitrarily between generations.
No closure/fuel/Acc premise is supplied. Not a saturation or selection theorem. -/
theorem actual_child_closed (registry : Registry) (root parent : SourceRequest n)
    (member : parent ∈ closure registry root) (s : State n) (d : Declaration)
    (lp hp : Ty) (depth : Nat) (child : Request)
    (produced : production registry.declarations (parent.eval s) = some (d, lp, hp))
    (located : captureDepth d.head = some depth)
    (generated : child ∈ children (parent.eval s) d lp hp) :
    ∃ childSource ∈ closure registry root, childSource.eval s = child := by
  obtain ⟨childSource, equal, edge, _⟩ :=
    every_child_generated registry parent s d lp hp depth child produced located generated
  exact ⟨childSource, generated_closed registry root parent childSource member edge, equal⟩

/-- Finite request overapproximation of every source template in the closure,
across every ordinary state. Shared-slot consistency is deliberately overapproximated. -/
def materializedDomain (registry : Registry) (root : SourceRequest n) : List Request :=
  (closure registry root).flatMap SourceRequest.variants

theorem all_states_present (registry : Registry) (root source : SourceRequest n)
    (member : source ∈ closure registry root) (s : State n) :
    source.eval s ∈ materializedDomain registry root := by
  exact List.mem_flatMap.mpr ⟨source, member, root_present s source⟩

/-- The witness remains in the finite request domain under every future state.
This does not assert that the same candidate stays selected in those states. -/
theorem actual_child_all_states (registry : Registry) (root parent : SourceRequest n)
    (member : parent ∈ closure registry root) (s : State n) (d : Declaration)
    (lp hp : Ty) (depth : Nat) (child : Request)
    (produced : production registry.declarations (parent.eval s) = some (d, lp, hp))
    (located : captureDepth d.head = some depth)
    (generated : child ∈ children (parent.eval s) d lp hp) :
    ∃ childSource ∈ closure registry root, childSource.eval s = child ∧
      ∀ future : State n, childSource.eval future ∈ materializedDomain registry root := by
  obtain ⟨source, present, equal⟩ :=
    actual_child_closed registry root parent member s d lp hp depth child produced located generated
  exact ⟨source, present, equal, all_states_present registry root source present⟩

end Yulang.CommonRoleSourceTemplateClosure
