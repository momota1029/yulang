import Yulang.CommonRoleSourceTemplateClosure
import Yulang.FiniteHorn

/-! Duplicate-free closure under actual producer edges at one ordinary state.
Implementation-fragment restriction: int-only unary capture-bearing templates.
State-changing saturation and candidate uniqueness are NOT claimed. -/
namespace Yulang.CommonRoleSourceWorklist
open CommonRoleSettledSyntax CommonRoleOpenProducer CommonRoleCaptureOrigin
open CommonRoleMaterializedDomain CommonRoleChildTemplates CommonRoleSourceTemplateClosure
open CommonRoleSettledConstraints (State)

deriving instance DecidableEq for Endpoint
deriving instance DecidableEq for SourceRequest

/-- Actual first-hit production, not all structural alternatives or unique selection. -/
def actualNext (registry : Registry) (s : State n) (parent : SourceRequest n) :
    List (SourceRequest n) :=
  match production registry.declarations (parent.eval s) with
  | none => []
  | some (d, _, _) => declarationChildren d parent

theorem actual_next_generated (registry : Registry) (s : State n)
    (parent child : SourceRequest n) (member : child ∈ actualNext registry s parent) :
    Generated registry child parent := by
  unfold actualNext at member
  cases produced : production registry.declarations (parent.eval s) with
  | none => simp [produced] at member
  | some result =>
    obtain ⟨d, lp, hp⟩ := result
    simp only [produced] at member
    unfold declarationChildren at member
    cases located : captureDepth d.head with
    | none => simp [located] at member
    | some depth =>
      simp only [located] at member
      cases lf : extract depth parent.lower with
      | none => simp [lf] at member
      | some lo =>
        cases hf : extract depth parent.upper with
        | none => simp [lf, hf] at member
        | some hi =>
          simp only [lf, hf] at member
          obtain ⟨r, required, rfl⟩ := List.mem_map.mp member
          exact .step parent s d lp hp depth lo hi r produced located lf hf required

abbrev Node (registry : Registry) (root : SourceRequest n) :=
  { q : SourceRequest n // q ∈ closure registry root }

def nodes (registry : Registry) (root : SourceRequest n) : List (Node registry root) :=
  (closure registry root).attach

theorem nodes_complete (registry : Registry) (root : SourceRequest n)
    (q : Node registry root) : q ∈ nodes registry root := List.mem_attach _ _

def rootNode (registry : Registry) (root : SourceRequest n) : Node registry root :=
  ⟨root, closure_complete registry root root .refl⟩

def edgeRule (parent child : Node registry root) : FiniteHorn.Rule (Node registry root) :=
  ⟨[parent], child⟩

def rules (registry : Registry) (root : SourceRequest n) (s : State n) :
    List (FiniteHorn.Rule (Node registry root)) :=
  ⟨[], rootNode registry root⟩ :: (nodes registry root).flatMap (fun parent =>
    ((nodes registry root).filter fun child => child.val ∈ actualNext registry s parent.val).map
      (edgeRule parent))

def saturate (registry : Registry) (root : SourceRequest n) (s : State n) :
    List (Node registry root) := FiniteHorn.saturate (rules registry root s) (nodes registry root)

/-- Source-path judgment independent of the executable worklist. -/
inductive Reach (registry : Registry) (root : SourceRequest n) (s : State n) :
    Node registry root → Prop where
  | root : Reach registry root s (rootNode registry root)
  | step : Reach registry root s parent → child.val ∈ actualNext registry s parent.val →
      Reach registry root s child

theorem edge_rule_present (registry : Registry) (root : SourceRequest n) (s : State n)
    (parent child : Node registry root) (edge : child.val ∈ actualNext registry s parent.val) :
    edgeRule parent child ∈ rules registry root s := by
  apply List.mem_cons_of_mem
  apply List.mem_flatMap.mpr
  refine ⟨parent, nodes_complete .., List.mem_map.mpr ⟨child, ?_, rfl⟩⟩
  exact List.mem_filter.mpr ⟨nodes_complete .., by simpa using edge⟩

theorem derives_sound (registry : Registry) (root : SourceRequest n) (s : State n)
    (q : Node registry root) (h : FiniteHorn.Derives (rules registry root s) q) :
    Reach registry root s q := by
  apply h.sound
  intro rule member premises
  rcases List.mem_cons.mp member with rfl | member
  · exact .root
  · obtain ⟨parent, _, member⟩ := List.mem_flatMap.mp member
    obtain ⟨child, filtered, rfl⟩ := List.mem_map.mp member
    have edge : child.val ∈ actualNext registry s parent.val := by
      simpa using (List.mem_filter.mp filtered).2
    exact .step (premises parent (by simp [edgeRule])) edge

theorem derives_complete (registry : Registry) (root : SourceRequest n) (s : State n)
    (q : Node registry root) (h : Reach registry root s q) :
    FiniteHorn.Derives (rules registry root s) q := by
  induction h with
  | root => exact .applyRule _ List.mem_cons_self (by simp)
  | @step parent child _ edge ih =>
    apply FiniteHorn.Derives.applyRule (edgeRule parent child)
      (edge_rule_present registry root s parent child edge)
    simpa [edgeRule] using ih

theorem saturate_exact (registry : Registry) (root : SourceRequest n) (s : State n)
    (q : Node registry root) : q ∈ saturate registry root s ↔ Reach registry root s q := by
  rw [saturate, FiniteHorn.saturate_exact _ _ (nodes_complete registry root)]
  exact ⟨derives_sound registry root s q, derives_complete registry root s q⟩

theorem saturate_nodup (registry : Registry) (root : SourceRequest n) (s : State n) :
    (saturate registry root s).Nodup := FiniteHorn.saturate_nodup _ _

theorem saturate_capacity (registry : Registry) (root : SourceRequest n) (s : State n) :
    (saturate registry root s).length ≤ (closure registry root).length := by
  simpa [saturate, nodes] using
    FiniteHorn.saturate_length_le (rules registry root s) (nodes registry root)
      (nodes_complete registry root)

/-- Every actual source child of a visited node is visited. The finite domain
is computed from declarations, rather than supplied as a closed-domain premise. -/
theorem saturate_actual_closed (registry : Registry) (root : SourceRequest n) (s : State n)
    (parent : Node registry root) (present : parent ∈ saturate registry root s)
    (child : SourceRequest n) (edge : child ∈ actualNext registry s parent.val) :
    ∃ q ∈ saturate registry root s, q.val = child := by
  have member := generated_closed registry root parent.val child parent.property
    (actual_next_generated registry s parent.val child edge)
  let q : Node registry root := ⟨child, member⟩
  exact ⟨q, (saturate_exact registry root s q).mpr
    (.step ((saturate_exact registry root s parent).mp present) edge), rfl⟩

/-- All concrete children of a visited capture-bearing production are in the
computed worklist, with their source identity retained. -/
theorem concrete_child_visited (registry : Registry) (root : SourceRequest n) (s : State n)
    (parent : Node registry root) (present : parent ∈ saturate registry root s)
    (d : Declaration) (lp hp : Ty) (depth : Nat) (child : Request)
    (produced : production registry.declarations (parent.val.eval s) = some (d, lp, hp))
    (located : captureDepth d.head = some depth)
    (generated : child ∈ children (parent.val.eval s) d lp hp) :
    ∃ q ∈ saturate registry root s, q.val.eval s = child := by
  obtain ⟨lo, hi, r, required, lf, hf, equal, _⟩ :=
    every_child_lifts registry.declarations parent.val s d lp hp depth child
      produced located generated
  have edge : childTemplate r lo hi ∈ actualNext registry s parent.val := by
    simp only [actualNext, produced, declarationChildren, located, lf, hf]
    exact List.mem_map.mpr ⟨r, required, rfl⟩
  obtain ⟨q, visited, same⟩ := saturate_actual_closed registry root s parent present _ edge
  exact ⟨q, visited, by rw [same]; exact equal⟩

theorem root_visited (registry : Registry) (root : SourceRequest n) (s : State n) :
    rootNode registry root ∈ saturate registry root s :=
  (saturate_exact registry root s _).mpr .root

/-- Least closure, for every interpretation of source nodes closed under the
actual fixed-state producer edges. This is not a supplied B4 semantics premise. -/
theorem saturate_least (registry : Registry) (root : SourceRequest n) (s : State n)
    (holds : Node registry root → Prop) (seed : holds (rootNode registry root))
    (closed : ∀ parent child, holds parent →
      child.val ∈ actualNext registry s parent.val → holds child)
    (q : Node registry root) (present : q ∈ saturate registry root s) : holds q := by
  have reachable := (saturate_exact registry root s q).mp present
  clear present
  induction reachable with
  | root => exact seed
  | step _ edge ih => exact closed _ _ ih edge

end Yulang.CommonRoleSourceWorklist
