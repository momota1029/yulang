import Yulang.CommonRoleOpenProducerAccess
import Yulang.CommonRoleOpenThreading

/-! A concrete ordinary-state pass fed by the two-endpoint producer. The
finite slot map is an explicit boundary input, NOT a proved source allocator.
Every update is derived from the selected declaration and its original two
captured payloads. No precomputed update list is accepted by this interface. -/
namespace Yulang.CommonRoleOpenPropagation
open CommonRoleSettledSyntax
open CommonRoleSettledConstraints (State)
open CommonRoleOpenProducer
open CommonRoleOutermostResolver (Frontier)
open CommonRoleCandidateConstraints (Bindings Compatible)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)

abbrev Allocation (n : Nat) := Ty → Fin n

/-- Use every original name occurrence; the endpoints stay separate. -/
def capture (allocate : Allocation n) (d : Declaration) (lo up : Ty) : Bindings n :=
  d.head.names.map (fun name => (name, (allocate lo, allocate up)))

/-- Updates only come from the actual uniquely selected structural producer. -/
def update (visible : List Declaration) (allocate : Allocation n) (q : Request) : Bindings n :=
  match frontier visible q with
  | .selected _ _ => match production visible q with
      | some (d, lo, up) => capture allocate d lo up
      | none => []
  | _ => []

def prepare (visible : List Declaration) (allocate : Allocation n) (q : Request) (s : State n) : State n :=
  CommonRoleOpenState.add s (update visible allocate q)

theorem prepare_exact (visible : List Declaration) (allocate : Allocation n)
    (q : Request) (s : State n) (assignment : Fin n → Comp Common.model) :
    All Common.model assignment (prepare visible allocate q s).atoms ↔
      All Common.model assignment s.atoms ∧ Compatible (update visible allocate q) assignment :=
  CommonRoleOpenState.add_exact _ _ _

/-- The actual finite ordinary solver, not a compatibility oracle. -/
def consistent (s : State n) : Bool := !(CommonRoleOpenState.solve s []).isEmpty

theorem consistent_exact (s : State n) : consistent s = true ↔ s.Models := by
  have empty := CommonRoleOpenState.solve_empty_exact s []
  simp only [List.not_mem_nil, false_implies, forall_const, and_true] at empty
  unfold consistent
  cases found : CommonRoleOpenState.solve s [] with
  | nil =>
      have absent := empty.mp found
      simp only [List.isEmpty, Bool.not_true, Bool.false_eq_true, false_iff]
      exact absent
  | cons first rest =>
      have present : s.Models := by
        classical
        by_cases yes : s.Models
        · exact yes
        · have impossible := empty.mpr yes
          simp [found] at impossible
      simp [present]

def produce (visible : List Declaration) (allocate : Allocation n) (q : Request) (s : State n) : Frontier Request :=
  if consistent (prepare visible allocate q s) then frontier visible q else .rejected

/-- Independent state-gated local judgment. `Local` is the independent
structural judgment, and Models quantifies one shared ordinary assignment. -/
inductive Produced (visible : List Declaration) (allocate : Allocation n)
    (q : Request) (s : State n) : Frontier Request → Prop where
  | valid : (prepare visible allocate q s).Models → Local visible q f → Produced visible allocate q s f
  | impossible : ¬ (prepare visible allocate q s).Models → Produced visible allocate q s .rejected

theorem produce_exact (visible : List Declaration) (allocate : Allocation n)
    (q : Request) (s : State n) (f : Frontier Request) :
    produce visible allocate q s = f ↔ Produced visible allocate q s f := by
  by_cases ok : consistent (prepare visible allocate q s) = true
  · have models := (consistent_exact _).mp ok
    constructor
    · intro h
      exact .valid models ((frontier_exact visible q f).mp (by simpa [produce, ok] using h))
    · intro h
      cases h with
      | valid _ rule => simpa [produce, ok] using (frontier_exact visible q f).mpr rule
      | impossible bad => exact False.elim (bad models)
  · have absent : ¬ (prepare visible allocate q s).Models := mt (consistent_exact _).mpr ok
    have eqFalse := Bool.eq_false_iff.mpr ok
    constructor
    · intro h
      have : f = .rejected := by simpa [produce, eqFalse] using h.symm
      rw [this]
      exact .impossible absent
    · intro h
      cases h with
      | valid models _ => exact False.elim (absent models)
      | impossible _ => simp [produce, eqFalse]

/-- State gating never invents a new source where edge. -/
theorem produced_child_step (visible : List Declaration) (allocate : Allocation n)
    (q child : Request) (s : State n) (key : Nat) (cs : List Request)
    (selected : Produced visible allocate q s (.selected key cs)) (member : child ∈ cs) :
    CommonRoleOpenDescent.Step visible child q := by
  cases selected with
  | valid _ rule => exact CommonRoleOpenProducerAccess.child_step visible q child ⟨key, cs, rule, member⟩

/-- Every state-dependent generated child is covered by the declaration
check's strict measure. There is no accessibility field in the request. -/
theorem produced_child_decreases (registry : Registry) (allocate : Allocation n)
    (q child : Request) (s : State n) (key : Nat) (cs : List Request)
    (selected : Produced registry.declarations allocate q s (.selected key cs)) (member : child ∈ cs) :
    CommonRoleOpenDescent.weight child < CommonRoleOpenDescent.weight q :=
  CommonRoleOpenDescent.step_decreases registry.declarations registry.checked child q
    (produced_child_step _ allocate q child s key cs selected member)

def childList : Frontier Request → List Request
  | .selected _ cs => cs
  | _ => []

def children (visible : List Declaration) (allocate : Allocation n) (q : Request) (s : State n) : List Request :=
  childList (produce visible allocate q s)

def Children (visible : List Declaration) (allocate : Allocation n)
    (q : Request) (s : State n) (cs : List Request) : Prop :=
  ∃ f, Produced visible allocate q s f ∧ childList f = cs

theorem children_exact (visible : List Declaration) (allocate : Allocation n)
    (q : Request) (s : State n) (cs : List Request) :
    children visible allocate q s = cs ↔ Children visible allocate q s cs := by
  constructor
  · intro h; exact ⟨_, (produce_exact ..).mp rfl, h⟩
  · rintro ⟨f, produced, result⟩
    unfold children
    rw [(produce_exact ..).mpr produced, result]

/-- Regenerate one child's actual capture constraints from its CURRENT state. -/
def advance (visible : List Declaration) (allocate : Allocation n) (q : Request) (s : State n) :
    Frontier Request × State n := (produce visible allocate q s, prepare visible allocate q s)

inductive Advance (visible : List Declaration) (allocate : Allocation n)
    (q : Request) (s : State n) : Frontier Request → State n → Prop where
  | step : Produced visible allocate q s f → Advance visible allocate q s f (prepare visible allocate q s)

theorem advance_exact (visible : List Declaration) (allocate : Allocation n)
    (q : Request) (s : State n) (f : Frontier Request) (next : State n) :
    advance visible allocate q s = (f, next) ↔ Advance visible allocate q s f next := by
  constructor
  · intro h
    have parts : produce visible allocate q s = f ∧ prepare visible allocate q s = next := Prod.mk.inj h
    rw [← parts.2]
    exact .step ((produce_exact ..).mp parts.1)
  · intro h
    cases h with
    | step produced => simp only [advance, (produce_exact ..).mpr produced]

/-- One real state-changing sibling pass. This is not a saturation/recursive
resolve theorem: its child step is one local regeneration. -/
def pass (visible : List Declaration) (allocate : Allocation n) (q : Request) (s : State n) :=
  CommonRoleOpenThreading.drive (children visible allocate) (produce visible allocate)
    (advance visible allocate) q (prepare visible allocate q s)

theorem pass_exact (visible : List Declaration) (allocate : Allocation n)
    (q : Request) (s : State n) (trace) :
    pass visible allocate q s = trace ↔
      CommonRoleOpenThreading.Driven (Children visible allocate) (Produced visible allocate)
        (Advance visible allocate) q (prepare visible allocate q s) trace :=
  CommonRoleOpenThreading.drive_exact _ _ _ _ _ _
    (children_exact visible allocate) (produce_exact visible allocate) (advance_exact visible allocate) _ _ _

theorem advance_preserves (visible : List Declaration) (allocate : Allocation n)
    (q : Request) (s next : State n) (f : Frontier Request)
    (step : Advance visible allocate q s f next) (assignment : Fin n → Comp Common.model)
    (model : All Common.model assignment next.atoms) : All Common.model assignment s.atoms := by
  cases step
  exact ((prepare_exact ..).mp model).1

/-- The final models of the actual pass satisfy the original parent state. -/
theorem pass_preserves (visible : List Declaration) (allocate : Allocation n)
    (q : Request) (s : State n) (assignment : Fin n → Comp Common.model)
    (model : All Common.model assignment (pass visible allocate q s).state.atoms) :
    All Common.model assignment s.atoms := by
  have driven := (pass_exact visible allocate q s _).mp rfl
  have retained := CommonRoleOpenThreading.thread_preserves (Advance visible allocate)
    (fun child before result after step assignment model =>
      advance_preserves visible allocate child before after result step assignment model)
    driven.evaluated assignment model
  exact ((prepare_exact ..).mp retained).1

end Yulang.CommonRoleOpenPropagation
