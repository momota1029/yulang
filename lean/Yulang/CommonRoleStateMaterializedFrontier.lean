import Yulang.CommonRoleFrontierGraphs
import Yulang.CommonRoleOrdinaryKnownness

/-! Actual ordinary-state materialization for the existing int Form fragment.
Every source template has a computed finite domain covering all its regenerated
frontiers at arbitrary states. Original atoms, names and diagnostics are retained.
This is not general interval entailment, saturation or dictionary selection. -/
namespace Yulang.CommonRoleStateMaterializedFrontier
open CommonRoleCaptureNormalization (Form)
open CommonRoleStablePaterson (Declaration)
open CommonRoleIntervalPaterson (Goal Argument)
open CommonRoleIntervalWorkClosure (Checked Reach closure)
open CommonRoleGuardedIntervalPlans (Sources Plan Derives)
open CommonRoleCaptureBatchModels (SharedFits)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (Atom All)

/-- Only explicit int evidence is representable in this existing Form grammar.
Every other case keeps the original source variable, never a chosen type. -/
def materialize (atoms : List (Atom (Fin n))) (slots : Nat → Fin n) : Form → Form
  | .var name => if CommonRoleOrdinaryKnownness.detect atoms (slots name) = some .int
      then .int else .var name
  | .int => .int
  | .pair a b => .pair (materialize atoms slots a) (materialize atoms slots b)
  | .join a b => .join (materialize atoms slots a) (materialize atoms slots b)
  | .tick a => .tick (materialize atoms slots a)

/-- Independent original meaning is preserved for every model of the actual
state. This says nothing about invariance of syntactic candidate inspection. -/
theorem materialize_meaning (atoms : List (Atom (Fin n))) (slots : Nat → Fin n)
    (assignment : Fin n → Comp Common.model) (models : All Common.model assignment atoms)
    (form : Form) :
    Common.Equivalent ((materialize atoms slots form).eval (fun k => (assignment (slots k)).1))
      (form.eval (fun k => (assignment (slots k)).1)) := by
  induction form with
  | var name =>
      simp only [materialize]
      split
      · rename_i known
        exact Common.equivalent_symm
          (CommonRoleOrdinaryKnownness.detect_sound atoms (slots name) .int known assignment models)
      · exact Common.equivalent_refl _
  | int => exact Common.equivalent_refl _
  | pair a b ha hb =>
      exact (CommonCanonicalShapes.pair_equivalent_iff _ _ _ _).mpr ⟨ha,hb⟩
  | join a b ha hb => exact CommonRoleCaptureNormalization.join_congr _ _ _ _ ha hb
  | tick a ha => exact (CommonCanonicalShapes.variant_equivalent_iff 0 _ _).mpr ha

/-- Paired evidence persists under actual atom inclusion when the later state
has a model; conflicting evidence is not silently assigned a winner. -/
theorem detected_int_persists (before after : List (Atom (Fin n)))
    (included : ∀ atom ∈ before, atom ∈ after) (slot : Fin n)
    (assignment : Fin n → Comp Common.model) (models : All Common.model assignment after)
    (known : CommonRoleOrdinaryKnownness.detect before slot = some .int) :
    CommonRoleOrdinaryKnownness.detect after slot = some .int := by
  have evidence := CommonRoleOrdinaryKnownness.detect_evidence before slot .int known
  have later : CommonRoleOrdinaryKnownness.Evidence after slot .int :=
    ⟨included _ evidence.1,included _ evidence.2⟩
  obtain ⟨base,found⟩ := (CommonRoleOrdinaryKnownness.detect_exists after slot).mpr ⟨.int,later⟩
  have same := CommonRoleOrdinaryKnownness.evidence_unique after slot assignment models base .int
    (CommonRoleOrdinaryKnownness.detect_evidence after slot base found) later
  subst base
  exact found

/-- On a consistent extension, rematerializing the original template or the
previously materialized Form produces literally the same syntax. This does not
assert equality of complete frontier trees at different states. -/
theorem rematerialize_fusion (before after : List (Atom (Fin n)))
    (included : ∀ atom ∈ before, atom ∈ after) (slots : Nat → Fin n)
    (assignment : Fin n → Comp Common.model) (models : All Common.model assignment after)
    (form : Form) :
    materialize after slots (materialize before slots form) = materialize after slots form := by
  induction form with
  | var name =>
      by_cases known : CommonRoleOrdinaryKnownness.detect before (slots name) = some .int
      · simp [materialize,known,detected_int_persists before after included (slots name)
          assignment models known]
      · simp [materialize,known]
  | int => rfl
  | pair a b ha hb => simp [materialize,ha,hb]
  | join a b ha hb => simp [materialize,ha,hb]
  | tick a ha => simp [materialize,ha]

/-- Occurrences are independently enumerated, so this is an overapproximation
of consistent source sharing. No variables or constructors are invented. -/
def variants : Form → List Form
  | .var name => [.var name, .int]
  | .int => [.int]
  | .pair a b => (variants a).flatMap fun x => (variants b).map (.pair x)
  | .join a b => (variants a).flatMap fun x => (variants b).map (.join x)
  | .tick a => (variants a).map .tick

theorem materialize_present (atoms : List (Atom (Fin n))) (slots : Nat → Fin n)
    (form : Form) : materialize atoms slots form ∈ variants form := by
  induction form with
  | var name => simp only [materialize]; split <;> simp [variants]
  | int => simp [materialize, variants]
  | pair a b ha hb =>
      exact List.mem_flatMap.mpr ⟨_,ha,List.mem_map.mpr ⟨_,hb,rfl⟩⟩
  | join a b ha hb =>
      exact List.mem_flatMap.mpr ⟨_,ha,List.mem_map.mpr ⟨_,hb,rfl⟩⟩
  | tick a ha => exact List.mem_map.mpr ⟨_,ha,rfl⟩

def arguments (atoms : List (Atom (Fin n))) (slots : Nat → Fin n)
    (original : List Argument) : List Argument :=
  original.map fun pair => (materialize atoms slots pair.1, materialize atoms slots pair.2)

def argumentVariants : List Argument → List (List Argument)
  | [] => [[]]
  | (lo,hi) :: rest => (variants lo).flatMap fun a => (variants hi).flatMap fun b =>
      (argumentVariants rest).map ((a,b) :: ·)

theorem arguments_present (atoms : List (Atom (Fin n))) (slots : Nat → Fin n)
    (original : List Argument) : arguments atoms slots original ∈ argumentVariants original := by
  induction original with
  | nil => simp [arguments,argumentVariants]
  | cons pair rest ih =>
      rcases pair with ⟨lo,hi⟩
      exact List.mem_flatMap.mpr ⟨_,materialize_present atoms slots lo,
        List.mem_flatMap.mpr ⟨_,materialize_present atoms slots hi,
          List.mem_map.mpr ⟨_,ih,rfl⟩⟩⟩

def materializeGoal (atoms : List (Atom (Fin n))) (slots : Nat → Fin n) (original : Goal) : Goal :=
  ⟨original.role,arguments atoms slots original.arguments⟩

def goalVariants (original : Goal) : List Goal :=
  (argumentVariants original.arguments).map (fun args => ⟨original.role,args⟩)

theorem goal_present (atoms : List (Atom (Fin n))) (slots : Nat → Fin n) (original : Goal) :
    materializeGoal atoms slots original ∈ goalVariants original :=
  List.mem_map.mpr ⟨_,arguments_present atoms slots original.arguments,rfl⟩

/-- One finite list computed from the source template and checked declarations,
not from an execution trace or a selected ordinary state. -/
def domain (registry : List Declaration) (checked : Checked registry) (original : Goal) : List Goal :=
  (goalVariants original).flatMap (closure registry checked)

theorem domain_exact (registry : List Declaration) (checked : Checked registry)
    (original target : Goal) :
    target ∈ domain registry checked original ↔
      ∃ root ∈ goalVariants original, Reach registry root target := by
  simp only [domain,List.mem_flatMap,CommonRoleIntervalWorkClosure.closure_exact]

/-- Executable public finite bound; the declaration checker is run here rather
than asking the caller for its proof or for a precomputed closure. -/
def workDomain (registry : List Declaration) (original : Goal) : Option (List Goal) :=
  if checked : registry.all CommonRoleStablePaterson.check = true then
    some (domain registry (List.all_eq_true.mp checked) original)
  else none

theorem workDomain_exact (registry : List Declaration) (original : Goal) (bound : List Goal) :
    workDomain registry original = some bound ↔
      ∃ checked : Checked registry, bound = domain registry checked original := by
  unfold workDomain
  split
  · rename_i checked
    constructor
    · intro same; exact ⟨List.all_eq_true.mp checked,Option.some.inj same.symm⟩
    · rintro ⟨_,rfl⟩; rfl
  · rename_i notChecked
    constructor
    · intro impossible; cases impossible
    · rintro ⟨checked,_⟩
      exact False.elim (notChecked (List.all_eq_true.mpr checked))

/-- Repeated state changes may regenerate entirely different children, but every
finite generated descendant remains in the same source-template work domain. -/
theorem regenerated_reach_present (registry : List Declaration) (checked : Checked registry)
    (atoms : List (Atom (Fin n))) (slots : Nat → Fin n) (original target : Goal)
    (reachable : Reach registry (materializeGoal atoms slots original) target) :
    target ∈ domain registry checked original :=
  (domain_exact ..).mpr ⟨_,goal_present atoms slots original,reachable⟩

/-- Reinspection and complete recursive regeneration occur after materializing
from this exact atom list. Old demands and the original atoms are both kept. -/
def run (registry : List Declaration) (slots : Nat → Fin n) (sources : Sources)
    (atoms : List (Atom (Fin n))) (old : Plan (Fin n)) (original : Goal) :=
  CommonRoleFrontierGraphs.run registry slots sources atoms old
    (materializeGoal atoms slots original)

theorem run_models_exact (registry : List Declaration) (slots : Nat → Fin n) (sources : Sources)
    (atoms : List (Atom (Fin n))) (old : Plan (Fin n)) (original : Goal)
    (assignment : Fin n → Comp Common.model) :
    (∃ output, run registry slots sources atoms old original = some output ∧
      CommonRoleFrontierGraphs.Represents output.2 assignment) ↔
    Checked registry ∧ All Common.model assignment atoms ∧ ∃ sourceValues,
      SharedFits assignment sourceValues old ∧
        Derives registry slots sources assignment sourceValues (materializeGoal atoms slots original) :=
  CommonRoleFrontierGraphs.run_models_exact ..

/-- Every actual node, including unfinished and unsupported nodes, belongs to
the computed finite domain at every state. No represented graph is required. -/
theorem run_work_present (registry : List Declaration) (slots : Nat → Fin n) (sources : Sources)
    (atoms : List (Atom (Fin n))) (old : Plan (Fin n)) (original : Goal)
    (output) (returned : run registry slots sources atoms old original = some output)
    (target : Goal) (member : target ∈ CommonRoleFrontierReachability.goals output.1) :
    ∃ checked : Checked registry, target ∈ domain registry checked original := by
  obtain ⟨tree,found,rfl⟩ := Option.map_eq_some_iff.mp returned
  obtain ⟨checked,rfl⟩ := (CommonRoleGuardedIntervalFrontier.run_exact ..).mp found
  rw [CommonRoleFrontierReachability.build_goals] at member
  exact ⟨checked,regenerated_reach_present registry checked atoms slots original target
    ((CommonRoleIntervalWorkClosure.closure_exact ..).mp member)⟩

/-- The public bound succeeds and contains each actual node whenever the
public graph run succeeds, without caller-supplied proof, fuel or work list. -/
theorem run_computed_bound (registry : List Declaration) (slots : Nat → Fin n) (sources : Sources)
    (atoms : List (Atom (Fin n))) (old : Plan (Fin n)) (original : Goal)
    (output) (returned : run registry slots sources atoms old original = some output)
    (target : Goal) (member : target ∈ CommonRoleFrontierReachability.goals output.1) :
    ∃ bound, workDomain registry original = some bound ∧ target ∈ bound := by
  obtain ⟨checked,included⟩ := run_work_present registry slots sources atoms old original
    output returned target member
  exact ⟨domain registry checked original,(workDomain_exact ..).mpr ⟨checked,rfl⟩,included⟩

/-- The work bound remains closed under further real generated children even
when the node came from a different materialization of the source template. -/
theorem domain_child_closed (registry : List Declaration) (checked : Checked registry)
    (original goal target : Goal) (member : goal ∈ domain registry checked original)
    (edge : CommonRoleIntervalWorkClosure.Edge registry goal target) :
    target ∈ domain registry checked original := by
  obtain ⟨root,present,reachable⟩ := (domain_exact ..).mp member
  exact (domain_exact ..).mpr ⟨root,present,
    CommonRoleIntervalWorkClosure.reach_trans reachable (.step edge .refl)⟩

end Yulang.CommonRoleStateMaterializedFrontier
