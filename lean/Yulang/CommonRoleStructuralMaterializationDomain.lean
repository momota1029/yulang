import Yulang.CommonRoleStructuralMaterializationProgress

/-! A finite child-work domain computed from an actual ordinary atom envelope.
It covers every inclusive substate and all recursively regenerated children.
The envelope may be the computed final state of a finite submitted batch job;
no uniform bound on arbitrary future evidence is claimed. -/
namespace Yulang.CommonRoleStructuralMaterializationDomain
open CommonRoleCaptureNormalization (Form)
open CommonRoleStablePaterson (Declaration)
open CommonRoleIntervalPaterson (Goal Argument)
open CommonRoleIntervalWorkClosure (Checked Reach closure)
open CommonRoleStructuralOrdinaryMaterialization (materialize materializeGoal candidates Evidence)
open CommonRoleStructuralMaterializationProgress (Included)
open PresenceNormalForm (Atom)

variable {n : Nat} {atoms envelope : List (Atom (Fin n))}

def variants (envelope : List (Atom (Fin n))) (slots : Nat → Fin n) : Form → List Form
  | .var name => .var name :: candidates envelope (slots name)
  | .int => [.int]
  | .pair a b => (variants envelope slots a).flatMap fun x => (variants envelope slots b).map (.pair x)
  | .join a b => (variants envelope slots a).flatMap fun x => (variants envelope slots b).map (.join x)
  | .tick a => (variants envelope slots a).map .tick

theorem materialize_present (included : Included atoms envelope) (slots : Nat → Fin n) (f : Form) :
    materialize atoms slots f ∈ variants envelope slots f := by
  induction f with
  | var name =>
    cases found : CommonRoleStructuralOrdinaryMaterialization.detect atoms (slots name) with
    | none => simp [materialize,found,variants]
    | some payload =>
      have evidence := ((CommonRoleStructuralOrdinaryMaterialization.detect_exact atoms (slots name) payload).mp found).1
      have member := (CommonRoleStructuralOrdinaryMaterialization.candidates_exact envelope (slots name) payload).mpr
        (CommonRoleStructuralMaterializationProgress.evidence_mono included (slots name) payload evidence)
      simp [materialize,found,variants,member]
  | int => simp [materialize,variants]
  | pair a b ha hb | join a b ha hb =>
    exact List.mem_flatMap.mpr ⟨_,ha,List.mem_map.mpr ⟨_,hb,rfl⟩⟩
  | tick a ha => exact List.mem_map.mpr ⟨_,ha,rfl⟩

def argumentVariants (envelope : List (Atom (Fin n))) (slots : Nat → Fin n) :
    List Argument → List (List Argument)
  | [] => [[]]
  | (lo,hi) :: rest => (variants envelope slots lo).flatMap fun a =>
      (variants envelope slots hi).flatMap fun b =>
        (argumentVariants envelope slots rest).map ((a,b) :: ·)

theorem arguments_present (included : Included atoms envelope) (slots : Nat → Fin n)
    (args : List Argument) :
    args.map (fun p => (materialize atoms slots p.1,materialize atoms slots p.2)) ∈
      argumentVariants envelope slots args := by
  induction args with
  | nil => simp [argumentVariants]
  | cons arg rest ih =>
    exact List.mem_flatMap.mpr ⟨_,materialize_present included slots arg.1,
      List.mem_flatMap.mpr ⟨_,materialize_present included slots arg.2,List.mem_map.mpr ⟨_,ih,rfl⟩⟩⟩

def goalVariants (envelope : List (Atom (Fin n))) (slots : Nat → Fin n) (original : Goal) : List Goal :=
  (argumentVariants envelope slots original.arguments).map (Goal.mk original.role)

theorem goal_present (included : Included atoms envelope) (slots : Nat → Fin n) (original : Goal) :
    materializeGoal atoms slots original ∈ goalVariants envelope slots original :=
  List.mem_map.mpr ⟨_,arguments_present included slots original.arguments,rfl⟩

def domain (registry : List Declaration) (checked : Checked registry)
    (envelope : List (Atom (Fin n))) (slots : Nat → Fin n) (original : Goal) : List Goal :=
  (goalVariants envelope slots original).flatMap (closure registry checked)

theorem domain_exact (registry : List Declaration) (checked : Checked registry)
    (envelope : List (Atom (Fin n))) (slots : Nat → Fin n) (original target : Goal) :
    target ∈ domain registry checked envelope slots original ↔
      ∃ root ∈ goalVariants envelope slots original, Reach registry root target := by
  simp only [domain,List.mem_flatMap,CommonRoleIntervalWorkClosure.closure_exact]

theorem regenerated_reach_present (registry : List Declaration) (checked : Checked registry)
    (included : Included atoms envelope) (slots : Nat → Fin n) (original target : Goal)
    (reachable : Reach registry (materializeGoal atoms slots original) target) :
    target ∈ domain registry checked envelope slots original :=
  (domain_exact ..).mpr ⟨_,goal_present included slots original,reachable⟩

theorem domain_child_closed (registry : List Declaration) (checked : Checked registry)
    (envelope : List (Atom (Fin n))) (slots : Nat → Fin n) (original goal target : Goal)
    (member : goal ∈ domain registry checked envelope slots original)
    (edge : CommonRoleIntervalWorkClosure.Edge registry goal target) :
    target ∈ domain registry checked envelope slots original := by
  obtain ⟨root,present,reachable⟩ := (domain_exact ..).mp member
  exact (domain_exact ..).mpr ⟨root,present,
    CommonRoleIntervalWorkClosure.reach_trans reachable (.step edge .refl)⟩

def workDomain (registry : List Declaration) (envelope : List (Atom (Fin n)))
    (slots : Nat → Fin n) (original : Goal) : Option (List Goal) :=
  if checked : registry.all CommonRoleStablePaterson.check = true then
    some (domain registry (List.all_eq_true.mp checked) envelope slots original)
  else none

theorem workDomain_exact (registry : List Declaration) (envelope : List (Atom (Fin n)))
    (slots : Nat → Fin n) (original : Goal) (bound : List Goal) :
    workDomain registry envelope slots original = some bound ↔
      ∃ checked : Checked registry, bound = domain registry checked envelope slots original := by
  unfold workDomain
  split
  · constructor
    · intro same; exact ⟨_,Option.some.inj same.symm⟩
    · rintro ⟨_,rfl⟩; rfl
  · rename_i notChecked
    constructor
    · intro impossible; cases impossible
    · rintro ⟨checked,_⟩; exact False.elim (notChecked (List.all_eq_true.mpr checked))

/-- Every generated node, including failed and outside nodes, belongs to the
computed domain. No ordinary model or successful dictionary is required. -/
theorem run_work_present (registry : List Declaration) (included : Included atoms envelope)
    (slots : Nat → Fin n) (sources : CommonRoleGuardedIntervalPlans.Sources)
    (old : CommonRoleGuardedIntervalPlans.Plan (Fin n)) (original : Goal) (output)
    (returned : CommonRoleStructuralOrdinaryMaterialization.run registry slots sources atoms old original = some output)
    (target : Goal) (member : target ∈ CommonRoleFrontierReachability.goals output.1) :
    ∃ bound, workDomain registry envelope slots original = some bound ∧ target ∈ bound := by
  obtain ⟨tree,found,rfl⟩ := Option.map_eq_some_iff.mp returned
  obtain ⟨checked,rfl⟩ := (CommonRoleGuardedIntervalFrontier.run_exact ..).mp found
  rw [CommonRoleFrontierReachability.build_goals] at member
  exact ⟨_,(workDomain_exact ..).mpr ⟨checked,rfl⟩,
    regenerated_reach_present registry checked included slots original target
      ((CommonRoleIntervalWorkClosure.closure_exact ..).mp member)⟩

/-- The complete submitted finite job provides its own envelope through actual
cumulative appends. This is not an assumption that future inputs stop arriving. -/
theorem trace_includes_final (initial : CommonRoleSettledConstraints.State n)
    (batches : List (CommonRoleSettledConstraints.State n))
    (state : CommonRoleSettledConstraints.State n)
    (member : state ∈ CommonRoleCheckedOrdinaryReplay.trace initial batches) :
    Included state.atoms (CommonRoleCheckedOrdinaryReplay.final initial batches).atoms := by
  induction batches generalizing initial with
  | nil => cases member
  | cons batch rest ih =>
    rcases List.mem_cons.mp member with same | later
    · subst state
      exact CommonRoleCheckedOrdinaryReplay.final_includes _ _
    · exact ih _ later

end Yulang.CommonRoleStructuralMaterializationDomain
