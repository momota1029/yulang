import Yulang.CommonRoleStatefulIndexSweep
import Yulang.CommonRoleAssociatedParentGround

/-! A finite declaration-driven dependency example. Two visits are required in
reverse order. This is not a theorem about arbitrary source saturation. -/
namespace Yulang.CommonRoleStatefulParentExample
open CommonRoleSettledConstraints (State)
open CommonRoleCandidateStateFrontier (extend)
open CommonRoleOrdinaryKnownness
open CommonRoleStatefulIndexSweep
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)
open Roles.AssocExamples

def parent : Roles.Impl := ⟨30, [box (.var 0)], [⟨31, [.var 0]⟩, ⟨32, [.var 0]⟩], 200⟩
def left : Roles.Impl := ⟨31, [Roles.Examples.str], [], 201⟩
def right : Roles.Impl := ⟨32, [Roles.Examples.str], [], 202⟩
def visible : List Roles.Impl := [parent, left, right]
theorem declarations_checked : CheckedRoles.checkDatabase visible = true := by decide +kernel
theorem declarations_wellFormed : Roles.WellFormed visible :=
  (CheckedRoles.checkDatabase_exact visible).mp declarations_checked
def parentGoal (term : Roles.Term) : Roles.Goal := ⟨30, [box term]⟩

def rightAnnotation : Roles.AssocImpl := ⟨right, [(0, Roles.Examples.str)], by decide⟩
def annotations : List Roles.AssocImpl :=
  [⟨parent, [], by decide⟩, ⟨left, [], by decide⟩, rightAnnotation]
def assocEnvironment : Roles.AssocEnv where
  impls := annotations
  coherent := by
    intro i hi j hj same
    simp only [annotations, List.mem_cons, List.not_mem_nil, or_false] at hi hj
    rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;>
      simp_all [parent, left, rightAnnotation, right]
def signature : Roles.RoleDecl where
  arity := 1
  assoc := fun name => if name = 0 then some none else none
  defaultsScoped := by intro name rhs h; split at h <;> simp_all
def noAssociated : Roles.RoleDecl where
  arity := 1
  assoc := fun _ => none
  defaultsScoped := by intro _ _ h; cases h
def assocRoles : Roles.RoleDecls := fun role => if role = 32 then signature else noAssociated

theorem assoc_wellFormed : Roles.WellFormed assocEnvironment.cores := declarations_wellFormed

theorem associated_checked : Roles.AssocWellFormed assocEnvironment assocRoles := by
  intro implementation member
  simp only [assocEnvironment, annotations, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;>
    simp [Roles.AssocHeadVars, Roles.AssocComplete, Roles.AssocDeclared, rightAnnotation,
      right, parent, left, assocRoles, signature, noAssociated, Roles.Examples.str,
      box, Roles.Term.occurrences, Roles.argsOccurrences]

def rightGoal : Roles.Goal := ⟨32, [Roles.Examples.str]⟩
theorem right_resolved : Roles.resolve assocEnvironment.cores assoc_wellFormed rightGoal = .resolved := by
  rw [Roles.resolve_one _ _ _ right (by decide +kernel)]
  rfl

theorem right_value : Roles.assocOf assocEnvironment assocRoles assoc_wellFormed rightGoal 0 =
    some Roles.Examples.str := by
  rw [Roles.assoc_independent_of_constraints _ _ _ _ _ right_resolved rightAnnotation
    (by simp [assocEnvironment, annotations]) (by decide +kernel)]
  rfl

def seedRequest : CommonRoleAssociatedStateFlow.Request 3 :=
  ⟨rightGoal, 0, 0⟩
def seed : Option (State 3) :=
  CommonRoleAssociatedStateFlow.fromSourceStore assocEnvironment assocRoles
    assoc_wellFormed seedRequest State.empty

def s0 : State 3 := extend State.empty 0 .str
def s1 : State 3 := extend s0 1 .str
def s2 : State 3 := extend s1 2 .str
def s3 : State 3 := extend s2 1 .str

theorem seed_from_declaration : seed = some s0 := by
  unfold seed
  rw [CommonRoleAssociatedStateFlow.source_store_agrees]
  have computed : CommonRoleAssociatedStateFlow.Computed assocEnvironment
      assocRoles assoc_wellFormed seedRequest .str := ⟨rfl, _, right_value, rfl⟩
  have hv := (CommonRoleAssociatedStateFlow.value_exact ..).mpr computed
  simp only [CommonRoleAssociatedStateFlow.produce, hv, Option.map_some]
  rfl

def reverseEdges : List (Edge 3) := [⟨1, 2⟩, ⟨0, 1⟩]

private theorem detect0 : detect s0.atoms (0 : Fin 3) = some .str :=
  explicit_pair_detected _ _
private theorem detect1 : detect s1.atoms (1 : Fin 3) = some .str := by
  simp [s1, s0, extend, CommonRoleCandidateStateFrontier.equality,
    detect, candidates, upper, lower, upperHead, lowerHead, State.empty]
private theorem detect0_s2 : detect s2.atoms (0 : Fin 3) = some .str := by
  simp [s2, s1, s0, extend, CommonRoleCandidateStateFrontier.equality,
    detect, candidates, upper, lower, upperHead, lowerHead, State.empty]

theorem first_pending : produceIndex s0 (1 : Fin 3) (2 : Fin 3) = none := by
  simp [produceIndex, materialize, detect, candidates, upper, lower,
    upperHead, lowerHead, s0, extend, State.empty, CommonRoleCandidateStateFrontier.equality]

theorem first_sweep : sweep reverseEdges s0 = ([false, true], s1) := by
  have ready := index_from_detected_str s0 0 1 detect0
  simp [reverseEdges, sweep, visit, first_pending, ready, s1]

theorem second_sweep : sweep reverseEdges s1 = ([true, true], s3) := by
  have ready1 := index_from_detected_str s1 1 2 detect1
  have ready0 := index_from_detected_str s2 0 1 detect0_s2
  change produceIndex (extend s1 (2 : Fin 3) .str) (0 : Fin 3) (1 : Fin 3) =
    some (extend s2 (1 : Fin 3) .str) at ready0
  simp only [reverseEdges, sweep, visit, ready1, ready0]
  rfl

theorem final_materialized : materialize s3.atoms (2 : Fin 3) = some Roles.Examples.str := by
  simp [materialize, detect, candidates, upper, lower, upperHead, lowerHead,
    s3, s2, s1, s0, extend, State.empty, CommonRoleCandidateStateFrontier.equality, encode,
    Roles.Examples.str]

theorem final_models (assignment : Fin 3 → Comp Common.model) :
    All Common.model assignment s3.atoms ↔
      Common.Equivalent (assignment (0 : Fin 3)).1 (.base .str) ∧
      Common.Equivalent (assignment (1 : Fin 3)).1 (.base .str) ∧
      Common.Equivalent (assignment (2 : Fin 3)).1 (.base .str) := by
  simp only [s3, s2, s1, s0, CommonRoleCandidateStateFrontier.extend_exact]
  simp [State.empty, All, and_assoc, and_left_comm, and_comm]

theorem final_consistent : CommonRoleOpenPropagation.consistent s3 = true := by
  apply (CommonRoleOpenPropagation.consistent_exact _).mpr
  refine ⟨fun _ => Comp.pure Common.model (.base .str), (final_models _).mpr ?_⟩
  exact ⟨Common.equivalent_refl _, Common.equivalent_refl _, Common.equivalent_refl _⟩


theorem parent_str_resolved : Roles.resolve visible declarations_wellFormed
    (parentGoal Roles.Examples.str) = .resolved := by
  rw [Roles.resolve_one _ _ _ parent (by decide +kernel)]
  change Roles.combine [Roles.resolve visible declarations_wellFormed ⟨31, [Roles.Examples.str]⟩,
    Roles.resolve visible declarations_wellFormed ⟨32, [Roles.Examples.str]⟩] = .resolved
  rw [Roles.resolve_one _ _ _ left (by decide +kernel), Roles.resolve_one _ _ _ right (by decide +kernel)]
  rfl

def run : Option (State 3 × Roles.Term × RoleDictionaries.Answer) := do
  let initial ← seed
  let pass1 := sweep reverseEdges initial
  let pass2 := sweep reverseEdges pass1.2
  if CommonRoleOpenPropagation.consistent pass2.2 then
    let argument ← materialize pass2.2.atoms 2
    pure (pass2.2, argument,
      RoleDictionaries.elaborate visible declarations_wellFormed (parentGoal argument))
  else none

/-- Independent final result: ordinary models all impose str and the actual
Parent goal resolves with a dictionary, not an arbitrary claimed result tag. -/
def Final (out : State 3) (argument : Roles.Term) (answer : RoleDictionaries.Answer) : Prop :=
  out = s3 ∧ argument = Roles.Examples.str ∧
    ∃ dictionary : RoleDictionaries.Dictionary visible (parentGoal Roles.Examples.str),
      answer = .resolved dictionary.erase

theorem run_value : run = some (s3, Roles.Examples.str,
    RoleDictionaries.elaborate visible declarations_wellFormed
      (parentGoal Roles.Examples.str)) := by
  unfold run
  rw [seed_from_declaration]
  change (if CommonRoleOpenPropagation.consistent (sweep reverseEdges (sweep reverseEdges s0).2).2 then
    (materialize (sweep reverseEdges (sweep reverseEdges s0).2).2.atoms 2).bind
      (fun argument => some ((sweep reverseEdges (sweep reverseEdges s0).2).2, argument,
        RoleDictionaries.elaborate visible declarations_wellFormed (parentGoal argument)))
    else none) = _
  rw [first_sweep]
  change (if CommonRoleOpenPropagation.consistent (sweep reverseEdges s1).2 then _ else none) = _
  rw [second_sweep]
  change (if CommonRoleOpenPropagation.consistent s3 then
    (materialize s3.atoms 2).bind (fun argument => some (s3, argument,
      RoleDictionaries.elaborate visible declarations_wellFormed (parentGoal argument))) else none) = _
  rw [final_consistent]
  simp only [↓reduceIte]
  rw [final_materialized]
  rfl

/-- An unconditional iff for this complete finite example, not general B4. -/
theorem outer_exact (out : State 3) (argument : Roles.Term)
    (answer : RoleDictionaries.Answer) : run = some (out, argument, answer) ↔
      Final out argument answer := by
  rw [run_value]
  constructor
  · intro h
    cases h
    let d := RoleDictionaries.buildResolved visible declarations_wellFormed
      (parentGoal Roles.Examples.str) parent_str_resolved
    exact ⟨rfl, rfl, d, (RoleDictionaries.elaborate_success_iff ..).mpr ⟨d, rfl⟩⟩
  · rintro ⟨rfl, rfl, dictionary, rfl⟩
    rw [(RoleDictionaries.elaborate_success_iff ..).mpr ⟨dictionary, rfl⟩]

theorem resolved_visible : ∃ plan, run = some (s3, Roles.Examples.str, .resolved plan) ∧
    ∀ implementation ∈ plan.declarations, implementation ∈ visible := by
  let d := RoleDictionaries.buildResolved visible declarations_wellFormed
    (parentGoal Roles.Examples.str) parent_str_resolved
  exact ⟨d.erase, (outer_exact ..).mpr ⟨rfl, rfl, d, rfl⟩, d.all_visible⟩

end Yulang.CommonRoleStatefulParentExample
