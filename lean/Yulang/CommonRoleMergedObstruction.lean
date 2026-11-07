import Yulang.CommonRoleMergedHalting

/-! E2 with canonical visible capture, both K2 guards, and actual normalized
variant rows. The fixed input program copies every declaration field and
constructs the finite goal description; its descriptor contains no oracle. -/
namespace Yulang.CommonRoleMergedObstruction

open CommonRoleComputation (Code Tree Eval Halts IsNode)
open CommonRoleCanonicalMergedEvidence (Goal Dictionary)
open CommonRoleMergedRegistry (visible environment roles)
open CommonRoleMergedHalting (startGoal dictionary_exact)
open CommonRoleRegularWire (tagged groundWire listWire assocImplWire Signature taggedCode eval_taggedCode)
open CommonRoleTuringBridge (Machine Runs encodeNat encodeBool project eval_project)
open CommonRoleTuringDelimited (initial classifierCode classifier_of_runs)

/-- Finite descriptions can contain raw input data without an oracle that
first expands that data into a type. There are no unresolved type variables. -/
inductive FiniteDescription where
  | ground : CommonRoleLinearClock.Ground → FiniteDescription
  | data : Tree → FiniteDescription
  | pair : FiniteDescription → FiniteDescription → FiniteDescription
  deriving DecidableEq, Repr

def FiniteDescription.eval : FiniteDescription → CommonRoleLinearClock.Ground
  | .ground value => value
  | .data value => value.encode
  | .pair first last => .pair first.eval last.eval

def FiniteDescription.wire : FiniteDescription → Tree
  | .ground value => tagged 1 (groundWire value)
  | .data value => tagged 0 value
  | .pair first last => tagged 2 (.node first.wire last.wire)

structure GoalDescription where
  role : Nat
  payload : FiniteDescription
  deriving DecidableEq, Repr

def GoalDescription.eval (goal : GoalDescription) : Goal := ⟨goal.role, goal.payload.eval⟩
def GoalDescription.wire (goal : GoalDescription) : Tree :=
  .node (encodeNat goal.role) (tagged 4 (.node (encodeNat 0) goal.payload.wire))

def startDescription (code : Code) (input : Tree) : GoalDescription :=
  ⟨1, .pair (.ground code.encode) (.pair (.data input) (.ground CommonRoleLinearInterpreter.Kont.halt.encode))⟩

theorem start_description (code : Code) (input : Tree) :
    (startDescription code input).eval = startGoal code input := rfl

abbrev signatures := CommonRoleReachedRootObstruction.signatures

def databaseWire (code : Code) : Tree :=
  .node (listWire assocImplWire (environment code).impls) (listWire Signature.wire signatures)

def descriptor (code : Code) : Tree := .node (databaseWire code) (groundWire code.encode)
def queryWire (code : Code) (input : Tree) : Tree :=
  .node (databaseWire code) (startDescription code input).wire

def queryCode : Code :=
  .pair (project [false, false])
    (.pair (.const (encodeNat 1))
      (taggedCode 4 (.pair (.const (encodeNat 0))
        (taggedCode 2 (.pair (taggedCode 1 (project [false, true]))
          (taggedCode 2 (.pair (taggedCode 0 .right)
            (taggedCode 1 (.const (groundWire CommonRoleLinearInterpreter.Kont.halt.encode))))))))))

theorem eval_queryCode (code : Code) (input : Tree) :
    Eval queryCode (.node (descriptor code) input) (queryWire code input) := by
  apply Eval.pair
  · exact eval_project [false, false] _
  · apply Eval.pair (.const _ _)
    apply eval_taggedCode
    apply Eval.pair (.const _ _)
    apply eval_taggedCode
    apply Eval.pair
    · exact eval_taggedCode 1 (eval_project [false, true] _)
    · apply eval_taggedCode
      apply Eval.pair
      · exact eval_taggedCode 0 (.rightNode _ _)
      · exact eval_taggedCode 1 (.const _ _)

theorem queryCode_exact (code : Code) (input output : Tree) :
    Eval queryCode (.node (descriptor code) input) output ↔ output = queryWire code input :=
  ⟨fun evaluation => evaluation.deterministic (eval_queryCode code input), fun same => same ▸ eval_queryCode code input⟩

/-- A necessary success bit of a total exact finite resolver. A real resolver
returning all where dictionaries supplies this bit by inspecting its result. -/
def TotalCanonicalMergedResolver (machine : Machine) : Prop :=
  ∀ code input, ∃ final, Runs machine (initial (queryWire code input)) final ∧
    (final.current = true ↔ Nonempty (Dictionary (visible code) (startGoal code input)))

theorem no_total_canonical_merged_resolver : ¬ ∃ machine : Machine, TotalCanonicalMergedResolver machine := by
  rintro ⟨machine, classifies⟩
  apply CommonRoleComputation.no_halting_classifier descriptor
  refine ⟨.seq queryCode (classifierCode machine), ?_⟩
  intro code input
  obtain ⟨final, executed, correct⟩ := classifies code input
  have halting := correct.trans (dictionary_exact code input)
  refine ⟨encodeBool final.current,
    .seq (eval_queryCode code input) (classifier_of_runs machine _ final executed), ?_⟩
  cases symbol : final.current <;>
    simpa only [symbol, encodeBool, CommonRoleTuringBridge.truth, IsNode, Bool.false_eq_true] using halting

theorem canonical_merged_registry_undecidable :
    (∀ code, CommonRoleMergedRegistry.checkEnvironment (environment code) = true ∧
      CommonRoleNormalizedDeclarations.NormalizedWellFormed (environment code).cores ∧
      Roles.WellFormed (environment code).cores ∧
      CommonRoleMergedRegistry.HeadDeterminesAssociated (environment code) ∧
      Roles.AssocWellFormed (environment code) roles ∧
      ∀ implementation ∈ visible code,
        CommonRoleNormalizedDeclarations.normalizeImpl implementation = implementation ∧
        ∃ copies pattern, CommonRoleMergedRegistry.headFromRow
          (CommonRoleMergedPayload.mergedRow copies pattern) = some implementation.head) ∧
    (∀ code (goal : Goal), goal.description.argument.finite = true ∧
      CommonRoleInspectedSemantics.Ready (visible code) goal.description) ∧
    ¬ ∃ machine : Machine, TotalCanonicalMergedResolver machine := by
  refine ⟨?_, ?_, no_total_canonical_merged_resolver⟩
  · intro code
    have checked := CommonRoleMergedRegistry.environment_checked code
    obtain ⟨wellFormed, associated⟩ := CommonRoleMergedRegistry.checkEnvironment_sound _ checked
    refine ⟨checked, wellFormed, ?_, associated, CommonRoleMergedRegistry.associated_wellFormed code, ?_⟩
    · rw [CommonRoleMergedRegistry.environment_cores]
      exact CommonRoleMergedRegistry.declarations_wellFormed code
    · intro implementation member
      exact ⟨CommonRoleMergedRegistry.declarations_normal code implementation member,
        CommonRoleMergedRegistry.all_heads_from_merge code implementation member⟩
  · intro code goal
    exact ⟨CommonRoleCanonicalMergedEvidence.goal_finite goal,
      CommonRoleCanonicalMergedEvidence.goal_ready (visible code) goal⟩

end Yulang.CommonRoleMergedObstruction
