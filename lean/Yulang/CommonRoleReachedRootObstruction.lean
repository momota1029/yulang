import Yulang.CommonRolePackedHalting

/-!
# E2: rejecting only recursive role-argument roots is insufficient

The machine input contains all actual packed declaration fields, associated
bodies, unary signatures and a finite regular goal description. It contains
no semantic oracle. The success bit is only a necessary fragment of a total
exact resolver returning selection/rejection/ambiguity and real dictionaries.
-/

namespace Yulang.CommonRoleReachedRootObstruction

open CommonRoleComputation (Code Tree Eval Halts IsNode)
open CommonRoleReachedRoot
open CommonRolePackedRegistry (visible environment roles)
open CommonRolePackedHalting (startGoal dictionary_exact)
open CommonRoleRegularWire (tagged groundWire listWire assocImplWire Signature taggedCode eval_taggedCode)
open CommonRoleTuringBridge (Machine Runs encodeNat encodeBool project eval_project)
open CommonRoleTuringDelimited (initial classifierCode classifier_of_runs)

def descriptionWire : Description → Tree
  | .finite value => tagged 1 (groundWire value)
  | .data value => tagged 0 value
  | .clock => CommonRoleRegularWire.TypeDescription.clock.wire
  | .pair first last => tagged 2 (.node (descriptionWire first) (descriptionWire last))
  | .variant tag payload => tagged 4 (.node (encodeNat tag) (descriptionWire payload))

def goalWire (goal : Goal) : Tree := .node (encodeNat goal.role) (descriptionWire goal.argument)

def signatures : List Signature := List.replicate 5 ⟨1, [(0, none)]⟩

def databaseWire (code : Code) : Tree :=
  .node (listWire assocImplWire (environment code).impls) (listWire Signature.wire signatures)

def descriptor (code : Code) : Tree := .node (databaseWire code) (groundWire code.encode)

def queryWire (code : Code) (input : Tree) : Tree :=
  .node (databaseWire code) (goalWire (startGoal code input))

/-- A fixed finite program copies the actual database from the descriptor
and builds the unary pair goal, including the one-node clock graph. -/
def queryCode : Code :=
  .pair (project [false, false])
    (.pair (.const (encodeNat 1))
      (taggedCode 2 (.pair (.const (descriptionWire .clock))
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
    Eval queryCode (.node (descriptor code) input) output ↔ output = queryWire code input := by
  constructor
  · intro evaluated
    exact evaluated.deterministic (eval_queryCode code input)
  · rintro rfl
    exact eval_queryCode code input

theorem signature_actual (role : Nat) (bound : role < 5) :
    (signatures[role]?).map Signature.arity = some (roles role).arity ∧
    (signatures[role]?).map Signature.associated = some [(0, none)] := by
  unfold signatures
  rw [List.getElem?_replicate]
  simp [bound, CommonRolePackedRegistry.roles,
    CommonRolePackedRegistry.requiredRole]

/-- Only finite descriptions are input; every actual stored head, where,
key, associated body and role signature is serialized. -/
def TotalReachedRootResolver (machine : Machine) : Prop :=
  ∀ code input, ∃ final,
    Runs machine (initial (queryWire code input)) final ∧
      (final.current = true ↔ Nonempty (Dictionary (visible code) (startGoal code input)))

theorem no_total_reached_root_resolver :
    ¬ ∃ machine : Machine, TotalReachedRootResolver machine := by
  rintro ⟨machine, classifies⟩
  apply CommonRoleComputation.no_halting_classifier descriptor
  refine ⟨.seq queryCode (classifierCode machine), ?_⟩
  intro code input
  obtain ⟨final, executed, correct⟩ := classifies code input
  have halting : final.current = true ↔ Halts code input := correct.trans (dictionary_exact code input)
  refine ⟨encodeBool final.current,
    .seq (eval_queryCode code input) (classifier_of_runs machine _ final executed), ?_⟩
  cases symbol : final.current <;>
    simpa only [symbol, encodeBool, CommonRoleTuringBridge.truth, IsNode,
      Bool.false_eq_true] using halting

/-- Every amended declaration premise is proved, without adding role ranks,
fuel, support, residual, resolver-success or termination premises. -/
theorem reached_root_registry_undecidable :
    (∀ code,
      CommonRoleRegularResolutionObstruction.checkEnvironment (environment code) = true ∧
      Roles.WellFormed (environment code).cores ∧
      CommonRoleRegularResolutionObstruction.HeadDeterminesAssociated (environment code) ∧
      Roles.AssocWellFormed (environment code) roles) ∧
    (∀ code input path, ¬ Rejects (visible code) (startGoal code input) path) ∧
    ¬ ∃ machine : Machine, TotalReachedRootResolver machine := by
  refine ⟨?_, ?_, no_total_reached_root_resolver⟩
  · intro code
    refine ⟨CommonRolePackedRegistry.environment_checked code, ?_,
      CommonRolePackedRegistry.head_determines_associated code,
      CommonRolePackedRegistry.associated_wellFormed code⟩
    rw [CommonRolePackedRegistry.environment_cores]
    exact CommonRolePackedRegistry.declarations_wellFormed code
  · intro code input path
    exact CommonRolePackedHalting.no_rejection code _ _ _ path

end Yulang.CommonRoleReachedRootObstruction
