import Yulang.CommonRoleFiniteShadowHalting

/-! E2 for the approved root-and-constructor-inspection rejection semantics.
All serialized goal descriptions are finite trees. Actual declaration fields,
associated bodies, signatures and the input are concrete finite syntax. -/

namespace Yulang.CommonRoleFiniteShadowObstruction

open CommonRoleComputation (Code Tree Eval Halts IsNode)
open CommonRoleInspectedSemantics
open CommonRoleFiniteShadowRegistry (visible environment roles HeadDeterminesAssociated)
open CommonRoleFiniteShadowHalting (startGoal dictionary_exact)
open CommonRoleRegularWire (tagged groundWire listWire assocImplWire Signature taggedCode eval_taggedCode)
open CommonRoleTuringBridge (Machine Runs encodeNat encodeBool project eval_project)
open CommonRoleTuringDelimited (initial classifierCode classifier_of_runs)

def descriptionWire : Description → Tree
  | .ground value => tagged 1 (groundWire value)
  | .data value => tagged 0 value
  | .clock => CommonRoleRegularWire.TypeDescription.clock.wire
  | .pair first last => tagged 2 (.node (descriptionWire first) (descriptionWire last))
  | .variant tag payload => tagged 4 (.node (encodeNat tag) (descriptionWire payload))
  | .int => tagged 5 .leaf
  | .empty => tagged 6 .leaf
  | .record payload rest => tagged 7 (.node (descriptionWire payload) (descriptionWire rest))

def goalWire (goal : Goal) : Tree := .node (encodeNat goal.role) (descriptionWire goal.argument)

def signatures : List Signature := List.replicate 5 ⟨1, [(0, none)]⟩

def databaseWire (code : Code) : Tree :=
  .node (listWire assocImplWire (environment code).impls) (listWire Signature.wire signatures)

def descriptor (code : Code) : Tree := .node (databaseWire code) (groundWire code.encode)

def queryWire (code : Code) (input : Tree) : Tree :=
  .node (databaseWire code) (goalWire (startGoal code input))

def queryCode : Code :=
  .pair (project [false, false])
    (.pair (.const (encodeNat 1))
      (taggedCode 7 (.pair
        (taggedCode 2 (.pair (taggedCode 1 (project [false, true]))
          (taggedCode 2 (.pair (taggedCode 0 .right)
            (taggedCode 1 (.const (groundWire CommonRoleLinearInterpreter.Kont.halt.encode)))))))
        (.const (descriptionWire .empty)))))

theorem eval_queryCode (code : Code) (input : Tree) :
    Eval queryCode (.node (descriptor code) input) (queryWire code input) := by
  apply Eval.pair
  · exact eval_project [false, false] _
  · apply Eval.pair (.const _ _)
    apply eval_taggedCode
    apply Eval.pair
    · apply eval_taggedCode
      apply Eval.pair
      · exact eval_taggedCode 1 (eval_project [false, true] _)
      · apply eval_taggedCode
        apply Eval.pair
        · exact eval_taggedCode 0 (.rightNode _ _)
        · exact eval_taggedCode 1 (.const _ _)
    · exact .const _ _

theorem queryCode_exact (code : Code) (input output : Tree) :
    Eval queryCode (.node (descriptor code) input) output ↔ output = queryWire code input :=
  ⟨fun evaluated => evaluated.deterministic (eval_queryCode code input), fun equal => equal ▸ eval_queryCode code input⟩

theorem signature_actual (role : Nat) (bound : role < 5) :
    (signatures[role]?).map Signature.arity = some (roles role).arity ∧
    (signatures[role]?).map Signature.associated = some [(0, none)] := by
  unfold signatures
  rw [List.getElem?_replicate]
  simp [roles, CommonRolePackedRegistry.roles, bound, CommonRolePackedRegistry.requiredRole]

theorem configuration_ready (code : Code) (configuration : CommonRoleLinearClock.Configuration) :
    (CommonRoleFiniteShadowHalting.goalOf configuration).argument.finite = true ∧
      Ready (visible code) (CommonRoleFiniteShadowHalting.goalOf configuration) :=
  ⟨rfl, finite_ready _ _ rfl⟩

def TotalFiniteShadowResolver (machine : Machine) : Prop :=
  ∀ code input, ∃ final,
    Runs machine (initial (queryWire code input)) final ∧
      (final.current = true ↔ Nonempty (Dictionary (visible code) (startGoal code input)))

theorem no_total_finite_shadow_resolver : ¬ ∃ machine : Machine, TotalFiniteShadowResolver machine := by
  rintro ⟨machine, classifies⟩
  apply CommonRoleComputation.no_halting_classifier descriptor
  refine ⟨.seq queryCode (classifierCode machine), ?_⟩
  intro code input
  obtain ⟨final, executed, correct⟩ := classifies code input
  have halting : final.current = true ↔ Halts code input := correct.trans (dictionary_exact code input)
  refine ⟨encodeBool final.current,
    .seq (eval_queryCode code input) (classifier_of_runs machine _ final executed), ?_⟩
  cases symbol : final.current <;>
    simpa only [symbol, encodeBool, CommonRoleTuringBridge.truth, IsNode, Bool.false_eq_true] using halting

/-- The extra K2 guard is inactive on all canonical finite configurations,
yet even the necessary success bit of a total exact resolver is impossible. -/
theorem finite_tree_registry_undecidable :
    (∀ code,
      CommonRoleRegularResolutionObstruction.checkEnvironment (environment code) = true ∧
      Roles.WellFormed (environment code).cores ∧
      HeadDeterminesAssociated (environment code) ∧ Roles.AssocWellFormed (environment code) roles) ∧
    (∀ code input, (startGoal code input).argument.finite = true ∧ Ready (visible code) (startGoal code input)) ∧
    ¬ ∃ machine : Machine, TotalFiniteShadowResolver machine := by
  refine ⟨?_, ?_, no_total_finite_shadow_resolver⟩
  · intro code
    refine ⟨CommonRoleFiniteShadowRegistry.environment_checked code, ?_,
      CommonRoleFiniteShadowRegistry.head_determines_associated code,
      CommonRoleFiniteShadowRegistry.associated_wellFormed code⟩
    rw [CommonRoleFiniteShadowRegistry.environment_cores]
    exact CommonRoleFiniteShadowRegistry.declarations_wellFormed code
  · intro code input
    exact ⟨rfl, finite_ready _ _ rfl⟩

end Yulang.CommonRoleFiniteShadowObstruction
