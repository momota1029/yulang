import Yulang.CommonRoleFiniteTailHalting

/-! E2 under normalized Paterson checking and both K2 rejection rules.
The inputs are actual finite core declarations, not a claim of source
annotation reachability. Every stored declaration is already N-normal. -/
namespace Yulang.CommonRoleFiniteTailObstruction

open CommonRoleComputation (Code Tree Eval Halts IsNode)
open CommonRoleInspectedSemantics
open CommonRoleFiniteTailClock (clock count)
open CommonRoleFiniteTailRegistry (visible environment roles)
open CommonRoleFiniteTailHalting (startGoal dictionary_exact)
open CommonRoleFiniteShadowObstruction (descriptionWire goalWire signatures signature_actual)
open CommonRoleRegularWire (groundWire listWire assocImplWire Signature taggedCode eval_taggedCode)
open CommonRoleTuringBridge (Machine Runs encodeNat encodeBool project eval_project)
open CommonRoleTuringDelimited (initial classifierCode classifier_of_runs)

attribute [local irreducible] count

def databaseWire (code : Code) : Tree :=
  .node (listWire assocImplWire (environment code).impls) (listWire Signature.wire signatures)

def descriptor (code : Code) : Tree :=
  .node (databaseWire code) (.node (descriptionWire (clock (count code))) (groundWire code.encode))

def queryWire (code : Code) (input : Tree) : Tree :=
  .node (databaseWire code) (goalWire (startGoal code input))

def queryCode : Code :=
  .pair (project [false, false])
    (.pair (.const (encodeNat 1))
      (taggedCode 2 (.pair (project [false, true, false])
        (taggedCode 2 (.pair (taggedCode 1 (project [false, true, true]))
          (taggedCode 2 (.pair (taggedCode 0 .right)
            (taggedCode 1 (.const (groundWire CommonRoleLinearInterpreter.Kont.halt.encode))))))))))

theorem eval_queryCode (code : Code) (input : Tree) :
    Eval queryCode (.node (descriptor code) input) (queryWire code input) := by
  apply Eval.pair
  · exact eval_project [false, false] _
  · apply Eval.pair (.const _ _)
    apply eval_taggedCode
    apply Eval.pair
    · exact eval_project [false, true, false] _
    · apply eval_taggedCode
      apply Eval.pair
      · exact eval_taggedCode 1 (eval_project [false, true, true] _)
      · apply eval_taggedCode
        apply Eval.pair
        · exact eval_taggedCode 0 (.rightNode _ _)
        · exact eval_taggedCode 1 (.const _ _)

theorem queryCode_exact (code : Code) (input output : Tree) :
    Eval queryCode (.node (descriptor code) input) output ↔ output = queryWire code input :=
  ⟨fun evaluation => evaluation.deterministic (eval_queryCode code input), fun same => same ▸ eval_queryCode code input⟩

theorem configuration_ready (code : Code) (configuration : CommonRoleLinearClock.Configuration) :
    (CommonRoleFiniteTailHalting.goalOf code configuration).argument.finite = true ∧
      Ready (visible code) (CommonRoleFiniteTailHalting.goalOf code configuration) := by
  have finite : (CommonRoleFiniteTailHalting.goalOf code configuration).argument.finite = true := by
    simp [CommonRoleFiniteTailHalting.goalOf, CommonRoleFiniteTailHalting.dataGoal,
      CommonRoleFiniteTailRegistry.pairGoal, Description.finite, CommonRoleFiniteTailClock.clock_finite]
  exact ⟨finite, finite_ready _ _ finite⟩

def TotalNormalizedResolver (machine : Machine) : Prop :=
  ∀ code input, ∃ final, Runs machine (initial (queryWire code input)) final ∧
    (final.current = true ↔ Nonempty (Dictionary (visible code) (startGoal code input)))

theorem no_total_normalized_resolver : ¬ ∃ machine : Machine, TotalNormalizedResolver machine := by
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

theorem normalized_registry_undecidable :
    (∀ code, CommonRoleNormalizedDeclarations.checkEnvironment (environment code) = true ∧
      CommonRoleNormalizedDeclarations.NormalizedWellFormed (environment code).cores ∧
      CommonRoleFiniteShadowRegistry.HeadDeterminesAssociated (environment code) ∧
      Roles.AssocWellFormed (environment code) roles ∧
      ∀ implementation ∈ visible code, CommonRoleNormalizedDeclarations.normalizeImpl implementation = implementation) ∧
    (∀ code input, (startGoal code input).argument.finite = true ∧ Ready (visible code) (startGoal code input)) ∧
    ¬ ∃ machine : Machine, TotalNormalizedResolver machine := by
  refine ⟨?_, ?_, no_total_normalized_resolver⟩
  · intro code
    exact ⟨CommonRoleFiniteTailRegistry.environment_checked code,
      CommonRoleFiniteTailRegistry.normalized_wellFormed code,
      CommonRoleFiniteTailRegistry.head_determines_associated code,
      CommonRoleFiniteTailRegistry.associated_wellFormed code,
      CommonRoleFiniteTailRegistry.declarations_normal code⟩
  · intro code input
    have finite := CommonRoleFiniteTailHalting.start_finite code input
    exact ⟨finite, finite_ready _ _ finite⟩

end Yulang.CommonRoleFiniteTailObstruction
