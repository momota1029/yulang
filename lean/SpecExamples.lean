import Yulang.CommonRoleStablePaterson
import Yulang.CommonDeclarationVarianceExamples
import Yulang.CommonOptionalFieldBoundary
import Yulang.CommonAlignedPatternGeneration
import Yulang.CommonRoleNormalizedDeclarations
import Yulang.CommonRoleFiniteShadowExamples

/-!
# Specification conformance cases

The IDs and expected outcomes are from
`notes/handoff/2026-11-08-m1-spec-examples-conformance.md`. These are checks of
the current outermost available components, not `Core.infer` integration.

* X1 PROVED: `x1_declaration_accepted` checks the list constructor declaration.
* X2 PROVED: `x2_declaration_rejected` checks the list constructor declaration.
* X3 PROVED: `x3_shadow_rejected` checks the normalized record declaration.
* X4 NOT-EXPRESSIBLE-YET: no source record-tail scheduler and resolver.
* X5 PROVED: `x5_rejected` uses the stable declaration checker.
* X6 NOT-EXPRESSIBLE-YET: the interval candidate scanner lacks merged-variable heads.
* X7 NOT-EXPRESSIBLE-YET: no associated-type declaration checker for record heads.
* X8 NOT-EXPRESSIBLE-YET: no whole resolver for nominal lists and regular types.
* X9 NOT-EXPRESSIBLE-YET: no whole resolver for nominal lists and regular types.
* X10 NOT-EXPRESSIBLE-YET: no whole resolver inspecting regular record heads.
* X11 NOT-EXPRESSIBLE-YET: no whole resolver with K2 rejection priority.
* X12 NOT-EXPRESSIBLE-YET: no whole resolver for named recursive nominal types.
* X13 NOT-EXPRESSIBLE-YET: no source bound collector and co-occurrence simplifier.
* X14 NOT-EXPRESSIBLE-YET: the recursive nominal compiler's `TyTerm` has no
  float constructor, and the source interval merger/solver pipeline is absent.
* X15 NOT-EXPRESSIBLE-YET: no interval-to-constructor simplifier.
* X16 NOT-EXPRESSIBLE-YET: no interval-to-constructor simplifier.
* X17 NOT-EXPRESSIBLE-YET: no source interval simplifier for function positions.
* X18 PROVED: `x18_box_covariant`, `x18_box2_covariant`, `x18_reset_covariant`,
  and `x18_stream_covariant` evaluate the declaration-derived table.
* X19 PROVED: `x19_chain_invariant` and `x19_mutual_invariant` evaluate that table.
* X20 PROVED: `x20_phantom_unused` uses the actual derived variance table.
* X21 NOT-EXPRESSIBLE-YET: rank-2 field lowering lacks the actual `sub` source body.
* X22 MISMATCH: `x22_strict_rejects` and `x22_missing_field_misses`;
  the separately modeled optional rule is not integrated into the main generator.
* X23 NOT-EXPRESSIBLE-YET: no complete source static-effect-row generator.
* X24 NOT-EXPRESSIBLE-YET: no source pipe/catch lowering and handler execution bridge.
-/

namespace Yulang.SpecExamples

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

open CommonDeclarationVarianceExamples
open CommonDeclarationVarianceTable
open CommonDeclarationVarianceLowering
open CommonNominalFieldTemplates (Body)
open CommonRoleStablePaterson

/-- `list` is constructor 0 and the role is 0; variable 0 is `'a`. -/
def x1DisplayList : Roles.Impl :=
  ⟨0, [.app 0 [.var 0]], [⟨0, [.var 0]⟩], 0⟩

theorem x1_declaration_accepted : CheckedRoles.checkImpl x1DisplayList = true := by decide +kernel

/-- `Foo 'a` with prerequisite `Foo (list 'a)`. -/
def x2GrowingList : Roles.Impl :=
  ⟨0, [.var 0], [⟨0, [.app 0 [.var 0]]⟩], 0⟩

theorem x2_declaration_rejected : CheckedRoles.checkImpl x2GrowingList = false := by decide +kernel

/-- The first-field-wins record normalization runs before the declaration check. -/
theorem x3_shadow_rejected :
    CommonRoleNormalizedDeclarations.checkImpl CommonRoleFiniteShadowExamples.loopImpl = false := by
  decide +kernel

/-- X5: the repeated `tick` payload merges after `'a := int`. -/
theorem x5_rejected : check previousExample = false := by decide +kernel

/-- X18: `box 'a { value: 'a }`, from the declaration body. -/
def specBoxBody : Fin 1 → Body 1 1 0 := fun _ => .record 0 (.inr 0) .emptyRecord
def specBox := fromBodies specBoxBody (fun _ => 0) oneHeader

theorem x18_box_covariant :
    LoweringVerified specBoxBody (fun _ => 0) oneHeader ∧
      deriveVariance specBox (pool 1 1) = [(0, .covariant)] := by
  unfold LoweringVerified
  decide

/-- X18: `reset 'a = value 'a | next (reset int)`. -/
def specResetBody : Fin 3 → Body 3 1 0 := fun index =>
  if index = 0 then .union (.variant 0 (.inr 0)) (.variant 1 (.inl 1))
  else if index = 1 then .nominal 0 [.inl (.inl 2)] else .base .int
def specReset := fromBodies specResetBody (fun _ => 0) oneHeader

theorem x18_reset_covariant :
    LoweringVerified specResetBody (fun _ => 0) oneHeader ∧
      deriveVariance specReset (pool 3 1) = [(0, .covariant)] := by
  unfold LoweringVerified
  decide

/-- X19: `chain 'a = end | link 'a (chain 'a)`. -/
def specChainBody : Fin 4 → Body 4 1 0 := fun index =>
  if index = 0 then .union (.variant 0 (.inl 1)) (.variant 1 (.inl 2))
  else if index = 1 then .base .unit
  else if index = 2 then .pair (.inr 0) (.inl 3)
  else .nominal 0 [.inl (.inr 0)]
def specChain := fromBodies specChainBody (fun _ => 0) oneHeader

theorem x19_chain_invariant :
    LoweringVerified specChainBody (fun _ => 0) oneHeader ∧
      deriveVariance specChain (pool 4 1) = [(0, .invariant)] := by
  unfold LoweringVerified
  decide

/-- `box 'a` and `box2 'b { value: box (box 'b) }`, with separate slots. -/
def box2Bodies : Fin 4 → Body 4 2 0 := fun index =>
  if index = 0 then .record 0 (.inr 0) .emptyRecord
  else if index = 1 then .record 0 (.inl 2) .emptyRecord
  else if index = 2 then .nominal 0 [.inl (.inl 3)]
  else .nominal 0 [.inl (.inr 1)]

def box2Roots : Fin 2 → Fin 4 := fun parameter => if parameter = 0 then 0 else 1
def box2Program := fromBodies box2Bodies box2Roots twoHeaders

theorem x18_box2_covariant :
    LoweringVerified box2Bodies box2Roots twoHeaders ∧
      deriveVariance box2Program (pool 4 2) = [(0, .covariant), (1, .covariant)] := by
  unfold LoweringVerified
  decide

/-- `stream 'a { next: () -> ('a, stream 'a) }`. -/
def streamBodies : Fin 5 → Body 5 1 0 := fun index =>
  if index = 0 then .record 0 (.inl 1) .emptyRecord
  else if index = 1 then .arrow (.inl 2) .empty (.inl 3) .empty
  else if index = 2 then .base .unit
  else if index = 3 then .pair (.inr 0) (.inl 4)
  else .nominal 0 [.inl (.inr 0)]

def streamProgram := fromBodies streamBodies (fun _ => 0) oneHeader

theorem x18_stream_covariant :
    LoweringVerified streamBodies (fun _ => 0) oneHeader ∧
      deriveVariance streamProgram (pool 5 1) = [(0, .covariant)] := by
  unfold LoweringVerified
  decide

/-- `left 'a = value 'a | next (right 'a)`; `right 'b = next (left 'b)`. -/
def mutualBodies : Fin 4 → Body 4 2 0 := fun index =>
  if index = 0 then .union (.variant 0 (.inr 0)) (.variant 1 (.inl 2))
  else if index = 1 then .variant 1 (.inl 3)
  else if index = 2 then .nominal 1 [.inl (.inr 0)]
  else .nominal 0 [.inl (.inr 1)]

def mutualRoots : Fin 2 → Fin 4 := fun parameter => if parameter = 0 then 0 else 1
def mutualProgram := fromBodies mutualBodies mutualRoots twoHeaders

theorem x19_mutual_invariant :
    LoweringVerified mutualBodies mutualRoots twoHeaders ∧
      deriveVariance mutualProgram (pool 4 2) = [(0, .invariant), (1, .invariant)] := by
  unfold LoweringVerified
  decide

/-- X20: `phantom 'a = end | next (phantom 'a)`. -/
def specPhantomBody : Fin 3 → Body 3 1 0 := fun index =>
  if index = 0 then .union (.variant 0 (.inl 1)) (.variant 1 (.inl 2))
  else if index = 1 then .base .unit else .nominal 0 [.inl (.inr 0)]
def specPhantom := fromBodies specPhantomBody (fun _ => 0) oneHeader

theorem x20_phantom_unused :
    LoweringVerified specPhantomBody (fun _ => 0) oneHeader ∧
      deriveVariance specPhantom (pool 3 1) = [(0, .unused)] := by
  unfold LoweringVerified
  decide

/-- X22: the main aligned pattern typing rejects the optional input. -/
theorem x22_strict_rejects
    (defaults : CommonPatternEnvironment.NamedTypes → D → Common.Ty → Prop)
    (types bindings : CommonPatternEnvironment.NamedTypes) :
    ¬ CommonAlignedPatternTyping.RawTyping defaults types
      CommonOptionalFieldBoundary.pattern CommonOptionalFieldBoundary.subject bindings :=
  CommonOptionalFieldBoundary.strict_rejects defaults types bindings

/-- X22: the actual main generator has no model for this optional input. -/
theorem x22_main_generator_rejects :
    ¬ (CommonAlignedPatternGeneration.generatePattern
      (CommonOptionalFieldBoundary.pattern : CasePatterns.Pattern Empty Inference.Expr)
      [] [] (.var 0) [(0, .var 1)]).Holds Common.model CommonOptionalFieldBoundary.assignment := by
  intro model
  have typed := (CommonAlignedPatternGeneration.generatePattern_exact
    (CommonOptionalFieldBoundary.pattern : CasePatterns.Pattern Empty Inference.Expr)
    CommonOptionalFieldBoundary.assignment [] []
    (Core.PresenceGeneration.EnvRel.nil Common.model CommonOptionalFieldBoundary.assignment)
    [] (.var 0) [(0, .var 1)]).mp model
  exact CommonOptionalFieldBoundary.strict_rejects _ _ _ typed

/-- X22: with the same pattern, an absent field takes the actual miss branch. -/
theorem x22_missing_field_misses (floatCheck : Empty → Empty → Bool)
    (defaultEval : CaseValues.Bindings Empty → D →
      EvaluationTrace.Logged E R (CaseValues.Value Empty))
    (environment : CaseValues.Bindings Empty) :
    ScopedCasePatterns.run floatCheck defaultEval environment CommonOptionalFieldBoundary.pattern
      (.record []) = EvaluationTrace.Logged.ofResult (.ok none) :=
  CommonOptionalFieldBoundary.actual_empty_miss floatCheck defaultEval environment

end Yulang.SpecExamples
