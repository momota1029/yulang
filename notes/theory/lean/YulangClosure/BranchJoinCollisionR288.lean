import YulangClosure.OriginalSourceGeneration

/-!
A syntactic collision in the current candidate source-rule generator.

SG §3.1 requires original ordered branch/handler laws. The source inventory
and the corrected source-core action coverage §3--4 distinguish value and
operation attempts. This module examines only the generated root branchJoin
Atom. It does not identify whole source trees, environments, denotations or
operational behavior; it supplies no original local semantic law.
-/
namespace YulangClosure.BranchJoinCollisionR288

open OriginalSource

/-- Inspect the actual Catch root premises, leaving all other trees alone. -/
def generatedJoin (context : Context) (source : Source .expression) : Option Atom :=
  match sourceRules context source with
  | .rule .catchE _ _ localPremises _ =>
      localPremises.findSome? (fun premise => match premise with
        | .atom a => if a.kind == .branchJoin then some a else none
        | _ => none)
  | _ => none

def valueCatch (parent armSite : Site) (scrutinee body : Source .expression)
    (pattern : Source .pattern) : Source .expression :=
  .catchE ⟨parent, none⟩ scrutinee
    (.arm armSite pattern .noExpression body .armsNil) .operationArmsNil [armSite]

def operationCatch (parent armSite : Site) (scrutinee body : Source .expression)
    (operation : Declaration) (rigids : Nat) (payload continuation : Source .pattern) :
    Source .expression :=
  .catchE ⟨parent, none⟩ scrutinee .armsNil
    (.operationArm armSite operation rigids payload continuation .noExpression body
      .operationArmsNil) [armSite]

def sharedJoin (context : Context) (parent armSite : Site)
    (scrutinee body : Source .expression) : Atom :=
  { (atom .branchJoin parent context [scrutinee.site, body.site]) with order := [armSite] }

/-- This observable reads the original source arm partition, not generated IDs. -/
def hasValueArm : Source .expression → Bool
  | .catchE _ _ (.arm ..) _ _ => true
  | _ => false

variable (context : Context) (parent armSite : Site)
  (scrutinee body : Source .expression) (pattern : Source .pattern)
  (operation : Declaration) (rigids : Nat) (payload continuation : Source .pattern)

theorem value_generated :
    generatedJoin context (valueCatch parent armSite scrutinee body pattern) =
      some (sharedJoin context parent armSite scrutinee body) := by
  simp [generatedJoin, valueCatch, sourceRules, sharedJoin, Source.roots]
  rfl

theorem operation_generated :
    generatedJoin context
      (operationCatch parent armSite scrutinee body operation rigids payload continuation) =
      some (sharedJoin context parent armSite scrutinee body) := by
  simp [generatedJoin, operationCatch, sourceRules, sharedJoin, Source.roots]
  rfl

/-- Full Atom equality: all fields, including context, operands and order. -/
theorem collision :
    generatedJoin context (valueCatch parent armSite scrutinee body pattern) =
      generatedJoin context
        (operationCatch parent armSite scrutinee body operation rigids payload continuation) := by
  rw [value_generated, operation_generated]

theorem distinct_arm_kind :
    hasValueArm (valueCatch parent armSite scrutinee body pattern) = true ∧
    hasValueArm
      (operationCatch parent armSite scrutinee body operation rigids payload continuation) = false :=
  ⟨rfl, rfl⟩

theorem distinct_sources :
    valueCatch parent armSite scrutinee body pattern ≠
      operationCatch parent armSite scrutinee body operation rigids payload continuation := by
  intro same
  have observed := congrArg hasValueArm same
  exact Bool.noConfusion observed

/-- The entire generated tree still retains different child structure. -/
theorem distinct_generated_trees :
    sourceRules context (valueCatch parent armSite scrutinee body pattern) ≠
      sourceRules context
        (operationCatch parent armSite scrutinee body operation rigids payload continuation) := by
  intro same
  simp only [valueCatch, operationCatch, sourceRules] at same
  cases same

include parent armSite scrutinee body pattern operation rigids payload continuation in
/-- No decoder of this Atom projection alone can recover the source partition.
This quantifies over the full existing Source expression type. -/
theorem no_join_only_decoder :
    ¬ ∃ recover : Option Atom → Bool,
      ∀ source : Source .expression, recover (generatedJoin context source) = hasValueArm source := by
  rintro ⟨recover, correct⟩
  have first := correct (valueCatch parent armSite scrutinee body pattern)
  have second := correct
    (operationCatch parent armSite scrutinee body operation rigids payload continuation)
  have equalInput := congrArg recover
    (collision context parent armSite scrutinee body pattern operation rigids payload continuation)
  rw [first, second] at equalInput
  exact Bool.noConfusion equalInput

/-- The actual Kernel.atom consumer receives the same question at any one
chosen environment. No equality between two environments is assumed. -/
theorem consumer_same_question {Value : Type} (kernel : Kernel Value)
    (environment : Environment Value) :
    (∃ a, generatedJoin context (valueCatch parent armSite scrutinee body pattern) = some a ∧
      kernel.atom environment a) ↔
    (∃ a, generatedJoin context
        (operationCatch parent armSite scrutinee body operation rigids payload continuation) = some a ∧
      kernel.atom environment a) := by
  rw [collision context parent armSite scrutinee body pattern operation rigids payload continuation]

/-- Explicit finite original-source witnesses; no opaque source existence. -/
def concreteValue : Source .expression :=
  valueCatch 10 30 (.literal ⟨20, none⟩ .unit) (.literal ⟨40, none⟩ .unit) (.wild 31)

def concreteOperation : Source .expression :=
  operationCatch 10 30 (.literal ⟨20, none⟩ .unit) (.literal ⟨40, none⟩ .unit)
    7 0 (.wild 31) (.varPattern 32 8)

theorem concrete_collision :
    concreteValue ≠ concreteOperation ∧
    hasValueArm concreteValue = true ∧ hasValueArm concreteOperation = false ∧
    generatedJoin [] concreteValue = generatedJoin [] concreteOperation ∧
    generatedJoin [] concreteValue =
      some { (atom .branchJoin 10 [] [20, 40]) with order := [30] } := by
  refine ⟨distinct_sources 10 30 _ _ _ 7 0 _ _, rfl, rfl, ?_, ?_⟩
  · exact collision [] 10 30 _ _ _ 7 0 _ _
  · exact value_generated [] 10 30 _ _ _

end YulangClosure.BranchJoinCollisionR288
