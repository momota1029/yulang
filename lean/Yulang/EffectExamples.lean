import Yulang.Effects

/-!
Executable witnesses for the scoped effect kernel. The computation examples are
explicit elaborated witnesses, not a proved translation of the surface examples
in `spec/05-effects.md`. All equalities are kernel-checked reductions or proofs;
no native evaluator is trusted.
-/

namespace Yulang.Effects.Examples

abbrev Key := EffectKey Nat Nat

def subKey : Key := ⟨0, [0]⟩
def ioKey : Key := ⟨1, []⟩
def undetKey : Key := ⟨2, []⟩

def visible (key : Key) : Occurrence Key := ⟨key, []⟩
def guarded (scope : Nat) (key : Key) : Occurrence Key := ⟨key, [scope]⟩

def firstOperation : OperationKey Nat Nat Nat := ⟨3, 0, [7]⟩
def secondOperation : OperationKey Nat Nat Nat := ⟨3, 1, [7]⟩

theorem operations_share_parameterized_family :
    firstOperation.toEffectKey = secondOperation.toEffectKey := rfl

/-- Handling one operation does not remove another operation of the same family. -/
theorem incomplete_operation_coverage_preserves_residual :
    residual [firstOperation]
      [⟨firstOperation, []⟩, ⟨secondOperation, []⟩] = [⟨secondOperation, []⟩] := by
  decide

/-- Family type arguments participate in identity; same path is insufficient. -/
theorem different_arguments_not_captured :
    residual [⟨3, [0]⟩] [visible ⟨3, [1]⟩] = [visible ⟨3, [1]⟩] := by
  decide

theorem concrete_head_does_not_consume_same_family_tail :
    residual [ioKey] [visible ioKey, guarded 7 ioKey] = [guarded 7 ioKey] := by
  decide

theorem selective_permission_preserves_other_effects :
    residual [ioKey, undetKey]
      (protect 7 (fun key => decide (key = ioKey))
        [visible ioKey, visible undetKey, guarded 8 ioKey]) =
      [guarded 7 undetKey, guarded 8 ioKey] := by
  decide

/-- Granting all families at a new input boundary is not an output release. -/
theorem glob_is_not_release :
    protect 8 allowAll [guarded 7 ioKey] ≠ release 7 [guarded 7 ioKey] := by
  decide

theorem release_is_local :
    release 8 [⟨ioKey, [8, 7]⟩] = [guarded 7 ioKey] := by
  decide

theorem release_preserves_repeated_activation :
    residual [ioKey] (release 7 [⟨ioKey, [7, 7]⟩]) = [guarded 7 ioKey] := by
  decide

/-- Without freshness, release could erase a pre-existing permitted-key barrier. -/
theorem freshness_is_necessary :
    release 7 (protect 7 allowAll [guarded 7 ioKey]) ≠ [guarded 7 ioKey] := by
  decide

def environment : Nat → Row Key := fun _ => [visible ioKey, visible undetKey]

def protectedTail : RowExpr Nat Key := .protect 7 allowNone (.var 0)

/-- Releasing one occurrence of 'e does not mutate another occurrence of 'e. -/
theorem shared_variable_has_independent_slots :
    RowExpr.eval environment (.union protectedTail (.release 7 protectedTail)) =
      [guarded 7 ioKey, guarded 7 undetKey, visible ioKey, visible undetKey] := by
  decide

abbrev Program := Computation Key Nat Unit Nat

def signal (value : Nat) (next : Program) : Program :=
  .request (visible subKey) value (fun _ => next)

def subHandler (body : Program) : Program :=
  body.shallowHandle [subKey] Computation.pure
    (fun _ payload _ => .pure payload)

def callback : Program := signal 0 (.pure 99)

/-- The callback's effect enters g protected; g's own return is visible. -/
def innerG : Program :=
  subHandler ((callback.mapRequests (protectOccurrence 7 allowNone)).bind
    (fun _ => signal 1 (.pure 99)))

/-- Only the matching g-boundary is released before reaching the outer handler. -/
def nestedSub : Program :=
  subHandler ((innerG.mapRequests (releaseOccurrence 7)).bind
    (fun _ => signal 2 (.pure 99)))

theorem nested_sub_returns_zero : nestedSub = .pure 0 := by
  rfl

/-- Erasing the callback barrier changes the observable answer from 0 to 2. -/
def unprotectedNestedSub : Program :=
  subHandler ((subHandler (callback.bind (fun _ => signal 1 (.pure 99)))).bind
    (fun _ => signal 2 (.pure 99)))

theorem erased_protection_returns_two : unprotectedNestedSub = .pure 2 := by
  rfl

theorem erasing_protection_changes_result : nestedSub ≠ unprotectedNestedSub := by
  rw [nested_sub_returns_zero, erased_protection_returns_two]
  intro impossible
  cases impossible

def twoSignals : Program := signal 1 (signal 2 (.pure 3))

def resumeOnce (body : Program) : Program :=
  body.shallowHandle [subKey] Computation.pure
    (fun _ _ continuation => continuation ())

theorem shallow_resume_leaves_second_operation :
    resumeOnce twoSignals = signal 2 (.pure 3) := by
  rfl

theorem explicit_rehandling_consumes_second_operation :
    resumeOnce (resumeOnce twoSignals) = .pure 3 := by
  rfl

/-- The continuation is an ordinary reusable function, with no linearity rule. -/
def resumeTwice (body : Program) : Program :=
  body.shallowHandle [subKey] Computation.pure
    (fun _ _ continuation => (continuation ()).bind
      (fun first => (continuation ()).bind (fun second => .pure (first + second))))

theorem multishot_resumption : resumeTwice (signal 1 (.pure 3)) = .pure 6 := by
  rfl

/-- Effects introduced by an operation arm are outside that handler. -/
theorem operation_arm_is_not_implicitly_handled :
    Computation.shallowHandle [subKey] Computation.pure
      (fun _ _ _ => signal 4 (.pure 5)) (signal 1 (.pure 3)) =
        signal 4 (.pure 5) := by
  rfl

end Yulang.Effects.Examples
