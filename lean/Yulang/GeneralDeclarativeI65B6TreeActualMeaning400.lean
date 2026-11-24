import Yulang.GeneralDeclarativeI65B6TreeReceipts400

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open GeneralDeclarativeWhere319 (Capture)
open CommonNominalFullCarrier (Ty Row nominal record variant)

private def centerValue400 (m : Model) (slots : Nat → Option Capture) (name : Nat) : Option Ty :=
  (slots name).map fun c => (m.assignment c.center).1

private def centerRow400 (m : Model) (slots : Nat → Option Capture) (name : Nat) : Option Row :=
  (slots name).map fun c => (m.assignment c.center).2

mutual
/-- Read the actual type value on the model of this same event. A
bounded nominal slot retains its checked bounds in the *syntax*; to
read its actual value here use its original selected binder name,
never select a value from its lower or upper endpoint. -/
def actualTreeValue400 (m : Model) (slots : Nat → Option Capture) : SourceRhsCode394 → Option Ty
  | .variable _ center => some (m.assignment center).1
  | .record label payload tail => do
    pure (record label (← actualTreeValue400 m slots payload) (← actualTreeValue400 m slots tail))
  | .variant tag payload => (actualTreeValue400 m slots payload).map (variant tag)
  | .join first last => do
    pure (.union (← actualTreeValue400 m slots first) (← actualTreeValue400 m slots last))
  | .nominal ctor args => (actualTreeArgList400 m slots args).map (nominal ctor)

def actualTreeArg400 (m : Model) (slots : Nat → Option Capture) : SourceRhsArg394 → Option (Ty ⊕ Row)
  | .valueSlot binder _ => (centerValue400 m slots binder).map Sum.inl
  | .rowSlot binder _ => (centerRow400 m slots binder).map Sum.inr
  | .valueExpression child => (actualTreeValue400 m slots child).map Sum.inl

def actualTreeArgList400 (m : Model) (slots : Nat → Option Capture) :
    List SourceRhsArg394 → Option (List (Ty ⊕ Row))
  | [] => some []
  | first::rest => do pure ((← actualTreeArg400 m slots first) :: (← actualTreeArgList400 m slots rest))
end

mutual
/-- Independent actual-value interpretation of B6's original symbolic
tree in the same assignment, before B4 substitutes logical names. -/
def actualPlanValue400 (m : Model) (slots : Nat → Option Capture) {s c p} :
    B6ValuePlan398 s c p → Option Ty
  | .binder n => centerValue400 m slots n
  | .record label payload tail => do
    pure (record label (← actualPlanValue400 m slots payload) (← actualPlanValue400 m slots tail))
  | .variant tag payload => (actualPlanValue400 m slots payload).map (variant tag)
  | .join first last => do
    pure (.union (← actualPlanValue400 m slots first) (← actualPlanValue400 m slots last))
  | .declaredApp ctor _ _ _ args => (actualPlanArgs400 m slots args).map (nominal ctor)

def actualPlanArg400 (m : Model) (slots : Nat → Option Capture) {s c param p} :
    B6ArgPlan398 s c param p → Option (Ty ⊕ Row)
  | .valuePoint n _ _ => (centerValue400 m slots n).map Sum.inl
  | .valueInterval n _ _ => (centerValue400 m slots n).map Sum.inl
  | .rowPoint n _ _ => (centerRow400 m slots n).map Sum.inr
  | .rowInterval n _ _ => (centerRow400 m slots n).map Sum.inr
  | .valueTree _ _ term => (actualPlanValue400 m slots term).map Sum.inl

def actualPlanArgs400 (m : Model) (slots : Nat → Option Capture) {s c params ps} :
    B6ArgPlans398 s c params ps → Option (List (Ty ⊕ Row))
  | .nil => some []
  | .cons first rest => do pure ((← actualPlanArg400 m slots first) :: (← actualPlanArgs400 m slots rest))
end

/-- The exact B6 tree and the B4-substituted RHS read the same value
on any one supplied assignment. This is actual type-value meaning
of represented syntax; not subtype completeness or state retention. -/
theorem actual_tree_value_after_B6_substitution400 {s c p}
    (m : Model) (slots : Nat → Option Capture) (plan : B6ValuePlan398 s c p) :
    ∀ output : ExactRoleRhs398 p,
      instantiateB6Value398 slots plan = some output →
      actualTreeValue400 m slots output.val = actualPlanValue400 m slots plan := by
  refine B6ValuePlan398.rec
    (motive_1 := fun _ p plan => ∀ out : ExactRoleRhs398 p,
      instantiateB6Value398 slots plan = some out →
      actualTreeValue400 m slots out.val = actualPlanValue400 m slots plan)
    (motive_2 := fun _ _ p plan => ∀ out : ExactRoleArg398 p,
      instantiateB6Arg398 slots plan = some out →
      actualTreeArg400 m slots out.val = actualPlanArg400 m slots plan)
    (motive_3 := fun _ _ ps plan => ∀ out : ExactRoleArgs398 ps,
      instantiateB6Args398 slots plan = some out →
      actualTreeArgList400 m slots out.val = actualPlanArgs400 m slots plan)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ plan
  · intro ctx n out run
    cases read : slots n with
    | none => simp [instantiateB6Value398,read] at run
    | some bound =>
      simp [instantiateB6Value398,read] at run
      rw [← run]
      simp [actualTreeValue400,actualPlanValue400,centerValue400,read]
  · intro ctx p q l a b first last out run
    cases left : instantiateB6Value398 slots a with
    | none => simp [instantiateB6Value398,left] at run
    | some x =>
      cases right : instantiateB6Value398 slots b with
      | none => simp [instantiateB6Value398,left,right] at run
      | some y =>
        simp [instantiateB6Value398,left,right] at run
        rw [← run]
        simp [actualTreeValue400,actualPlanValue400,first x left,last y right]
  · intro ctx p tag payload ih out run
    cases read : instantiateB6Value398 slots payload with
    | none => simp [instantiateB6Value398,read] at run
    | some x =>
      simp [instantiateB6Value398,read] at run
      rw [← run]
      simp [actualTreeValue400,actualPlanValue400,ih x read]
  · intro ctx p q a b first last out run
    cases left : instantiateB6Value398 slots a with
    | none => simp [instantiateB6Value398,left] at run
    | some x =>
      cases right : instantiateB6Value398 slots b with
      | none => simp [instantiateB6Value398,left,right] at run
      | some y =>
        simp [instantiateB6Value398,left,right] at run
        rw [← run]
        simp [actualTreeValue400,actualPlanValue400,first x left,last y right]
  · intro params ctx ps name use declared table args ih out run
    cases read : instantiateB6Args398 slots args with
    | none => simp [instantiateB6Value398,read] at run
    | some x =>
      simp [instantiateB6Value398,read] at run
      rw [← run]
      simp [actualTreeValue400,actualPlanValue400,ih x read]
  · intro ctx param n kind mode out run
    cases read : slots n with
    | none => simp [instantiateB6Arg398,read] at run
    | some x =>
      simp [instantiateB6Arg398,read] at run
      rw [← run]
      rfl
  · intro ctx param n kind mode out run
    cases read : slots n with
    | none => simp [instantiateB6Arg398,read] at run
    | some x =>
      simp [instantiateB6Arg398,read] at run
      rw [← run]
      rfl
  · intro ctx param n kind mode out run
    cases read : slots n with
    | none => simp [instantiateB6Arg398,read] at run
    | some x =>
      simp [instantiateB6Arg398,read] at run
      rw [← run]
      rfl
  · intro ctx param n kind mode out run
    cases read : slots n with
    | none => simp [instantiateB6Arg398,read] at run
    | some x =>
      simp [instantiateB6Arg398,read] at run
      rw [← run]
      rfl
  · intro p ctx param kind notVar term ih out run
    cases read : instantiateB6Value398 slots term with
    | none => simp [instantiateB6Arg398,read] at run
    | some x =>
      simp [instantiateB6Arg398,read] at run
      rw [← run]
      simp [actualTreeArg400,actualPlanArg400,ih x read]
  · intro ctx out run
    simp [instantiateB6Args398] at run
    rw [← run]
    rfl
  · intro ctx param p params ps a b first last out run
    cases left : instantiateB6Arg398 slots a with
    | none => simp [instantiateB6Args398,left] at run
    | some x =>
      cases right : instantiateB6Args398 slots b with
      | none => simp [instantiateB6Args398,left,right] at run
      | some y =>
        simp [instantiateB6Args398,left,right] at run
        rw [← run]
        simp [actualTreeArgList400,actualPlanArgs400,first x left,last y right]

/-- The selected literal frame's exact retained B6 plan and typed
tree share one model and the same real lexical slots. No mixed tree
is converted to a flat vector or interpreted by a second assignment. -/
theorem retained_typed_output_same_model400 {s q f i}
    (out : TreeOutput400 (s := s) (q := q) f i) (m : Model) :
    match out.write with
    | .ordinary _ => True
    | .typed _ rhs =>
      ∃ plan : B6ValuePlan398 s false (GeneralDeclarationPatterns.normalize
          (GeneralDeclarativeOutputs320.bodyPattern out.body)),
        out.originalPlan = some plan ∧
        actualTreeValue400 m (f.slots out.body) rhs =
          actualPlanValue400 m (f.slots out.body) plan := by
  cases out with
  | mk body supplier written production =>
    cases production with
    | ordinary source => exact True.intro
    | typed plan inst replay fit proof =>
      exact ⟨plan,rfl,actual_tree_value_after_B6_substitution400 m (f.slots body) plan inst replay⟩

private theorem readyUsesLeft400 {s slots as bs} (ready : B6UsesFit398 s slots (as ++ bs)) :
    B6UsesFit398 s slots as :=
  fun _ used => ready _ (List.mem_append.mpr (.inl used))

private theorem readyUsesRight400 {s slots as bs} (ready : B6UsesFit398 s slots (as ++ bs)) :
    B6UsesFit398 s slots bs :=
  fun _ used => ready _ (List.mem_append.mpr (.inr used))

/-- Successful same-source kind input supplies every actual read.
Consequently the same-model theorem below does not relate two failed
evaluations. -/
theorem actual_B6_plan_value_exists400 {s c p}
    (m : Model) (slots : Nat → Option Capture) (plan : B6ValuePlan398 s c p)
    (ready : B6UsesFit398 s slots plan.needs) :
    ∃ value, actualPlanValue400 m slots plan = some value := by
  refine B6ValuePlan398.rec
    (motive_1 := fun _ _ plan => B6UsesFit398 s slots plan.needs →
      ∃ value, actualPlanValue400 m slots plan = some value)
    (motive_2 := fun _ _ _ plan => B6UsesFit398 s slots plan.needs →
      ∃ value, actualPlanArg400 m slots plan = some value)
    (motive_3 := fun _ _ _ plan => B6UsesFit398 s slots plan.needs →
      ∃ value, actualPlanArgs400 m slots plan = some value)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ plan ready
  · intro context name input
    obtain ⟨slot,read,_⟩ := input (name,.value) (by simp [B6ValuePlan398.needs])
    exact ⟨(m.assignment slot.center).1,by simp [actualPlanValue400,centerValue400,read]⟩
  · intro _ _ _ l _ _ left right input
    obtain ⟨a,readA⟩ := left (readyUsesLeft400 input)
    obtain ⟨b,readB⟩ := right (readyUsesRight400 input)
    exact ⟨record l a b,by simp [actualPlanValue400,readA,readB]⟩
  · intro _ _ tag _ next input
    obtain ⟨a,read⟩ := next input
    exact ⟨variant tag a,by simp [actualPlanValue400,read]⟩
  · intro _ _ _ _ _ left right input
    obtain ⟨a,readA⟩ := left (readyUsesLeft400 input)
    obtain ⟨b,readB⟩ := right (readyUsesRight400 input)
    exact ⟨.union a b,by simp [actualPlanValue400,readA,readB]⟩
  · intro _ _ _ name _ _ _ _ next input
    obtain ⟨a,read⟩ := next input
    exact ⟨nominal name a,by simp [actualPlanValue400,read]⟩
  · intro _ _ name _ _ input
    obtain ⟨slot,read,_⟩ := input (name,.value) (by simp [B6ArgPlan398.needs])
    exact ⟨.inl (m.assignment slot.center).1,by simp [actualPlanArg400,centerValue400,read]⟩
  · intro _ _ name _ _ input
    obtain ⟨slot,read,_⟩ := input (name,.value) (by simp [B6ArgPlan398.needs])
    exact ⟨.inl (m.assignment slot.center).1,by simp [actualPlanArg400,centerValue400,read]⟩
  · intro _ _ name _ _ input
    obtain ⟨slot,read,_⟩ := input (name,.row) (by simp [B6ArgPlan398.needs])
    exact ⟨.inr (m.assignment slot.center).2,by simp [actualPlanArg400,centerRow400,read]⟩
  · intro _ _ name _ _ input
    obtain ⟨slot,read,_⟩ := input (name,.row) (by simp [B6ArgPlan398.needs])
    exact ⟨.inr (m.assignment slot.center).2,by simp [actualPlanArg400,centerRow400,read]⟩
  · intro _ _ _ _ _ _ next input
    obtain ⟨a,read⟩ := next input
    exact ⟨.inl a,by simp [actualPlanArg400,read]⟩
  · intro _ _
    exact ⟨[],rfl⟩
  · intro _ _ _ _ _ _ _ left right input
    obtain ⟨a,readA⟩ := left (readyUsesLeft400 input)
    obtain ⟨b,readB⟩ := right (readyUsesRight400 input)
    exact ⟨a::b,by simp [actualPlanArgs400,readA,readB]⟩

/-- Exact B6 plan and typed receipt have an actual, identical type
value on every one supplied assignment. Invariant bounds remain
available in the receipt; this is not a finite subtype decision. -/
theorem retained_typed_output_actual_value400 {s q f i}
    (out : TreeOutput400 (s := s) (q := q) f i) (m : Model) :
    match out.write with
    | .ordinary _ => True
    | .typed _ rhs =>
      ∃ (plan : B6ValuePlan398 s false (GeneralDeclarationPatterns.normalize
          (GeneralDeclarativeOutputs320.bodyPattern out.body))) (value : Ty),
        out.originalPlan = some plan ∧
        actualTreeValue400 m (f.slots out.body) rhs = some value ∧
        actualPlanValue400 m (f.slots out.body) plan = some value := by
  cases out with
  | mk body supplier written production =>
    cases production with
    | ordinary source => exact True.intro
    | typed plan inst replay fit proof =>
      obtain ⟨value,read⟩ := actual_B6_plan_value_exists400 m (f.slots body) plan fit
      have same := actual_tree_value_after_B6_substitution400 m (f.slots body) plan inst replay
      exact ⟨plan,value,rfl,same.trans read,read⟩

/-- The actual equation pair (original target, same-model type value).
Application of an equality/subtyping judgment is a separate matter;
no uniform invariant comparison is substituted for declared modes. -/
def TreeOutput400.actualEquation400 {s q f i}
    (o : TreeOutput400 (s := s) (q := q) f i) (m : Model) : Option (Nat × Ty) :=
  match o.write with
  | .ordinary _ => none
  | .typed target rhs => (actualTreeValue400 m (f.slots o.body) rhs).map fun value => (target,value)

theorem typed_fixed_equation_matches_B6_value400 {s q f i}
    (o : TreeOutput400 (s := s) (q := q) f i) (m : Model) :
    match o.write with
    | .ordinary _ => True
    | .typed _ _ =>
      ∃ (plan : B6ValuePlan398 s false (GeneralDeclarationPatterns.normalize
            (GeneralDeclarativeOutputs320.bodyPattern o.body))) (value : Ty),
        o.originalPlan = some plan ∧
        o.actualEquation400 m = some (q.demand.outputs[i].target,value) ∧
        actualPlanValue400 m (f.slots o.body) plan = some value := by
  cases o with
  | mk body supplier written source =>
    cases source with
    | ordinary original => exact True.intro
    | typed plan inst replay kinds meaning =>
      obtain ⟨value,read⟩ := actual_B6_plan_value_exists400 m (f.slots body) plan kinds
      have applied := (actual_tree_value_after_B6_substitution400 m (f.slots body) plan inst replay).trans read
      exact ⟨plan,value,rfl,by
        simp only [TreeOutput400.actualEquation400,applied,Option.map_some],read⟩

/-- Equal interval syntax does not authorize choosing another frame.
The bounds are carried in the type syntax, but the actual value of
that slot is read at the original event's retained center. -/
theorem same_interval_syntax_can_read_different_centers400
    (m : Model) (first last : Nat → Option Capture) (binder : Nat)
    (bounds : CommonRecursiveNominalIntervals.Bounds (CommonRecursiveNominalIntervals.Endpoint Nat))
    {a b : Capture} (atFirst : first binder = some a) (atLast : last binder = some b)
    (actualTypesDiffer : (m.assignment a.center).1 ≠ (m.assignment b.center).1) :
    actualTreeArg400 m first (.valueSlot binder bounds) ≠
      actualTreeArg400 m last (.valueSlot binder bounds) := by
  simpa [actualTreeArg400,centerValue400,atFirst,atLast] using actualTypesDiffer

end Yulang.GeneralDeclarativeI65
