import Std

/-!
Record-boundary component of the existing whole-language research manuscript.
The compiler below checks every common payload, including optional fields;
execution reads only the incoming visible view and visits target fields in order.
The normal-result theorem has an independent child-cast preservation premise.
It does not assert request/resumption safety, native elaboration, or whole-source
inference soundness. In particular, direct checking is not made transitive.
-/

namespace YulangClosure.RecordBoundary

inductive Aligned {Left Right : Type} (rel : Left → Right → Prop) :
    List Left → List Right → Prop where
  | nil : Aligned rel [] []
  | cons : rel left right → Aligned rel lefts rights →
      Aligned rel (left :: lefts) (right :: rights)

structure Spec (Ty : Type) where
  ty : Ty
  optional : Bool
  deriving DecidableEq, Repr

abbrev Field (Ty : Type) := Nat × Spec Ty
abbrev Signature (Ty : Type) := Nat → Option (Spec Ty)
abbrev View (Value : Type) := Nat → Option Value

def signature (fields : List (Field Ty)) : Signature Ty := fun label =>
  match fields with
  | [] => none
  | (name, spec) :: tail => if label = name then some spec else signature tail label

def visible (slots : List (Nat × Option Value)) : View Value := fun label =>
  match slots with
  | [] => none
  | (name, value) :: tail => if label = name then value else visible tail label

def SlotTyped (typed : Value → Ty → Prop) (spec : Spec Ty) : Option Value → Prop
  | none => spec.optional = true
  | some value => typed value spec.ty

/-- Independent visible-record meaning: required fields exist; all present
payloads have their declared types; undeclared fields are hidden. -/
def ViewTyped (typed : Value → Ty → Prop) (source : Signature Ty)
    (input : View Value) : Prop :=
  ∀ label, match source label with
    | none => input label = none
    | some spec => SlotTyped typed spec (input label)

def PresenceValid (known : Nat → Bool) (input : View Value) : Prop :=
  ∀ label, known label = true → ∃ value, input label = some value

inductive FieldPlan (Ty Cast : Type) where
  | absent (target : Field Ty)
  | convert (target : Field Ty) (source : Spec Ty) (cast : Cast)
  deriving DecidableEq, Repr

def FieldPlan.target : FieldPlan Ty Cast → Field Ty
  | .absent target => target
  | .convert target _ _ => target

def FieldPlan.Valid (source : Signature Ty) (known : Nat → Bool)
    (resolve : Ty → Ty → Option Cast) : FieldPlan Ty Cast → Prop
  | .absent (label, target) => source label = none ∧ target.optional = true
  | .convert (label, target) origin cast =>
      source label = some origin ∧
      (origin.optional = false ∨ target.optional = true ∨ known label = true) ∧
      resolve origin.ty target.ty = some cast

/-- The optional-to-required case needs a genuine presence witness. With
`known := fun _ => false` this is the current native dispatch's static rule. -/
def compileField (source : Signature Ty) (known : Nat → Bool)
    (resolve : Ty → Ty → Option Cast) (target : Field Ty) : Option (FieldPlan Ty Cast) :=
  match source target.1 with
  | none =>
      if target.2.optional = true then some (.absent target) else none
  | some origin =>
      if origin.optional = false ∨ target.2.optional = true ∨ known target.1 = true then
        (resolve origin.ty target.2.ty).map (FieldPlan.convert target origin)
      else none

def compile (source : Signature Ty) (known : Nat → Bool)
    (resolve : Ty → Ty → Option Cast) : List (Field Ty) → Option (List (FieldPlan Ty Cast))
  | [] => some []
  | target :: tail => do
      let entry ← compileField source known resolve target
      let rest ← compile source known resolve tail
      pure (entry :: rest)

def ValidPlan (source : Signature Ty) (known : Nat → Bool)
    (resolve : Ty → Ty → Option Cast) (targets : List (Field Ty))
    (plan : List (FieldPlan Ty Cast)) : Prop :=
  Aligned (fun target entry => entry.target = target ∧
    entry.Valid source known resolve) targets plan

theorem compileField_sound
    (h : compileField source known resolve target = some entry) :
    entry.target = target ∧ entry.Valid source known resolve := by
  unfold compileField at h
  split at h
  next hs =>
    split at h
    next optional =>
      cases h
      exact ⟨rfl, hs, optional⟩
    next => contradiction
  next origin hs =>
    split at h
    next presence =>
      cases hr : resolve origin.ty target.2.ty with
      | none => simp [hr] at h
      | some cast =>
          simp only [hr, Option.map_some, Option.some.injEq] at h
          cases h
          exact ⟨rfl, hs, presence, hr⟩
    next => contradiction

theorem compile_sound
    (h : compile source known resolve targets = some plan) :
    ValidPlan source known resolve targets plan := by
  induction targets generalizing plan with
  | nil =>
      simp only [compile, Option.some.injEq] at h
      cases h
      exact .nil
  | cons target tail ih =>
      cases he : compileField source known resolve target with
      | none => simp [compile, he] at h
      | some entry =>
          cases ht : compile source known resolve tail with
          | none => simp [compile, he, ht] at h
          | some rest =>
              simp only [compile, he, ht, pure] at h
              cases h
              exact .cons (compileField_sound he) (ih ht)

/-- A declared common field must retain a resolved payload comparison, even
when both declarations are optional or the particular input value is absent. -/
theorem common_field_resolved
    (compiled : compileField source known resolve target = some entry)
    (common : source target.1 = some origin) :
    ∃ cast, entry = .convert target origin cast ∧
      resolve origin.ty target.2.ty = some cast := by
  have valid := compileField_sound compiled
  cases entry with
  | absent actual =>
      cases valid.1
      simp only [FieldPlan.target] at common
      rw [valid.2.1] at common
      contradiction
  | convert actual declared cast =>
      cases valid.1
      have equal : declared = origin := Option.some.inj (valid.2.1.symm.trans common)
      cases equal
      exact ⟨cast, rfl, valid.2.2.2⟩

/-- Before executing any child, a required output field has an actual visible
input. Optional-to-required needs the independent input-specific witness. -/
theorem required_input_present
    {entry : FieldPlan Ty Cast}
    (valid : entry.Valid source known resolve)
    (inputTyped : ViewTyped typed source input)
    (presence : PresenceValid known input)
    (required : entry.target.2.optional = false) :
    ∃ value, input entry.target.1 = some value := by
  cases entry with
  | absent target =>
      simp only [FieldPlan.target] at required
      simp [FieldPlan.Valid, required] at valid
  | convert target origin cast =>
      rcases valid.2.1 with originRequired | targetOptional | knownPresent
      · have hs := inputTyped target.1
        rw [valid.1] at hs
        cases h : input target.1 with
        | none => simp [h, SlotTyped, originRequired] at hs
        | some value => exact ⟨value, h⟩
      · simp only [FieldPlan.target] at required
        simp [required] at targetOptional
      · exact presence _ knownPresent

/-- A child execution includes its actual ordered finite trace. No child
termination, effect permission, or resumption contract is inferred here. -/
inductive FieldRun (child : Cast → Value → List Event → Value → Prop)
    (input : View Value) : FieldPlan Ty Cast → List Event → Option Value → Prop where
  | absent {target : Field Ty} : FieldRun child input (.absent target) [] none
  | missing {target : Field Ty} {origin : Spec Ty} {cast : Cast} : input target.1 = none →
      FieldRun child input (.convert target origin cast) [] none
  | present {target : Field Ty} {origin : Spec Ty} {cast : Cast}
      {value result : Value} {trace : List Event} :
      input target.1 = some value → child cast value trace result →
      FieldRun child input (.convert target origin cast) trace (some result)

inductive Run (child : Cast → Value → List Event → Value → Prop)
    (input : View Value) : List (FieldPlan Ty Cast) → List Event →
      List (Nat × Option Value) → Prop where
  | nil : Run child input [] [] []
  | cons : FieldRun child input entry first value → Run child input tail rest output →
      Run child input (entry :: tail) (first ++ rest) ((entry.target.1, value) :: output)

def ChildSound (typed : Value → Ty → Prop) (resolve : Ty → Ty → Option Cast)
    (child : Cast → Value → List Event → Value → Prop) : Prop :=
  ∀ a b cast value trace result, resolve a b = some cast → typed value a →
    child cast value trace result → typed result b

def OutputTyped (typed : Value → Ty → Prop) (targets : List (Field Ty))
    (output : List (Nat × Option Value)) : Prop :=
  Aligned (fun target slot => slot.1 = target.1 ∧
    SlotTyped typed target.2 slot.2) targets output

theorem fieldRun_preserves
    (valid : entry.Valid source known resolve)
    (inputTyped : ViewTyped typed source input)
    (presence : PresenceValid known input)
    (children : ChildSound typed resolve child)
    (run : FieldRun child input entry trace result) :
    SlotTyped typed entry.target.2 result := by
  cases run with
  | absent => exact valid.2
  | @missing target origin cast absent =>
      have hs := inputTyped target.1
      rw [valid.1, absent] at hs
      rcases valid.2.1 with required | optional | knownPresent
      · simp [SlotTyped, required] at hs
      · exact optional
      · obtain ⟨value, hp⟩ := presence _ knownPresent
        rw [absent] at hp
        contradiction
  | @present target origin cast value trace result hp hc =>
      have hs := inputTyped target.1
      rw [valid.1, hp] at hs
      exact children _ _ _ _ _ _ valid.2.2 hs hc

theorem run_preserves
    (valid : ValidPlan source known resolve targets plan)
    (inputTyped : ViewTyped typed source input)
    (presence : PresenceValid known input)
    (children : ChildSound typed resolve child)
    (run : Run child input plan trace output) :
    OutputTyped typed targets output := by
  induction run generalizing targets with
  | nil =>
      cases valid
      exact .nil
  | @cons entry first value tail rest output hf hr ih =>
      cases valid with
      | cons hv ht =>
          exact .cons ⟨congrArg Prod.fst hv.1,
            hv.1 ▸ fieldRun_preserves hv.2 inputTyped presence children hf⟩ (ih ht)

theorem outputTyped_visible
    (typedOutput : OutputTyped typed targets output) :
    ViewTyped typed (signature targets) (visible output) := by
  induction typedOutput with
  | nil => intro label; rfl
  | @cons target slot targets output head tail ih =>
      intro label
      rcases target with ⟨name, spec⟩
      rcases slot with ⟨outName, value⟩
      rcases head with ⟨hname, hv⟩
      change outName = name at hname
      subst outName
      by_cases h : label = name
      · simpa [signature, visible, h] using hv
      · simpa [signature, visible, h] using ih label

/-- A successful compilation and actual child executions construct a correctly
typed visible output. Child type preservation remains independent of checking. -/
theorem compiled_run_preserves
    (compiled : compile source known resolve targets = some plan)
    (inputTyped : ViewTyped typed source input)
    (presence : PresenceValid known input)
    (children : ChildSound typed resolve child)
    (run : Run child input plan trace output) :
    ViewTyped typed (signature targets) (visible output) :=
  outputTyped_visible (run_preserves (compile_sound compiled) inputTyped presence children run)

theorem fieldRun_presence
    (valid : entry.Valid source known resolve)
    (inputTyped : ViewTyped typed source input)
    (run : FieldRun child input entry trace result) :
    result.isSome = (input entry.target.1).isSome := by
  cases run with
  | @absent target =>
      have h := inputTyped target.1
      rw [valid.1] at h
      simp only [FieldPlan.target, h, Option.isSome_none]
  | missing h => simp only [FieldPlan.target, h, Option.isSome_none]
  | present h _ => simp only [FieldPlan.target, h, Option.isSome_some]

/-- The input view, rather than a hidden backing object, determines survival.
Neither an absent optional field nor a child cast can create a record label. -/
theorem run_survivors
    (valid : ValidPlan source known resolve targets plan)
    (inputTyped : ViewTyped typed source input)
    (run : Run child input plan trace output) (label : Nat) :
    (visible output label).isSome =
      ((input label).isSome && (signature targets label).isSome) := by
  induction run generalizing targets with
  | nil =>
      cases valid
      simp [visible, signature]
  | @cons entry first value tail rest output hf hr ih =>
      cases valid with
      | @cons target _ targets _ hv ht =>
          have hp := fieldRun_presence hv.2 inputTyped hf
          by_cases h : label = target.1
          · simpa [visible, signature, hv.1, h] using hp
          · simpa [visible, signature, hv.1, h] using ih ht

/-- Sequential casts retain the intermediate survivor set. This conclusion does
not require, produce, or replace the plan by a direct endpoint comparison. -/
theorem composed_survivors
    (firstValid : ValidPlan source firstKnown resolve middle firstPlan)
    (secondValid : ValidPlan (signature middle) secondKnown resolve target secondPlan)
    (inputTyped : ViewTyped typed source input)
    (firstPresence : PresenceValid firstKnown input)
    (children : ChildSound typed resolve child)
    (firstRun : Run child input firstPlan firstTrace intermediate)
    (secondRun : Run child (visible intermediate) secondPlan secondTrace output)
    (label : Nat) :
    (visible output label).isSome =
      ((input label).isSome && (signature middle label).isSome &&
        (signature target label).isSome) := by
  have middleTyped := outputTyped_visible
    (run_preserves firstValid inputTyped firstPresence children firstRun)
  rw [run_survivors secondValid middleTyped secondRun,
    run_survivors firstValid inputTyped firstRun]

/-- Pure payload execution is a concrete normal-execution specialization. -/
def execute (apply : Cast → Value → Value) (input : View Value) :
    List (FieldPlan Ty Cast) → List (Nat × Option Value)
  | [] => []
  | .absent target :: tail => (target.1, none) :: execute apply input tail
  | .convert target _ cast :: tail =>
      (target.1, (input target.1).map (apply cast)) :: execute apply input tail

def PureChild (apply : Cast → Value → Value) (cast : Cast) (value : Value)
    (trace : List Event) (result : Value) : Prop :=
  trace = [] ∧ result = apply cast value

theorem execute_runs (apply : Cast → Value → Value) (input : View Value)
    (plan : List (FieldPlan Ty Cast)) :
    Run (PureChild (Event := Event) apply) input plan [] (execute apply input plan) := by
  induction plan with
  | nil => exact .nil
  | cons entry tail ih =>
      cases entry with
      | absent target => exact .cons .absent ih
      | convert target source cast =>
          cases h : input target.1 with
          | none => simpa [execute, FieldPlan.target, h] using Run.cons (FieldRun.missing h) ih
          | some value =>
              simpa [execute, FieldPlan.target, h] using Run.cons
                (FieldRun.present h (show PureChild apply cast value ([] : List Event)
                  (apply cast value) from ⟨rfl, rfl⟩)) ih

namespace Witness

inductive Atom where
  | str | int
  deriving DecidableEq, Repr

def resolve (a b : Atom) : Option Unit := if a = b then some () else none
def noPresence : Nat → Bool := fun _ => false
def a : List (Field Atom) := [(0, ⟨.str, true⟩)]
def b : List (Field Atom) := []
def c : List (Field Atom) := [(0, ⟨.int, true⟩)]
def aRequired : List (Field Atom) := [(0, ⟨.int, false⟩)]
def emptyPlan : List (FieldPlan Atom Unit) := []
def absentPlan : List (FieldPlan Atom Unit) := [.absent (0, ⟨.int, true⟩)]
def directPlan : List (FieldPlan Atom Unit) :=
  [.convert (0, ⟨.int, true⟩) ⟨.int, false⟩ ()]

theorem direct_comparison_nontransitive :
    compile (signature a) noPresence resolve b = some emptyPlan ∧
    compile (signature b) noPresence resolve c = some absentPlan ∧
    compile (signature a) noPresence resolve c = none := by
  decide

def one : View Nat := fun label => if label = 0 then some 1 else none
def keep : Unit → Nat → Nat := fun _ value => value

theorem accepted_paths_have_different_views :
    compile (signature aRequired) noPresence resolve c = some directPlan ∧
    compile (signature aRequired) noPresence resolve b = some emptyPlan ∧
    compile (signature b) noPresence resolve c = some absentPlan ∧
    visible (execute keep one directPlan) 0 = some 1 ∧
    visible (execute keep (visible (execute keep one emptyPlan)) absentPlan) 0 = none := by
  decide

end Witness
end YulangClosure.RecordBoundary
