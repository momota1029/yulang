import YulangClosure.NativeClosureEnvironment
import YulangClosure.CoreSubstitution

namespace YulangClosure.CallEnvironmentRealization
open YulangClosure.Original
open YulangClosure.TypedCall
open YulangClosure.NativeClosureEnvironment

/-- A resolved lexical full identity or an already resolved global cell address.
The source resolver's coverage/accuracy is a separate premise. -/
inductive Reference (K : Type) where
  | lexical (key : K)
  | global (cell : Nat)

abbrev Layout (K : Type) := List (Reference K × Ty)

def address [DecidableEq K] (arena : Arena K D) (env : Nat) : Reference K → Option Nat
  | .lexical key => lookupKey key arena env
  | .global cell => some cell

def read [DecidableEq K] (arena : Arena K D) (env : Nat)
    (store : Nat → Option Value) (ref : Reference K) : Option Value :=
  (address arena env ref).bind store

/-- This genuinely runs the finite lookup/read sequence. Any failed read aborts. -/
def realize [DecidableEq K] (arena : Arena K D) (env : Nat)
    (store : Nat → Option Value) : Layout K → Option (List Value)
  | [] => some []
  | (ref, _) :: rest => do
      let value ← read arena env store ref
      let values ← realize arena env store rest
      pure (value :: values)

def context : Layout K → Original.Context
  | [], _ => none
  | (_, ty) :: _, 0 => some ty
  | _ :: rest, n + 1 => context rest n

/-- Filler occurs only outside the represented finite context. -/
def substitution (filler : Value) : List Value → Nat → Value
  | [], _ => filler
  | value :: _, 0 => value
  | _ :: rest, n + 1 => substitution filler rest n

inductive Captured (readValue : Reference K → Option Value) : Layout K → List Value → Prop where
  | nil : Captured readValue [] []
  | cons : readValue ref = some value → Captured readValue rest values →
      Captured readValue ((ref, ty) :: rest) (value :: values)

theorem realize_captured [DecidableEq K] (arena : Arena K D) (env : Nat)
    (store : Nat → Option Value) (layout : Layout K) (values : List Value)
    (h : realize arena env store layout = some values) :
    Captured (read arena env store) layout values := by
  induction layout generalizing values with
  | nil => simp [realize] at h; subst values; exact .nil
  | cons head rest ih =>
      rcases head with ⟨ref, ty⟩
      cases hr : read arena env store ref with
      | none => simp [realize, hr] at h
      | some value =>
          cases ht : realize arena env store rest with
          | none => simp [realize, hr, ht] at h
          | some tail =>
              simp [realize, hr, ht] at h
              subst values
              exact .cons hr (ih tail ht)

/-- Every typed free index sees a successful actual read, never the filler. -/
theorem captured_index {readValue : Reference K → Option Value}
    {layout : Layout K} {values : List Value} (h : Captured readValue layout values)
    (filler : Value) (i : Nat) (ty : Ty) (hi : context layout i = some ty) :
    ∃ ref, (ref, ty) ∈ layout ∧ readValue ref = some (substitution filler values i) := by
  induction h generalizing i with
  | nil => cases hi
  | @cons ref value rest values a hr ht ih =>
      cases i with
      | zero =>
          simp only [context, Option.some.injEq] at hi
          subst ty
          exact ⟨ref, by simp, hr⟩
      | succ i =>
          obtain ⟨r, hm, hv⟩ := ih i hi
          exact ⟨r, by simp [hm], hv⟩

/-- The per-cell typing obligation is explicit and restricted to layout entries
and successful addresses/current reads. Arbitrary stores need not be typed. -/
def CellsTyped [DecidableEq K] (arena : Arena K D) (env : Nat)
    (store : Nat → Option Value) (layout : Layout K) : Prop :=
  ∀ ref ty, (ref, ty) ∈ layout → ∀ cell value,
    address arena env ref = some cell → store cell = some value →
    ValueTyped emptyContext value ty

theorem successful_read_typed [DecidableEq K] {arena : Arena K D} {env : Nat}
    {store : Nat → Option Value} {layout : Layout K} (hc : CellsTyped arena env store layout)
    {ref : Reference K} {ty : Ty} (hm : (ref, ty) ∈ layout)
    {value : Value} (hr : read arena env store ref = some value) :
    ValueTyped emptyContext value ty := by
  cases ha : address arena env ref with
  | none => simp [read, ha] at hr
  | some cell =>
      have hs : store cell = some value := by simpa [read, ha] using hr
      exact hc ref ty hm cell value ha hs

theorem realized_substitution_typed [DecidableEq K] {arena : Arena K D} {env : Nat}
    {store : Nat → Option Value} {layout : Layout K} {values : List Value}
    (success : realize arena env store layout = some values)
    (cells : CellsTyped arena env store layout) (filler : Value) :
    ∀ i ty, context layout i = some ty →
      ValueTyped emptyContext (substitution filler values i) ty := by
  intro i ty hi
  obtain ⟨ref, hm, hr⟩ := captured_index
    (realize_captured arena env store layout values success) filler i ty hi
  exact successful_read_typed cells hm hr

/-- Parent application: actual successful capture construction supplies the
existing substitution theorem, including its bind and request lifting cases. -/
theorem close_body [DecidableEq K] {arena : Arena K D} {env : Nat}
    {store : Nat → Option Value} {layout : Layout K} {values : List Value}
    (success : realize arena env store layout = some values)
    (cells : CellsTyped arena env store layout) (filler : Value)
    {body : TypedCall.Comp} {result : Ty} (typed : TypedCall.CompTyped (context layout) body result) :
    TypedCall.CompTyped emptyContext (substituteCallComp (substitution filler values) body) result :=
  substituteCallComp_typed typed (realized_substitution_typed success cells filler)

def parameterSubstitution (parameter : Value) (captures : Nat → Value) : Nat → Value
  | 0 => parameter
  | n + 1 => captures n

theorem close_parameter_body [DecidableEq K] {arena : Arena K D} {env : Nat}
    {store : Nat → Option Value} {layout : Layout K} {values : List Value}
    (success : realize arena env store layout = some values)
    (cells : CellsTyped arena env store layout) (filler : Value)
    {parameter : Value} {a result : Ty} (hp : ValueTyped emptyContext parameter a)
    {body : TypedCall.Comp} (hb : TypedCall.CompTyped (Original.extend (context layout) a) body result) :
    TypedCall.CompTyped emptyContext
      (substituteCallComp (parameterSubstitution parameter (substitution filler values)) body) result := by
  apply substituteCallComp_typed hb
  intro i ty hi
  cases i with
  | zero =>
      simp only [Original.extend, Option.some.injEq] at hi
      subst ty
      exact hp
  | succ i => exact realized_substitution_typed success cells filler i ty hi

/-- Computation entry retains the actual closed delayed body, at UA. -/
theorem delayed_parameter {body : TypedCall.Comp} {a : Ty}
    (h : TypedCall.CompTyped emptyContext body a) :
    ValueTyped emptyContext (.delay body) (.thunk a) := .delay h

theorem close_computation_body [DecidableEq K] {arena : Arena K D} {env : Nat}
    {store : Nat → Option Value} {layout : Layout K} {values : List Value}
    (success : realize arena env store layout = some values)
    (cells : CellsTyped arena env store layout) (filler : Value)
    {argument body : TypedCall.Comp} {a result : Ty}
    (ha : TypedCall.CompTyped emptyContext argument a)
    (hb : TypedCall.CompTyped (Original.extend (context layout) (.thunk a)) body result) :
    TypedCall.CompTyped emptyContext
      (substituteCallComp
        (parameterSubstitution (.delay argument) (substitution filler values)) body) result :=
  close_parameter_body success cells filler (.delay ha) hb

example : realize (Arena.root ()) 0 (fun _ => (none : Option Value))
    [((Reference.lexical (1 : Nat)), Ty.base .unit)] = none := rfl

example : realize (Arena.root ()) 0 (fun _ => (none : Option Value))
    [((Reference.global (K := Nat) 3), Ty.base .unit)] = none := rfl

example : realize (Arena.root ()) 0 (fun _ => some (Value.original .unit))
    [((Reference.global (K := Nat) 3), Ty.base .unit)] =
      some [.original .unit] := rfl

end YulangClosure.CallEnvironmentRealization
