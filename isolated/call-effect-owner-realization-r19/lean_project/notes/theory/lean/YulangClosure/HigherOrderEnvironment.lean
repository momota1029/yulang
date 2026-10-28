import YulangClosure.HigherOrderSubstitution
import YulangClosure.HigherOrderEmbedding

namespace YulangClosure.HigherOrder.Environment
open YulangClosure.NativeClosureEnvironment
open YulangClosure.CallEnvironmentRealization (Reference address)

abbrev Layout (K : Type) := List (Reference K × Ty)

def read [DecidableEq K] (arena : Arena K D) (env : Nat)
    (store : Nat → Option Value) (ref : Reference K) : Option Value :=
  readEmbedded arena env store ref

/-- This genuinely runs the finite lookup/read sequence. Any failed read aborts. -/
def realize [DecidableEq K] (arena : Arena K D) (env : Nat)
    (store : Nat → Option Value) : Layout K → Option (List Value)
  | [] => some []
  | (ref, _) :: rest => do
      let value ← read arena env store ref
      let values ← realize arena env store rest
      pure (value :: values)

def context : Layout K → Context
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
  | none => simp [read, readEmbedded, ha] at hr
  | some cell =>
      have hs : store cell = some value := by simpa [read, readEmbedded, ha] using hr
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
    {body : Comp} {result : Ty} (typed : CompTyped (context layout) body result) :
    CompTyped emptyContext (substComp (substitution filler values) body) result :=
  substComp_typed typed (realized_substitution_typed success cells filler)

/-- Capture closes the ambient environment while keeping a parameter binder.
The inserted callable values are shifted beneath that binder. -/
theorem close_bound_body [DecidableEq K] {arena : Arena K D} {env : Nat}
    {store : Nat → Option Value} {layout : Layout K} {values : List Value}
    (success : realize arena env store layout = some values)
    (cells : CellsTyped arena env store layout) (filler : Value)
    {body : Comp} {parameter result : Ty}
    (hb : CompTyped (extend (context layout) parameter) body result) :
    CompTyped (extend emptyContext parameter)
      (substComp (lift (substitution filler values)) body) result :=
  substComp_typed hb (lift_typed (realized_substitution_typed success cells filler) parameter)

theorem close_adapter [DecidableEq K] {arena : Arena K D} {env : Nat}
    {store : Nat → Option Value} {layout : Layout K} {values : List Value}
    (success : realize arena env store layout = some values)
    (cells : CellsTyped arena env store layout) (filler : Value)
    (ha : AdapterTyped (context layout) adapter a b) :
    AdapterTyped emptyContext (substAdapter (substitution filler values) adapter) a b :=
  substAdapter_typed ha (realized_substitution_typed success cells filler)

/-- A fresh global-reference witness is a formal address witness, not a claim
that a source ModuleDef identifier denotes this newly allocated cell. -/
def freshLayout (store : Store Value) (a : Ty) : Layout Nat :=
  [(.global store.size, a)]

theorem fresh_read (arena : Arena Nat D) (env : Nat) (store : Store Value) (v : Value) :
    read arena env (store.push v).cell (.global store.size) = some v := by
  simp [read, readEmbedded, address, push_current]

theorem fresh_realize (arena : Arena Nat D) (env : Nat) (store : Store Value) (v : Value) (a : Ty) :
    realize arena env (store.push v).cell (freshLayout store a) = some [v] := by
  simp [freshLayout, realize, fresh_read]

theorem fresh_cells (arena : Arena Nat D) (env : Nat) (store : Store Value)
    (hv : ValueTyped emptyContext v a) :
    CellsTyped arena env (store.push v).cell (freshLayout store a) := by
  intro ref ty hm cell value ha hs
  simp only [freshLayout, List.mem_singleton, Prod.mk.injEq] at hm
  rcases hm with ⟨hr, ht⟩
  subst ref
  subst ty
  simp only [address, Option.some.injEq] at ha
  subst cell
  rw [push_current] at hs
  cases hs
  exact hv

/-- The cell premise is constructed, then fed to finite capture and substitution
for an arbitrary typed higher-order body. No arbitrary native cell typing axiom. -/
theorem fresh_function_closes {f : TypedCall.Function} {a b : Original.Ty}
    (hf : TypedCall.FunctionTyped f a b) (arena : Arena Nat D) (env : Nat)
    (store : Store Value) (filler : Value) {body : Comp} {result : Ty}
    (hb : CompTyped (context (freshLayout store (.callable (embedTy a) (embedTy b)))) body result) :
    read arena env (store.push (embedFunction f)).cell (.global store.size) = some (embedFunction f) ∧
    realize arena env (store.push (embedFunction f)).cell
      (freshLayout store (.callable (embedTy a) (embedTy b))) = some [embedFunction f] ∧
    CompTyped emptyContext (substComp (substitution filler [embedFunction f]) body) result := by
  exact ⟨fresh_read arena env store _, fresh_realize arena env store _ _,
    close_body (fresh_realize arena env store _ _)
      (fresh_cells arena env store (embedFunction_typed hf _)) filler hb⟩

/-- Concrete consumer of the successful fresh capture: return the captured
callable, then allow it to be used as a delayed higher-order argument. -/
theorem fresh_function_return {f : TypedCall.Function} {a b : Original.Ty}
    (hf : TypedCall.FunctionTyped f a b) (arena : Arena Nat D) (env : Nat)
    (store : Store Value) (filler : Value) :
    CompTyped emptyContext (.ret (embedFunction f)) (.callable (embedTy a) (embedTy b)) := by
  have hb : CompTyped (context (freshLayout store (.callable (embedTy a) (embedTy b))))
      (.ret (.var 0)) (.callable (embedTy a) (embedTy b)) := .ret (.var rfl)
  exact close_body (fresh_realize arena env store (embedFunction f) _)
    (fresh_cells arena env store (embedFunction_typed hf _)) filler hb

theorem fresh_function_argument {f : TypedCall.Function} {a b : Original.Ty}
    (hf : TypedCall.FunctionTyped f a b) (arena : Arena Nat D) (env : Nat)
    (store : Store Value) (filler : Value) :
    ValueTyped emptyContext (.delay (.ret (embedFunction f)))
      (.thunk (.callable (embedTy a) (embedTy b))) :=
  .delay (fresh_function_return hf arena env store filler)

/-- Lexical capture selects the same freshly allocated current callable cell. -/
theorem fresh_lexical_read [DecidableEq K] (old : Arena K D) (parent : Nat)
    (key : K) (dispatch : D) (store : Store Value) (v : Value) :
    read (.append old parent (some (key, store.size)) dispatch) old.size
      (store.push v).cell (.lexical key) = some v := by
  simp [read, readEmbedded, address, parameter_shadows, push_current]

end YulangClosure.HigherOrder.Environment
