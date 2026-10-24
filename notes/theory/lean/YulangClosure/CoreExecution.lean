import YulangClosure.CoreSubstitution
import YulangClosure.Contracts

namespace YulangClosure.Original

/-- Actual original principal reductions, restricted to the explicitly typed fragment.
No premise here asserts preservation. -/
inductive Principal : Comp → Comp → Prop
  | letReturn : Principal (.bind (.ret v) n) (substComp (single v) n)
  | forceDelay : Principal (.force (.delay m)) m

theorem principal_preservation (step : Principal m n) (ht : CompTyped env m a) :
    CompTyped env n a := by
  cases step with
  | letReturn =>
    cases ht with
    | bind hm hn =>
      cases hm with
      | ret hv => exact substitute_top hn hv
  | forceDelay =>
    cases ht with
    | force hv =>
      cases hv with
      | delay hm => exact hm

/-- These are syntax-bearing frames, not opaque registered body opcodes. -/
inductive Frame where
  | bind : Comp → Frame

inductive FramesTyped (env : Context) : List Frame → Ty → Ty → Prop
  | nil : FramesTyped env [] a a
  | cons : CompTyped (extend env a) n b → FramesTyped env fs b result →
      FramesTyped env (.bind n :: fs) a result

structure State where
  current : Comp
  stack : List Frame

def StateTyped (env : Context) (result : Ty) (s : State) : Prop :=
  ∃ a, CompTyped env s.current a ∧ FramesTyped env s.stack a result

/-- Entry really changes the stack. The saved suffix is literally retained. -/
inductive Step : State → State → Prop
  | enter : Step ⟨.bind m n, fs⟩ ⟨m, .bind n :: fs⟩
  | returnBind : Step ⟨.ret v, .bind n :: fs⟩ ⟨substComp (single v) n, fs⟩
  | principal : Principal m n → Step ⟨m, fs⟩ ⟨n, fs⟩

theorem step_preservation (h : Step s t) (ht : StateTyped env result s) :
    StateTyped env result t := by
  rcases ht with ⟨a, hm, hfs⟩
  cases h with
  | enter =>
    cases hm with
    | bind first body => exact ⟨_, first, .cons body hfs⟩
  | returnBind =>
    cases hm with
    | ret hv =>
      cases hfs with
      | cons body tail => exact ⟨_, substitute_top body hv, tail⟩
  | principal hp => exact ⟨_, principal_preservation hp hm, hfs⟩

inductive Steps : Nat → State → State → Prop
  | refl : Steps 0 s s
  | snoc : Steps n s t → Step t u → Steps (n+1) s u

theorem finite_preservation (h : Steps n s t) (ht : StateTyped env result s) :
    StateTyped env result t := by
  induction h with
  | refl => exact ht
  | snoc hp hx ih => exact step_preservation hx (ih ht)

theorem closed_thunk (hv : ValTyped emptyContext v (.thunk a)) :
    ∃ m, v = .delay m ∧ CompTyped emptyContext m a := by
  cases hv with
  | var he => cases he
  | delay hm => exact ⟨_, rfl, hm⟩

/-- A closed typed fragment state either returns a typed value at the empty
stack or has a concrete next transition. No body-progress premise is used. -/
theorem progress (ht : StateTyped emptyContext result s) :
    (∃ v, s = ⟨.ret v, []⟩ ∧ ValTyped emptyContext v result) ∨ ∃ t, Step s t := by
  cases s with | mk m fs =>
    obtain ⟨a, hm, hs⟩ := ht
    cases hm with
    | ret hv =>
      cases hs with
      | nil => exact .inl ⟨_, rfl, hv⟩
      | cons hn tail => exact .inr ⟨_, .returnBind⟩
    | force hv =>
      obtain ⟨m, rfl, hm⟩ := closed_thunk hv
      exact .inr ⟨_, .principal .forceDelay⟩
    | bind hm hn => exact .inr ⟨_, .enter⟩

theorem finite_safety (trace : YulangClosure.Prefix Step n s t)
    (ht : StateTyped emptyContext result s) :
    StateTyped emptyContext result t ∧
      ((∃ v, t = ⟨.ret v, []⟩ ∧ ValTyped emptyContext v result) ∨ ∃ u, Step t u) := by
  have htyped : StateTyped emptyContext result t := by
    induction trace with
    | refl => exact ht
    | snoc hp hx ih => exact step_preservation hx (ih ht)
  exact ⟨htyped, progress htyped⟩

/-- Raw syntax counterpart of the actual let entry, with an arbitrary existing
raw frame suffix. It does not manufacture a Core-to-control Nat cast. -/
inductive RawFrame where
  | bind : Raw → RawFrame

inductive RawEntry : Raw × List RawFrame → Raw × List RawFrame → Prop
  | bind : RawEntry (rawLet m n, fs) (m, .bind n :: fs)

def Frame.raw : Frame → RawFrame
  | .bind n => .bind n.raw

theorem entry_correspondence (m n : Comp) (fs : List Frame) :
    RawEntry ((Comp.bind m n).raw, fs.map Frame.raw)
      (m.raw, RawFrame.bind n.raw :: fs.map Frame.raw) := .bind

abbrev RawState := Raw × List RawFrame

def State.raw (s : State) : RawState := (s.current.raw, s.stack.map Frame.raw)

def rawBad : Raw := .node .bad .nil

/-- Raw principal/entry rules for this source fragment. Malformed Force really
reaches Bad; it is not removed by an intrinsic typing index. Other original
constructors require their own raw rules before a whole-language claim. -/
inductive RawStep : RawState → RawState → Prop
  | enter : RawStep (rawLet m n, fs) (m, .bind n :: fs)
  | returnBind : RawStep (rawRet v, .bind n :: fs)
      (substituteRaw (rawSingle v) n, fs)
  | letReturn : RawStep (rawLet (rawRet v) n, fs)
      (substituteRaw (rawSingle v) n, fs)
  | forceDelay : RawStep (rawForce (rawDelay m), fs) (m, fs)
  /-- This known wrong constructor is rejected. No rule declares View/graph/
  type-application operands bad merely because their surface is not Delay. -/
  | forceUnitBad : RawStep (rawForce (.atom (.literal .unit)), fs) (rawBad, fs)
  | badFrame : RawStep (rawBad, f :: fs) (rawBad, fs)

theorem step_raw (h : Step s t) : RawStep s.raw t.raw := by
  cases h with
  | enter => exact .enter
  | returnBind =>
    simp only [State.raw, Comp.raw, List.map_cons, Frame.raw]
    rw [← single_raw]
    exact .returnBind
  | principal hp =>
    cases hp with
    | letReturn =>
      simp only [State.raw, Comp.raw]
      rw [← single_raw]
      exact .letReturn
    | forceDelay => exact .forceDelay

/-- Backwards step correspondence, crucial for safety of RAW execution rather
than just its chosen typed reduction. Every possible raw step from a closed
typed image is an actual typed-fragment step. -/
theorem raw_step_lifts (ht : StateTyped emptyContext result s)
    (hx : RawStep s.raw r) : ∃ t, r = t.raw ∧ Step s t := by
  cases s with | mk m fs =>
    obtain ⟨a, hm, hs⟩ := ht
    cases hm with
    | ret hv =>
      cases fs with
      | nil => cases hx
      | cons f fs =>
        cases f with | bind n =>
          cases hx
          exact ⟨_, by simp only [State.raw, single_raw], .returnBind⟩
    | force hv =>
      obtain ⟨m, rfl, hm⟩ := closed_thunk hv
      cases hx with
      | forceDelay => exact ⟨_, rfl, .principal .forceDelay⟩
    | bind hm hn =>
      cases hm with
      | ret hv =>
        cases hx with
        | enter => exact ⟨_, rfl, .enter⟩
        | letReturn =>
          exact ⟨_, by simp only [State.raw, single_raw], .principal .letReturn⟩
      | force hv =>
        cases hx
        exact ⟨_, rfl, .enter⟩
      | bind hm hn =>
        cases hx
        exact ⟨_, rfl, .enter⟩

def RawStateTyped (result : Ty) (r : RawState) : Prop :=
  ∃ s, r = s.raw ∧ StateTyped emptyContext result s

theorem raw_preservation (ht : RawStateTyped result r) (hx : RawStep r u) :
    RawStateTyped result u := by
  obtain ⟨s, rfl, hs⟩ := ht
  obtain ⟨t, he, hstep⟩ := raw_step_lifts hs hx
  exact ⟨t, he, step_preservation hstep hs⟩

theorem raw_not_bad (ht : RawStateTyped result r) : r.1 ≠ rawBad := by
  obtain ⟨s, rfl, hs⟩ := ht
  cases s with | mk m fs =>
    cases m <;> intro he <;> cases he

theorem raw_progress (ht : RawStateTyped result r) :
    (∃ v, r = (rawRet v.raw, []) ∧ ValTyped emptyContext v result) ∨
      ∃ u, RawStep r u := by
  obtain ⟨s, rfl, hs⟩ := ht
  cases progress hs with
  | inl hr =>
    obtain ⟨v, rfl, hv⟩ := hr
    exact .inl ⟨v, rfl, hv⟩
  | inr hs =>
    obtain ⟨t, hx⟩ := hs
    exact .inr ⟨t.raw, step_raw hx⟩

/-- A theorem about ALL raw traces, including the raw Bad rules. Its initial
typing is an independent syntax image, not reachability or absence of Bad. -/
theorem raw_finite_safety (ht : RawStateTyped result r)
    (trace : YulangClosure.Prefix RawStep n r u) :
    RawStateTyped result u ∧ u.1 ≠ rawBad ∧
      ((∃ v, u = (rawRet v.raw, []) ∧ ValTyped emptyContext v result) ∨
        ∃ z, RawStep u z) := by
  have typed : RawStateTyped result u := by
    induction trace with
    | refl => exact ht
    | snoc hp hx ih => exact raw_preservation (ih ht) hx
  exact ⟨typed, raw_not_bad typed, raw_progress typed⟩

/-!
LEAN-CORE-20261024/r1, jointly completed by primary after producer actual STOP.

Full raw constructor vocabulary and four namespace binding traversal are defined;
renaming/substitution identity/composition are proved over ALL Raw/Forest terms.
Raw arity/sort/original constructor-specific typing remain OPEN.

Typed coverage is exactly unit/variable/delay + Ret/Force/let. Contexts are partial;
emptyContext is truly empty. Within that scope, typed renaming/substitution,
raw embedding commutation, let/Force principal preservation, syntax-bearing
stack entry, progress, backwards correspondence for EVERY raw step and all-finite
raw safety are proved. Malformed raw Force reaches rawBad; the backwards proof
excludes it from closed typed images. No body-safety premise is assumed here.

This does not prove original full V1 or instantiate Control.BodyLaws. Original
Call/Resume/type beta/intersection/tuple/record/variant/nominal/guarded graph,
lookup/switch/primitives/perform/handler/mapop/eabs/eapp rules and type safety
remain owning obligations. Eapp must retain admin.effect/result and direct
result adapters before Yes. Existing Control modules are unchanged; their body
hook still needs a syntax-bearing stack-prefix extension and a real original
value/type interpretation. No Core-to-Nat cast or dummy Analysis is supplied.

Original whole source, source/native, extrusion/intrusion/SCC A/B, coverage,
principality and inference termination remain OPEN. Kernel checks and independent
review receipts are recorded separately; no project axioms or proof holes.
-/
end YulangClosure.Original
