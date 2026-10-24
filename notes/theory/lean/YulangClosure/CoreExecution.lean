import YulangClosure.CoreSubstitution
import YulangClosure.Contracts

namespace YulangClosure.Original

/-- Actual original principal reductions, restricted to the explicitly typed fragment.
No premise here asserts preservation. -/
inductive Principal : Comp → Comp → Prop
  | letReturn : Principal (.bind (.ret v) n) (substComp (single v) n)
  | forceDelay : Principal (.force (.delay m)) m
  | unionLeft : Principal (.unionCase (.inLeft v) l r) (substComp (single v) l)
  | unionRight : Principal (.unionCase (.inRight v) l r) (substComp (single v) r)
  | chooseLeft : Principal (.chooseLeft (.both v)) (.ret v)
  | chooseRight : Principal (.chooseRight (.both v)) (.ret v)

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
  | unionLeft =>
    cases ht with
    | unionCase hv hl hr =>
      cases hv with
      | inLeft hv => exact substitute_top hl hv
  | unionRight =>
    cases ht with
    | unionCase hv hl hr =>
      cases hv with
      | inRight hv => exact substitute_top hr hv
  | chooseLeft =>
    cases ht with
    | chooseLeft hv =>
      cases hv with
      | both ha hb => exact .ret ha
  | chooseRight =>
    cases ht with
    | chooseRight hv =>
      cases hv with
      | both ha hb => exact .ret hb

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

theorem closed_union (hv : ValTyped emptyContext v (.union a b)) :
    (∃ w, v = .inLeft w ∧ ValTyped emptyContext w a) ∨
    (∃ w, v = .inRight w ∧ ValTyped emptyContext w b) := by
  cases hv with
  | var he => cases he
  | inLeft h => exact .inl ⟨_, rfl, h⟩
  | inRight h => exact .inr ⟨_, rfl, h⟩

theorem closed_intersection (hv : ValTyped emptyContext v (.intersection a b)) :
    ∃ w, v = .both w ∧ ValTyped emptyContext w a ∧ ValTyped emptyContext w b := by
  cases hv with
  | var he => cases he
  | both ha hb => exact ⟨_, rfl, ha, hb⟩

theorem closed_bottom (hv : ValTyped emptyContext v .bottom) : False := by
  cases hv with
  | var he => cases he

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
    | unionCase hv hl hr =>
      cases closed_union hv with
      | inl h =>
        obtain ⟨v, rfl, hv⟩ := h
        exact .inr ⟨_, .principal .unionLeft⟩
      | inr h =>
        obtain ⟨v, rfl, hv⟩ := h
        exact .inr ⟨_, .principal .unionRight⟩
    | chooseLeft hv =>
      obtain ⟨v, rfl, ha, hb⟩ := closed_intersection hv
      exact .inr ⟨_, .principal .chooseLeft⟩
    | chooseRight hv =>
      obtain ⟨v, rfl, ha, hb⟩ := closed_intersection hv
      exact .inr ⟨_, .principal .chooseRight⟩
    | absurd hv => exact (closed_bottom hv).elim

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
  | unionLeft : RawStep (rawUnionCase (rawIn false v) l r, fs)
      (substituteRaw (rawSingle v) l, fs)
  | unionRight : RawStep (rawUnionCase (rawIn true v) l r, fs)
      (substituteRaw (rawSingle v) r, fs)
  | chooseLeft : RawStep (rawChoose false (rawProofBoth v), fs) (rawRet v, fs)
  | chooseRight : RawStep (rawChoose true (rawProofBoth v), fs) (rawRet v, fs)
  | unionUnitBad : RawStep (rawUnionCase (.atom (.literal .unit)) l r, fs) (rawBad, fs)
  | chooseUnitBad : RawStep (rawChoose side (.atom (.literal .unit)), fs) (rawBad, fs)
  | absurdUnitBad : RawStep (rawAbsurd (.atom (.literal .unit)), fs) (rawBad, fs)
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
    | unionLeft =>
      simp only [State.raw, Comp.raw, Val.raw]
      rw [← single_raw]
      exact .unionLeft
    | unionRight =>
      simp only [State.raw, Comp.raw, Val.raw]
      rw [← single_raw]
      exact .unionRight
    | chooseLeft => exact .chooseLeft
    | chooseRight => exact .chooseRight

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
      | unionCase hv hl hr =>
        cases hx
        exact ⟨_, rfl, .enter⟩
      | chooseLeft hv =>
        cases hx
        exact ⟨_, rfl, .enter⟩
      | chooseRight hv =>
        cases hx
        exact ⟨_, rfl, .enter⟩
      | absurd hv =>
        cases hx
        exact ⟨_, rfl, .enter⟩
    | unionCase hv hl hr =>
      cases closed_union hv with
      | inl h =>
        obtain ⟨v, rfl, hv⟩ := h
        cases hx with
        | unionLeft =>
          exact ⟨_, by simp only [State.raw, single_raw], .principal .unionLeft⟩
      | inr h =>
        obtain ⟨v, rfl, hv⟩ := h
        cases hx with
        | unionRight =>
          exact ⟨_, by simp only [State.raw, single_raw], .principal .unionRight⟩
    | chooseLeft hv =>
      obtain ⟨v, rfl, ha, hb⟩ := closed_intersection hv
      cases hx with
      | chooseLeft => exact ⟨_, rfl, .principal .chooseLeft⟩
    | chooseRight hv =>
      obtain ⟨v, rfl, ha, hb⟩ := closed_intersection hv
      cases hx with
      | chooseRight => exact ⟨_, rfl, .principal .chooseRight⟩
    | absurd hv => exact (closed_bottom hv).elim

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
LEAN-STRUCTURAL-20261024/r1, producer construction and primary post-STOP repair.

Added union injection/case (each arm independently binds one payload), Top,
Bottom elimination (no Bottom introduction), and one-value intersection/choose.
The computational representation erases only d1/d2 : Prop derivations.
ValTyped.both requires two judgments on the identical v; principal preservation
selects the corresponding judgment and returns that same v. This is NOT runtime
View removal. Each choose remains one actual principal step. rawProofBoth is
this proof-erased image; rawBoth retains the separate explicit-evidence syntax.
Correspondence to executable evidence outside this image remains OPEN, as do
all runtime View rules. No erasure of runtime metadata/receipts is authorized.

All former raw algebra is unchanged. The SAME raw_finite_safety now quantifies
the enlarged RawStep and typed image, including new malformed-unit Bad rules.
Typed renaming/substitution, raw embedding, canonical forms, preservation,
progress and lifting of EVERY raw successor have passed primary Lean checking.
The first check found a shadowed renaming variable in the new unionCase branch;
primary repaired it and removed unused simp arguments after actual worker STOP.
Checks and independent review have separate receipts in the sprint outcome.

Still OPEN: full original constructor typing/type-evidence substitution,
Call/Resume/type beta/tuple/record/variant/nominal/guarded graph/primitive/perform/
handler/mapop/eabs/eapp; actual Control stack-prefix connection and real value
interpretation; full original source/native/A-B/coverage/principality/termination.
No original full V1/BodyLaws/LocalLaws closure is claimed.
-/
end YulangClosure.Original
