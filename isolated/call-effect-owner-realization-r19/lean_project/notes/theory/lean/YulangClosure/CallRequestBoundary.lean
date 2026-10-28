import YulangClosure.CallRequestUnwind

namespace YulangClosure.Control

/-- The actual request transition; totalization outside requests is only notation. -/
def CallState.requestNext {W : Type} (md : Metadata W) (s : CallState W) : CallState W :=
  match s.head, s.frames with
  | .requesting op payload k observed, .bind body :: fs =>
      { s with head := .requesting op payload (captureBind k body) observed, frames := fs }
  | .requesting op payload k observed, .adapter _ _ body :: fs =>
      { s with head := .requesting op payload (captureBind k body) observed, frames := fs }
  | .requesting op payload k observed, .scope owner :: fs =>
      { s with
        world := md.suspendScope s.world owner
        head := .requesting op payload (.scope owner k) observed
        frames := fs
        scopeContext := owner :: s.scopeContext }
  | .requesting op payload k observed, .expose e r :: fs =>
      { s with
        world := md.suspendView s.world e.identity
        head := .requesting op payload (.expose e r k) observed
        frames := fs }
  | .requesting op payload k observed, [] =>
      { s with head := .requested op payload k, viewContext := observed }
  | _, _ => s

def CallState.requestBoundary {W : Type} (md : Metadata W) : Nat → CallState W → CallState W
  | 0, s => s
  | n + 1, s => requestNext md (requestBoundary md n s)

private def RequestRegion {W : Type} (s : CallState W) : Prop :=
  match s.head with
  | .requesting .. => True
  | .requested .. => True
  | _ => False

private theorem request_step_unique {W : Type} {md : Metadata W}
    {s t : CallState W} (hr : RequestRegion s) (h : CallControlStep md s t) :
    t = s.requestNext md ∧ RequestRegion t := by
  cases h <;> simp_all [RequestRegion, CallState.requestNext, CallState.initial]

private theorem boundary_shift {W : Type} (md : Metadata W) (n : Nat) (s : CallState W) :
    s.requestBoundary md (n + 1) = (s.requestNext md).requestBoundary md n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (CallState.requestNext md) ih

private theorem prefix_prepend {C : Type} {step : C → C → Prop}
    {n : Nat} {b c : C} (h : YulangClosure.Prefix step n b c) :
    ∀ {a}, step a b → YulangClosure.Prefix step (n + 1) a c := by
  induction h with
  | refl => intro a hs; exact .snoc (.refl a) hs
  | snoc h hs ih => intro a hf; exact .snoc (ih hf) hs

private theorem request_prefix_unique {W : Type} {md : Metadata W}
    {n : Nat} {s t : CallState W} (h : YulangClosure.Prefix (CallControlStep md) n s t)
    (hr : RequestRegion s) : t = s.requestBoundary md n ∧ RequestRegion t := by
  revert hr
  induction h with
  | refl => intro hr; exact ⟨rfl, hr⟩
  | snoc h hs ih =>
      intro hr
      obtain ⟨he, hm⟩ := ih hr
      obtain ⟨ht, hrt⟩ := request_step_unique hm hs
      exact ⟨by simpa only [CallState.requestBoundary, ← he] using ht, hrt⟩

private def requestRank {W : Type} (s : CallState W) : Nat :=
  match s.head with
  | .requesting .. => s.frames.length + 1
  | _ => 0

private theorem request_step_rank {W : Type} {md : Metadata W}
    {s t : CallState W} (hr : RequestRegion s) (hs : CallControlStep md s t) :
    requestRank t + 1 = requestRank s := by
  cases hs <;> simp_all [RequestRegion, requestRank, CallState.initial]

private theorem request_prefix_rank {W : Type} {md : Metadata W}
    {n : Nat} {s t : CallState W}
    (hp : YulangClosure.Prefix (CallControlStep md) n s t)
    (hr : RequestRegion s) : n + requestRank t = requestRank s := by
  induction hp with
  | refl => exact Nat.zero_add _
  | @snoc n s mid t hp hs ih =>
      have hmid := (request_prefix_unique hp hr).2
      calc
        n + 1 + requestRank t = n + (requestRank t + 1) := by
          rw [Nat.add_assoc, Nat.add_comm 1]
        _ = n + requestRank mid := congrArg (fun r => n + r) (request_step_rank hmid hs)
        _ = requestRank s := ih hr

section
variable {W : Type} (md : Metadata W)
variable (world : W) (op : TypedCall.OperationInstance) (payload : TypedCall.Value)
variable (k : TypedCall.Comp) (observed : List TypedCall.ViewOccurrence)
variable (frames : List TypedCall.ContextFrame) (view : TypedCall.CallView)
variable (result : Original.Ty) (scopes : List Nat)
variable (views : List TypedCall.ViewOccurrence) (receipts : List TypedCall.ReceiptSlot)
variable (suffix : List Frame)

private theorem request_next_realized :
    CallControlStep md
      ⟨world, .requesting op payload k observed, frames, view, result, scopes, views, receipts, suffix⟩
      (CallState.requestNext md
        ⟨world, .requesting op payload k observed, frames, view, result, scopes, views, receipts, suffix⟩) := by
  cases frames with
  | nil => exact .finishRequest world op payload k observed view result scopes views receipts suffix
  | cons f fs =>
      cases f with
      | bind body => exact .requestBind world op payload k body observed fs view result scopes views receipts suffix
      | adapter a b body => exact .requestAdapter world op payload k observed a b body fs view result scopes views receipts suffix
      | scope owner => exact .requestScope world owner op payload k observed fs view result scopes views receipts suffix
      | expose e r => exact .requestExpose world e r op payload k observed fs view result scopes views receipts suffix

/-- Every prefix up to and including completion is actually realized. -/
theorem call_request_prefix_realized (n : Nat) (hn : n ≤ frames.length + 1) :
    YulangClosure.Prefix (CallControlStep md) n
      ⟨world, .requesting op payload k observed, frames, view, result, scopes, views, receipts, suffix⟩
      (CallState.requestBoundary md n
        ⟨world, .requesting op payload k observed, frames, view, result, scopes, views, receipts, suffix⟩) := by
  induction frames generalizing world k scopes n with
  | nil =>
      cases n with
      | zero => exact .refl _
      | succ n =>
          have hz : n = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_succ_le_succ hn)
          subst n
          exact .snoc (.refl _) (request_next_realized md world op payload k observed [] view result scopes views receipts suffix)
  | cons f fs ih =>
      cases n with
      | zero => exact .refl _
      | succ n =>
          rw [boundary_shift]
          have hn' : n ≤ fs.length + 1 := Nat.le_of_succ_le_succ hn
          cases f with
          | bind body =>
              exact prefix_prepend (ih world (CallState.captureBind k body) scopes n hn')
                (.requestBind world op payload k body observed fs view result scopes views receipts suffix)
          | adapter a b body =>
              exact prefix_prepend (ih world (CallState.captureBind k body) scopes n hn')
                (.requestAdapter world op payload k observed a b body fs view result scopes views receipts suffix)
          | scope owner =>
              exact prefix_prepend (ih (md.suspendScope world owner) (.scope owner k)
                (owner :: scopes) n hn') (.requestScope world owner op payload k observed fs view result scopes views receipts suffix)
          | expose e r =>
              exact prefix_prepend (ih (md.suspendView world e.identity) (.expose e r k)
                scopes n hn') (.requestExpose world e r op payload k observed fs view result scopes views receipts suffix)

/-- Exact endpoint inversion, with unrestricted metadata and world. -/
theorem call_request_prefix_exact (n : Nat) (hn : n ≤ frames.length + 1)
    (t : CallState W) :
    YulangClosure.Prefix (CallControlStep md) n
      ⟨world, .requesting op payload k observed, frames, view, result, scopes, views, receipts, suffix⟩ t ↔
    t = CallState.requestBoundary md n
      ⟨world, .requesting op payload k observed, frames, view, result, scopes, views, receipts, suffix⟩ := by
  constructor
  · intro hp; exact (request_prefix_unique hp True.intro).1
  · intro he; subst t
    exact call_request_prefix_realized md world op payload k observed frames view result scopes views receipts suffix n hn

/-- All actual finite prefixes satisfy the bound; it is not a premise. -/
theorem call_request_prefix_iff (n : Nat) (t : CallState W) :
    YulangClosure.Prefix (CallControlStep md) n
      ⟨world, .requesting op payload k observed, frames, view, result, scopes, views, receipts, suffix⟩ t ↔
    n ≤ frames.length + 1 ∧
      t = CallState.requestBoundary md n
        ⟨world, .requesting op payload k observed, frames, view, result, scopes, views, receipts, suffix⟩ := by
  constructor
  · intro hp
    have hr := request_prefix_rank hp True.intro
    refine ⟨?_, (request_prefix_unique hp True.intro).1⟩
    calc
      n ≤ n + requestRank t := Nat.le_add_right _ _
      _ = frames.length + 1 := hr
  · rintro ⟨hn, ht⟩
    exact (call_request_prefix_exact md world op payload k observed frames view result
      scopes views receipts suffix n hn t).2 ht

end

/-- World/scope actions are folded in the same innermost-first order as capture. -/
def CallState.requestWorldScopes {W : Type} (md : Metadata W) :
    List TypedCall.ContextFrame → W → List Nat → W × List Nat
  | [], w, ss => (w, ss)
  | .bind _ :: fs, w, ss => requestWorldScopes md fs w ss
  | .adapter _ _ _ :: fs, w, ss => requestWorldScopes md fs w ss
  | .scope owner :: fs, w, ss => requestWorldScopes md fs (md.suspendScope w owner) (owner :: ss)
  | .expose e _ :: fs, w, ss => requestWorldScopes md fs (md.suspendView w e.identity) ss

/-- An arbitrary consumed innermost segment leaves its literal residual frames.
The head still carries the original observed list; completion has not occurred. -/
theorem call_request_boundary_partial {W : Type} (md : Metadata W)
    (world : W) (op : TypedCall.OperationInstance) (payload : TypedCall.Value)
    (k : TypedCall.Comp) (observed : List TypedCall.ViewOccurrence)
    (consumed remaining : List TypedCall.ContextFrame) (view : TypedCall.CallView)
    (result : Original.Ty) (scopes : List Nat)
    (views : List TypedCall.ViewOccurrence) (receipts : List TypedCall.ReceiptSlot)
    (suffix : List Frame) :
    CallState.requestBoundary md consumed.length
      ⟨world, .requesting op payload k observed, consumed ++ remaining,
        view, result, scopes, views, receipts, suffix⟩ =
    ⟨(CallState.requestWorldScopes md consumed world scopes).1,
      .requesting op payload (CallState.captureFrames consumed k) observed,
      remaining, view, result, (CallState.requestWorldScopes md consumed world scopes).2,
      views, receipts, suffix⟩ := by
  induction consumed generalizing world k scopes with
  | nil => rfl
  | cons f fs ih =>
      rw [List.length_cons, boundary_shift]
      cases f <;> simpa only [List.cons_append, CallState.requestNext,
        CallState.captureFrames, CallState.requestWorldScopes] using ih _ _ _

/-- Processing exactly the frame count has not yet performed finishRequest. -/
theorem call_request_boundary_frames {W : Type} (md : Metadata W)
    (world : W) (op : TypedCall.OperationInstance) (payload : TypedCall.Value)
    (k : TypedCall.Comp) (observed : List TypedCall.ViewOccurrence)
    (frames : List TypedCall.ContextFrame) (view : TypedCall.CallView)
    (result : Original.Ty) (scopes : List Nat)
    (views : List TypedCall.ViewOccurrence) (receipts : List TypedCall.ReceiptSlot)
    (suffix : List Frame) :
    CallState.requestBoundary md frames.length
      ⟨world, .requesting op payload k observed, frames, view, result, scopes, views, receipts, suffix⟩ =
    ⟨(CallState.requestWorldScopes md frames world scopes).1,
      .requesting op payload (CallState.captureFrames frames k) observed,
      [], view, result, (CallState.requestWorldScopes md frames world scopes).2,
      views, receipts, suffix⟩ := by
  induction frames generalizing world k scopes with
  | nil => rfl
  | cons f fs ih =>
      rw [List.length_cons, boundary_shift]
      cases f <;> simpa only [CallState.requestNext, CallState.captureFrames,
        CallState.requestWorldScopes] using ih _ _ _

/-- Completion is precisely the one additional finishRequest transition. -/
theorem call_request_boundary_complete {W : Type} (md : Metadata W)
    (world : W) (op : TypedCall.OperationInstance) (payload : TypedCall.Value)
    (k : TypedCall.Comp) (observed : List TypedCall.ViewOccurrence)
    (frames : List TypedCall.ContextFrame) (view : TypedCall.CallView)
    (result : Original.Ty) (scopes : List Nat)
    (views : List TypedCall.ViewOccurrence) (receipts : List TypedCall.ReceiptSlot)
    (suffix : List Frame) :
    CallState.requestBoundary md (frames.length + 1)
      ⟨world, .requesting op payload k observed, frames, view, result, scopes, views, receipts, suffix⟩ =
    ⟨(CallState.requestWorldScopes md frames world scopes).1,
      .requested op payload (CallState.captureFrames frames k),
      [], view, result, (CallState.requestWorldScopes md frames world scopes).2,
      observed, receipts, suffix⟩ := by
  rw [CallState.requestBoundary, call_request_boundary_frames]
  rfl

/-- The complete finite-prefix classification in terms of the actual state. -/
theorem call_request_state_prefix_iff
    {W : Type} (md : Metadata W) {s : CallState W}
    {op : TypedCall.OperationInstance} {payload : TypedCall.Value}
    {k : TypedCall.Comp} {observed : List TypedCall.ViewOccurrence}
    (hhead : s.head = .requesting op payload k observed)
    (n : Nat) (t : CallState W) :
    YulangClosure.Prefix (CallControlStep md) n s t ↔
      n ≤ s.frames.length + 1 ∧ t = s.requestBoundary md n := by
  rcases s with ⟨world, head, frames, view, result, scopes, views, receipts, suffix⟩
  cases hhead
  exact call_request_prefix_iff md world op payload k observed frames view result
    scopes views receipts suffix n t

/-- The terminal state retains every field not changed by the actual request
constructors. In particular, metadata acts in the captured frame order. -/
theorem call_request_state_boundary_complete
    {W : Type} (md : Metadata W) {s : CallState W}
    {op : TypedCall.OperationInstance} {payload : TypedCall.Value}
    {k : TypedCall.Comp} {observed : List TypedCall.ViewOccurrence}
    (hhead : s.head = .requesting op payload k observed) :
    s.requestBoundary md (s.frames.length + 1) =
      { s with
        world := (CallState.requestWorldScopes md s.frames s.world s.scopeContext).1
        head := .requested op payload (CallState.captureFrames s.frames k)
        frames := []
        scopeContext := (CallState.requestWorldScopes md s.frames s.world s.scopeContext).2
        viewContext := observed } := by
  rcases s with ⟨world, head, frames, view, result, scopes, views, receipts, suffix⟩
  cases hhead
  exact call_request_boundary_complete md world op payload k observed frames view result
    scopes views receipts suffix

/-- No step leaves a requested boundary in the represented Call relation. -/
theorem call_requested_no_step
    {W : Type} {md : Metadata W} {s t : CallState W}
    {op : TypedCall.OperationInstance} {payload : TypedCall.Value} {k : TypedCall.Comp}
    (hhead : s.head = .requested op payload k) : ¬ CallControlStep md s t := by
  intro hs
  cases hs <;> simp_all [CallState.initial]

/-- Among all actual prefixes, requested completion occurs exactly after one
step per original frame and the final finishRequest step. -/
theorem call_request_completion_iff
    {W : Type} {md : Metadata W} {s t : CallState W} {n : Nat}
    {op : TypedCall.OperationInstance} {payload : TypedCall.Value}
    {k : TypedCall.Comp} {observed : List TypedCall.ViewOccurrence}
    (hhead : s.head = .requesting op payload k observed)
    (hp : YulangClosure.Prefix (CallControlStep md) n s t) :
    (∃ op' payload' k', t.head = .requested op' payload' k') ↔
      n = s.frames.length + 1 := by
  constructor
  · rintro ⟨op', payload', k', ht⟩
    have hr : RequestRegion s := by simp only [RequestRegion, hhead]
    have hcount := request_prefix_rank hp hr
    simpa only [requestRank, hhead, ht, Nat.add_zero] using hcount
  · intro hn
    have ht := ((call_request_state_prefix_iff md hhead n t).1 hp).2
    rw [hn] at ht
    rw [ht, call_request_state_boundary_complete md hhead]
    exact ⟨op, payload, CallState.captureFrames s.frames k, rfl⟩

end YulangClosure.Control
