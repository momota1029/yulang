import YulangClosure.ControlComposition

/-! Concrete Original-to-Control bridge for LEAN-CORE-CONTROL-BRIDGE-20261024/r3.
The boundary delimits one source segment from an arbitrary existing Control
suffix. Source execution and the explicit boundary exit are distinguished.
No registered-body safety premise occurs in these theorems. -/
namespace YulangClosure.CoreControlBridge

def frame : Original.Frame → Control.Frame
  | .bind body => .originalBind body

def frames (fs : List Original.Frame) : List Control.Frame := fs.map frame

def embed (world : W) (source : Original.State) (suffix : List Control.Frame) :
    Control.State W :=
  ⟨world, .original source.current, frames source.stack ++ [.originalBoundary] ++ suffix⟩

def exit (world : W) (value : Original.Val) (suffix : List Control.Frame) :
    Control.State W := ⟨world, .ret (.originalValue value), suffix⟩

theorem value_typed (h : Original.ValTyped Original.emptyContext v a) :
    Control.ValueTyped (.originalValue v) (.original a) := .original h

theorem embed_typed {sig : Control.Signature}
    (h : Original.StateTyped Original.emptyContext a source)
    (hs : Control.FramesTyped sig suffix (.original a) result) (world : W) :
    Control.SegmentTyped sig (embed world source suffix) result :=
  ⟨a, source, suffix, rfl, rfl, h, hs⟩

theorem exit_typed {sig : Control.Signature}
    (h : Original.ValTyped Original.emptyContext v a)
    (hs : Control.FramesTyped sig suffix (.original a) result) (world : W) :
    Control.StateTyped sig (exit world v suffix) result :=
  ⟨.original a, .ret (value_typed h), hs⟩

/-- Entry adds the actual syntax-bearing frame before the literal old suffix. -/
theorem entry {md : Control.Metadata W} (world : W) (m n : Original.Comp)
    (fs : List Original.Frame) (suffix : List Control.Frame) :
    Control.ControlStep md (embed world ⟨.bind m n, fs⟩ suffix)
      (embed world ⟨m, .bind n :: fs⟩ suffix) := .originalEnter

/-- Return uses the actual existing substitution, not an assumed body law. -/
theorem return_bind {md : Control.Metadata W} (world : W) (v : Original.Val)
    (n : Original.Comp) (fs : List Original.Frame) (suffix : List Control.Frame) :
    Control.ControlStep md (embed world ⟨.ret v, .bind n :: fs⟩ suffix)
      (embed world ⟨Original.substComp (Original.single v) n, fs⟩ suffix) :=
  .originalReturnBind

theorem principal {md : Control.Metadata W} (world : W)
    (h : Original.Principal m n) (fs : List Original.Frame)
    (suffix : List Control.Frame) :
    Control.ControlStep md (embed world ⟨m, fs⟩ suffix)
      (embed world ⟨n, fs⟩ suffix) := .originalPrincipal h

theorem step {md : Control.Metadata W}
    {body : W → Nat → List Control.Value → Option Control.Kont → W → Control.Head → Prop}
    (h : Original.Step s t) (world : W) (suffix : List Control.Frame) :
    Control.Step md body (embed world s suffix) (embed world t suffix) := by
  cases h with
  | enter => exact .control (entry world _ _ _ suffix)
  | returnBind => exact .control (return_bind world _ _ _ suffix)
  | principal hp => exact .control (principal world hp _ suffix)

theorem boundary_exit {md : Control.Metadata W}
    {body : W → Nat → List Control.Value → Option Control.Kont → W → Control.Head → Prop}
    (world : W) (v : Original.Val) (suffix : List Control.Frame) :
    Control.Step md body (embed world ⟨.ret v, []⟩ suffix) (exit world v suffix) :=
  .control .originalExit

/-- Every successor of the delimited family is a source step or its one
explicit terminal handoff. This quantifies all metadata and registered bodies. -/
theorem successor_coverage {md : Control.Metadata W}
    {body : W → Nat → List Control.Value → Option Control.Kont → W → Control.Head → Prop}
    {source : Original.State} {target : Control.State W} {world : W}
    {suffix : List Control.Frame}
    (h : Control.Step md body (embed world source suffix) target) :
    (∃ next, target = embed world next suffix ∧ Original.Step source next) ∨
      (∃ value, source = ⟨.ret value, []⟩ ∧ target = exit world value suffix) := by
  cases source with | mk current stack =>
    cases stack with
    | nil =>
      change Control.Step md body
        ⟨world, .original current, .originalBoundary :: suffix⟩ target at h
      cases h with
      | control hc =>
        cases hc with
        | originalEnter => exact .inl ⟨_, rfl, .enter⟩
        | originalPrincipal hp => exact .inl ⟨_, rfl, .principal hp⟩
        | originalExit => exact .inr ⟨_, rfl, rfl⟩
    | cons f fs =>
      cases f with | bind n =>
        change Control.Step md body
          ⟨world, .original current,
            .originalBind n :: ((frames fs ++ [.originalBoundary]) ++ suffix)⟩ target at h
        cases h with
        | control hc =>
          cases hc with
          | originalEnter => exact .inl ⟨_, rfl, .enter⟩
          | originalReturnBind => exact .inl ⟨_, rfl, .returnBind⟩
          | originalPrincipal hp => exact .inl ⟨_, rfl, .principal hp⟩

theorem segment_representation {sig : Control.Signature} {s : Control.State W}
    (h : Control.SegmentTyped sig s result) :
    ∃ a source suffix, s = embed s.world source suffix ∧
      Original.StateTyped Original.emptyContext a source ∧
      Control.FramesTyped sig suffix (.original a) result := by
  obtain ⟨a, source, suffix, hh, hs, ht, hf⟩ := h
  cases s with | mk world head stack =>
    cases hh
    cases hs
    exact ⟨a, source, suffix, rfl, ht, hf⟩

/-- Preservation changes typing domains only at the explicit boundary exit.
The source preservation premise is the already proved actual substitution
theorem, not a newly assumed relation on the same syntax. -/
theorem segment_preservation {sig : Control.Signature} {md : Control.Metadata W}
    {body : W → Nat → List Control.Value → Option Control.Kont → W → Control.Head → Prop}
    (ht : Control.SegmentTyped sig s result) (hx : Control.Step md body s t) :
    Control.SegmentTyped sig t result ∨ Control.StateTyped sig t result := by
  obtain ⟨a, source, suffix, he, hsource, hsuffix⟩ := segment_representation ht
  rw [he] at hx
  cases successor_coverage hx with
  | inl hi =>
    obtain ⟨next, hn, hp⟩ := hi
    rw [hn]
    exact .inl (embed_typed (Original.step_preservation hp hsource) hsuffix s.world)
  | inr hi =>
    obtain ⟨value, hs, hn⟩ := hi
    rw [hs] at hsource
    obtain ⟨hole, hm, hf⟩ := hsource
    cases hf
    cases hm with | ret hv =>
      rw [hn]
      exact .inr (exit_typed hv hsuffix s.world)

/-- All source prefixes transfer with their exact length, world and old suffix. -/
theorem finite_transfer {md : Control.Metadata W}
    {body : W → Nat → List Control.Value → Option Control.Kont → W → Control.Head → Prop}
    (h : Prefix Original.Step n s t) (world : W) (suffix : List Control.Frame) :
    Prefix (Control.Step md body) n (embed world s suffix) (embed world t suffix) := by
  induction h with
  | refl => exact .refl _
  | snoc hp hx ih => exact .snoc ih (step hx world suffix)

/-- Keep the dependent start index variable during prefix induction. The
embedding equality is introduced only after the induction hypothesis exists. -/
private theorem finite_coverage_from {md : Control.Metadata W}
    {body : W → Nat → List Control.Value → Option Control.Kont → W → Control.Head → Prop}
    {source : Original.State} {start target : Control.State W} {world : W}
    {suffix : List Control.Frame}
    (h : Prefix (Control.Step md body) n start target) :
    start = embed world source suffix →
    (∃ next, target = embed world next suffix ∧ Prefix Original.Step n source next) ∨
      (∃ k l value, n = k + 1 + l ∧
        Prefix Original.Step k source ⟨.ret value, []⟩ ∧
        Prefix (Control.Step md body) l (exit world value suffix) target) := by
  induction h with
  | refl =>
    intro initial
    exact .inl ⟨source, initial, .refl _⟩
  | snoc hp hx ih =>
    intro initial
    cases ih initial with
    | inl hi =>
      obtain ⟨next, he, hs⟩ := hi
      rw [he] at hx
      cases successor_coverage hx with
      | inl hi =>
        obtain ⟨last, he, hl⟩ := hi
        exact .inl ⟨last, he, .snoc hs hl⟩
      | inr hi =>
        obtain ⟨value, he, ht⟩ := hi
        rw [he] at hs
        exact .inr ⟨_, 0, value, rfl, hs, by rw [ht]; exact .refl _⟩
    | inr hi =>
      obtain ⟨k, l, value, hn, hs, ht⟩ := hi
      exact .inr ⟨k, l+1, value, by rw [hn]; rfl, hs, .snoc ht hx⟩

/-- Exhaustive classification of arbitrary finite Control traces. Before the
exit, all steps are Original steps. After exit, the suffix executes under the
ordinary Control relation; no foreign execution is relabeled Original. -/
theorem finite_coverage {md : Control.Metadata W}
    {body : W → Nat → List Control.Value → Option Control.Kont → W → Control.Head → Prop}
    {source : Original.State} {target : Control.State W} {world : W}
    {suffix : List Control.Frame}
    (h : Prefix (Control.Step md body) n (embed world source suffix) target) :
    (∃ next, target = embed world next suffix ∧ Prefix Original.Step n source next) ∨
      (∃ k l value, n = k + 1 + l ∧
        Prefix Original.Step k source ⟨.ret value, []⟩ ∧
        Prefix (Control.Step md body) l (exit world value suffix) target) := by
  exact finite_coverage_from h rfl

/-- A legal external resumption cannot occur at an Original head. This checks
the actual suspended predicate instead of assuming foreign responses away. -/
theorem machine_successor_coverage {md : Control.Metadata W}
    {body : W → Nat → List Control.Value → Option Control.Kont → W → Control.Head → Prop}
    {source : Original.State} {target : Control.State W} {world : W}
    {suffix : List Control.Frame}
    (h : YulangClosure.Step (Control.machine md body)
      (embed world source suffix) target) :
    (∃ next, target = embed world next suffix ∧ Original.Step source next) ∨
      (∃ value, source = ⟨.ret value, []⟩ ∧ target = exit world value suffix) := by
  cases h with
  | internal hi => exact successor_coverage hi
  | resume hsp hc ha hr =>
    obtain ⟨event, operation, payload, he, hs⟩ := hsp
    cases he

theorem machine_finite_transfer {md : Control.Metadata W}
    {body : W → Nat → List Control.Value → Option Control.Kont → W → Control.Head → Prop}
    (h : Prefix Original.Step n s t) (world : W) (suffix : List Control.Frame) :
    Prefix (YulangClosure.Step (Control.machine md body)) n
      (embed world s suffix) (embed world t suffix) := by
  induction h with
  | refl => exact .refl _
  | snoc hp hx ih => exact .snoc ih (.internal (step hx world suffix))

/-- The root-machine variant retains arbitrary legal foreign responses after
exit, with the same variable-index induction as internal coverage. -/
private theorem machine_finite_coverage_from {md : Control.Metadata W}
    {body : W → Nat → List Control.Value → Option Control.Kont → W → Control.Head → Prop}
    {source : Original.State} {start target : Control.State W} {world : W}
    {suffix : List Control.Frame}
    (h : Prefix (YulangClosure.Step (Control.machine md body)) n start target) :
    start = embed world source suffix →
    (∃ next, target = embed world next suffix ∧ Prefix Original.Step n source next) ∨
      (∃ k l value, n = k + 1 + l ∧
        Prefix Original.Step k source ⟨.ret value, []⟩ ∧
        Prefix (YulangClosure.Step (Control.machine md body)) l
          (exit world value suffix) target) := by
  induction h with
  | refl =>
    intro initial
    exact .inl ⟨source, initial, .refl _⟩
  | snoc hp hx ih =>
    intro initial
    cases ih initial with
    | inl hi =>
      obtain ⟨next, he, hs⟩ := hi
      rw [he] at hx
      cases machine_successor_coverage hx with
      | inl hi =>
        obtain ⟨last, he, hl⟩ := hi
        exact .inl ⟨last, he, .snoc hs hl⟩
      | inr hi =>
        obtain ⟨value, he, ht⟩ := hi
        rw [he] at hs
        exact .inr ⟨_, 0, value, rfl, hs, by rw [ht]; exact .refl _⟩
    | inr hi =>
      obtain ⟨k, l, value, hn, hs, ht⟩ := hi
      exact .inr ⟨k, l+1, value, by rw [hn]; rfl, hs, .snoc ht hx⟩

/-- Full root-machine prefixes retain all independent legal external responses
in the post-exit foreign trace, without treating that trace as source execution. -/
theorem machine_finite_coverage {md : Control.Metadata W}
    {body : W → Nat → List Control.Value → Option Control.Kont → W → Control.Head → Prop}
    {source : Original.State} {target : Control.State W} {world : W}
    {suffix : List Control.Frame}
    (h : Prefix (YulangClosure.Step (Control.machine md body)) n
      (embed world source suffix) target) :
    (∃ next, target = embed world next suffix ∧ Prefix Original.Step n source next) ∨
      (∃ k l value, n = k + 1 + l ∧
        Prefix Original.Step k source ⟨.ret value, []⟩ ∧
        Prefix (YulangClosure.Step (Control.machine md body)) l
          (exit world value suffix) target) := by
  exact machine_finite_coverage_from h rfl

/-- Original preservation for the shared length-indexed prefix relation.
The initial typing premise is part of the induction motive. -/
private theorem original_prefix_preservation
    (h : Prefix Original.Step n s t) :
    Original.StateTyped env a s → Original.StateTyped env a t := by
  induction h with
  | refl => exact fun ht => ht
  | snoc hp hx ih =>
    intro ht
    exact Original.step_preservation hx (ih ht)

/-- Applying the bridge to the original typed parent: every transferred prefix
has segment typing from Original preservation and independent suffix typing. -/
theorem finite_typed_transfer {sig : Control.Signature} {md : Control.Metadata W}
    {body : W → Nat → List Control.Value → Option Control.Kont → W → Control.Head → Prop}
    (ht : Original.StateTyped Original.emptyContext a s)
    (hs : Control.FramesTyped sig suffix (.original a) result)
    (h : Prefix Original.Step n s t) (world : W) :
    Prefix (Control.Step md body) n (embed world s suffix) (embed world t suffix) ∧
      Control.SegmentTyped sig (embed world t suffix) result := by
  have typed := original_prefix_preservation h ht
  exact ⟨finite_transfer h world suffix, embed_typed typed hs world⟩

theorem exit_empty_no_step {md : Control.Metadata W}
    {body : W → Nat → List Control.Value → Option Control.Kont → W → Control.Head → Prop}
    {world : W} {value : Original.Val} {target : Control.State W}
    (h : Control.Step md body (exit world value []) target) : False := by
  cases h with
  | control hc => cases hc

/-- A finite prefix from a state with no successors is stationary. -/
private theorem prefix_eq_of_no_step {C : Type} {relation : C → C → Prop}
    {start target : C} (h : Prefix relation n start target) :
    (∀ next, ¬ relation start next) → target = start := by
  induction h with
  | refl => intro _; rfl
  | snoc hp hx ih =>
    intro noStep
    have he := ih noStep
    rw [he] at hx
    exact (noStep _ hx).elim

theorem exit_empty_prefix {md : Control.Metadata W}
    {body : W → Nat → List Control.Value → Option Control.Kont → W → Control.Head → Prop}
    {world : W} {value : Original.Val} {target : Control.State W}
    (h : Prefix (Control.Step md body) n (exit world value []) target) :
    target = exit world value [] := by
  exact prefix_eq_of_no_step h (fun _ hx => exit_empty_no_step hx)

/-- Actual all-successor finite safety for a closed embedded source program.
With an empty foreign suffix, the explicit exit is an ordinary terminal return;
registered-code BodyLaws are unnecessary throughout the entire trace. -/
theorem finite_closed_safety {sig : Control.Signature} {md : Control.Metadata W}
    {body : W → Nat → List Control.Value → Option Control.Kont → W → Control.Head → Prop}
    {world : W} {target : Control.State W}
    (ht : Original.StateTyped Original.emptyContext a source)
    (h : Prefix (Control.Step md body) n (embed world source []) target) :
    (Control.SegmentTyped sig target (.original a) ∨
      Control.StateTyped sig target (.original a)) ∧
      (∀ reason, target.head ≠ .bad reason) ∧
      ((∃ value, target = exit world value [] ∧
          Original.ValTyped Original.emptyContext value a) ∨
        ∃ next, Control.Step md body target next) := by
  cases finite_coverage h with
  | inl hi =>
    obtain ⟨next, he, hp⟩ := hi
    have typed := original_prefix_preservation hp ht
    have ct : Control.SegmentTyped sig target (.original a) := by
      rw [he]
      exact embed_typed typed .nil world
    refine ⟨.inl ct, ?_, .inr ?_⟩
    · rw [he]
      intro reason hbad
      cases hbad
    · cases Original.progress typed with
      | inl hr =>
        obtain ⟨value, hn, hv⟩ := hr
        rw [he, hn]
        exact ⟨_, boundary_exit world value []⟩
      | inr hr =>
        obtain ⟨last, hx⟩ := hr
        rw [he]
        exact ⟨_, step hx world []⟩
  | inr hi =>
    obtain ⟨k, l, value, hn, hp, tail⟩ := hi
    have typed := original_prefix_preservation hp ht
    obtain ⟨hole, hm, hf⟩ := typed
    cases hf
    cases hm with | ret hv =>
      have he := exit_empty_prefix tail
      have ct : Control.StateTyped sig target (.original a) := by
        rw [he]
        exact exit_typed hv .nil world
      exact ⟨.inr ct, Control.typed_not_bad ct, .inl ⟨value, he, hv⟩⟩

/-! This bridge does not establish full source initialization, Call/wrap/Resume,
all raw constructors, metadata observations, native correspondence, source-scoped
coverage, principality, termination, or the original inference A/B obligations.
Its fixed-context typing is exactly the existing closed Original fragment. -/
end YulangClosure.CoreControlBridge
