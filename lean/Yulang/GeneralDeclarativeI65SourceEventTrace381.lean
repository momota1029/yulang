import Yulang.GeneralDeclarativeI65State365
import Yulang.CommonRoleOutermostResolver

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open CommonRoleOutermostResolver (All₂ Frontier Tree Dictionary Result Resolves Summarizes)

/-- Structural interface for an independent per-source event relation,
not the definition of generalized Classifies or a validator. The
particular relation must still be implemented from actual source
rules and independently retained authority for the same fixed state. -/
def ProjectEventRule381 {Event : Type u}
    (rule : Request → Frontier Request → Event → Prop) (q : Request)
    (f : Frontier Request) : Prop :=
  ∃ event, rule q f event

mutual
inductive SourceEventTrace381 {Event : Type u}
    (rule : Request → Frontier Request → Event → Prop) : Request → Tree → Type u where
  | pending (event : Event) : rule q .pending event → SourceEventTrace381 rule q .pending
  | ambiguous (event : Event) : rule q .ambiguous event → SourceEventTrace381 rule q .ambiguous
  | rejected (event : Event) : rule q .rejected event → SourceEventTrace381 rule q .rejected
  | selected (event : Event) : rule q (.selected key kids) event →
      SourceEventForest381 rule kids trees → SourceEventTrace381 rule q (.selected key trees)

inductive SourceEventForest381 {Event : Type u}
    (rule : Request → Frontier Request → Event → Prop) : List Request → List Tree → Type u where
  | nil : SourceEventForest381 rule [] []
  | cons : SourceEventTrace381 rule q t → SourceEventForest381 rule qs ts →
      SourceEventForest381 rule (q::qs) (t::ts)
end

/-- The explicit event values are stored in data; projecting to an
ordinary finite diagnostic derivation preserves every request, the
exact selected key, and the full ordered child list. -/
theorem explicit_source_events_project381 {Event : Type u}
    {rule : Request → Frontier Request → Event → Prop} {q : Request} {t : Tree}
    (trace : SourceEventTrace381 rule q t) :
    Resolves (ProjectEventRule381 rule) q t := by
  exact SourceEventTrace381.rec
    (motive_1 := fun q t _ => Resolves (ProjectEventRule381 rule) q t)
    (motive_2 := fun qs ts _ => All₂ (Resolves (ProjectEventRule381 rule)) qs ts)
    (fun e witness => .pending ⟨e,witness⟩)
    (fun e witness => .ambiguous ⟨e,witness⟩)
    (fun e witness => .rejected ⟨e,witness⟩)
    (fun e witness _ ih => .selected ⟨e,witness⟩ ih)
    .nil
    (fun _ _ ih here => .cons ih here)
    trace

section
variable {Event : Type u} {rule : Request → Frontier Request → Event → Prop}

mutual
/-- Only existence of a trace is recovered here. If distinct original
events project to the same frontier, this theorem does not recover a
particular erased event, writer or compiler receipt. -/
theorem source_event_trace_exists381 (t : Tree)
    (derived : Resolves (ProjectEventRule381 rule) q t) :
    Nonempty (SourceEventTrace381 rule q t) := by
  cases derived with
  | pending h => obtain ⟨e,proof⟩ := h; exact ⟨.pending e proof⟩
  | ambiguous h => obtain ⟨e,proof⟩ := h; exact ⟨.ambiguous e proof⟩
  | rejected h => obtain ⟨e,proof⟩ := h; exact ⟨.rejected e proof⟩
  | selected h kids =>
    obtain ⟨e,proof⟩ := h
    obtain ⟨trace⟩ := source_event_forest_exists381 _ kids
    exact ⟨.selected e proof trace⟩
termination_by sizeOf t

theorem source_event_forest_exists381 (ts : List Tree)
    (derived : All₂ (Resolves (ProjectEventRule381 rule)) qs ts) :
    Nonempty (SourceEventForest381 rule qs ts) := by
  cases derived with
  | nil => exact ⟨.nil⟩
  | cons now more =>
    obtain ⟨nowTrace⟩ := source_event_trace_exists381 _ now
    obtain ⟨moreTrace⟩ := source_event_forest_exists381 _ more
    exact ⟨.cons nowTrace moreTrace⟩
termination_by sizeOf ts
end

/-- Pure structural piece for S01. This projects an already supplied
event-bearing independent classification derivation. It neither makes
one using an arbitrary `rule` nor attaches an external authority. -/
theorem classify_from_explicit_source_events381 {q : Request} {t : Tree}
    {r : Result} (trace : SourceEventTrace381 rule q t) (summary : Summarizes t r) :
    CommonRoleOutermostResolver.Classify (ProjectEventRule381 rule) q r :=
  ⟨t,explicit_source_events_project381 trace,summary⟩

/-- This is S01's outer shape for a supplied independent source-event
relation, not the all-state S01. Neither the identity nor the authority
of an erased concrete event follows from the returned existence. -/
theorem event_classification_unpacks381 {q : Request} {d : Dictionary}
    (h : CommonRoleOutermostResolver.Classify (ProjectEventRule381 rule) q (.selected d)) :
    ∃ t : Tree, Resolves (ProjectEventRule381 rule) q t ∧
      Nonempty (SourceEventTrace381 rule q t) ∧ Summarizes t (.selected d) := by
  obtain ⟨t,derived,summary⟩ := h
  exact ⟨t,derived,source_event_trace_exists381 t derived,summary⟩

end

def rootSourceEvent381 {Event : Type u}
    {rule : Request → Frontier Request → Event → Prop} {q : Request} {t : Tree} :
    SourceEventTrace381 rule q t → Event
  | .pending e _ | .ambiguous e _ | .rejected e _ | .selected e _ _ => e

/-- Exact same outer selected node and child trace need not identify the
parent event. This negative theorem is conditional on two independently
allowed events. It does not assert that any approved source admits such
an ambiguity; it shows what information a projection cannot recover. -/
theorem root_event_no_diagnostic_recovery381 {Event : Type u}
    {rule : Request → Frontier Request → Event → Prop} {q : Request} {key : Nat}
    {kids : List Request} {ts : List Tree} {a b : Event}
    (first : rule q (.selected key kids) a) (second : rule q (.selected key kids) b)
    (different : a ≠ b) (children : SourceEventForest381 rule kids ts)
    (recover : Request → Tree → Event) :
    ¬ (∀ {r : Request} {t : Tree} (trace : SourceEventTrace381 rule r t),
      recover r t = rootSourceEvent381 trace) := by
  intro promise
  have x := promise (.selected a first children)
  have y := promise (.selected b second children)
  exact different (x.symm.trans y)

end Yulang.GeneralDeclarativeI65
