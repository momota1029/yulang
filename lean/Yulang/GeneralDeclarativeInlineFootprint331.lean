import Yulang.GeneralDeclarativeInlineGround331

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeInlineFootprint331
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeLowerKnown321 (Alias)
open GeneralDeclarativeRecordSpine330 (Spine)
open GeneralDeclarativeInlineSpine331 (Closed)

-- Normal interval facts are deliberately held fixed. This record
-- does not claim that the origin of a normal atom can be recovered
-- from its truth in the ordinary model set.
def Replay (s : State) (P : State → Prop) : Prop :=
  ∃ uses : List Equation, uses ⊆ s.equations ∧
    ∀ t, s.normal = t.normal → uses ⊆ t.equations → P t

theorem pure (p : ∀ t, P t) : Replay s P :=
  ⟨[],fun _ absent => False.elim (List.not_mem_nil absent),fun t _ _ => p t⟩

theorem map (use : Replay s P) (f : ∀ t, P t → Q t) : Replay s Q := by
  obtain ⟨rows,inside,replay⟩ := use
  exact ⟨rows,inside,fun t normal known => f t (replay t normal known)⟩

theorem combine (left : Replay s P) (right : Replay s Q) :
    Replay s (fun t => P t ∧ Q t) := by
  obtain ⟨need,fromFirst,first⟩ := left
  obtain ⟨uses,fromLast,last⟩ := right
  refine ⟨need++uses,fun _ h => (List.mem_append.mp h).elim (fun row => fromFirst row) (fun row => fromLast row),?_⟩
  intro t tracks stored
  exact ⟨first t tracks (fun _ sub => stored (List.mem_append_left _ sub)),
    last t tracks (fun _ sub => stored (List.mem_append_right _ sub))⟩

theorem exact_row (known : row ∈ s.equations) : Replay s (fun t => row ∈ t.equations) :=
  ⟨[row],fun _ h => (List.mem_singleton.mp h).symm ▸ known,fun _ _ listed => listed List.mem_cons_self⟩

theorem alias {s : State} (known : Alias s a b) : Replay s (fun t => Alias t a b) := by
  induction known with
  | bounds x y =>
    exact ⟨[],fun _ h => False.elim (List.not_mem_nil h),fun _ h _ => .bounds (h ▸ x) (h ▸ y)⟩
  | forward row => exact map (exact_row row) (fun _ => .forward)
  | backward row => exact map (exact_row row) (fun _ => .backward)
  | trans _ _ x y => exact map (combine x y) (fun _ h => .trans h.1 h.2)

theorem spine {s : State} (known : Spine s n raw terminal) :
    Replay s (fun t => Spine t n raw terminal) := by
  induction known with
  | width link row => exact map (combine (alias link) (exact_row row)) (fun _ h => .width h.1 h.2)
  | exactEnd link row => exact map (combine (alias link) (exact_row row)) (fun _ h => .exactEnd h.1 h.2)
  | cons link row _ tail =>
    exact map (combine (combine (alias link) (exact_row row)) tail)
      (fun _ h => .cons h.1.1 h.1.2 h.2)
  | inline link endCode row => exact map (combine (alias link) (exact_row row)) (fun _ h => .inline h.1 endCode h.2)
  | prefixed link row _ tail =>
    exact map (combine (combine (alias link) (exact_row row)) tail)
      (fun _ h => .prefixed h.1.1 h.1.2 h.2)

theorem closed {s : State} (known : Closed s e raw terminal) :
    Replay s (fun t => Closed t e raw terminal) := by
  induction known with
  | terminal t => exact pure (fun _ => .terminal t)
  | field _ suffix => exact map suffix (fun _ => .field)
  | name yes => exact map (spine yes) (fun _ => .name)

open GeneralDeclarativeInlineTrace331 (Read Args Fields)

/-- Collect the finite equation premises used by this actual trace
and its alias paths and closed tails. No unrelated row in the current
state is added to the requirement. Other witnesses can use different
rows; minimality or a global observational algorithm is not asserted. -/
theorem trace {s : State} (known : Read s mode raw code seen) :
    Replay s (fun t => Read t mode raw code seen) := by
  refine Read.rec
    (motive_1 := fun mode raw code seen _ => Replay s (fun t => Read t mode raw code seen))
    (motive_2 := fun mode raw codes seen _ => Replay s (fun t => Args t mode raw codes seen))
    (motive_3 := fun mode raw codes seen _ => Replay s (fun t => Fields t mode raw codes seen))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ known
  · intro _ _ _
    exact pure (fun _ => .capture)
  · intro _ _ _ _ _ _ nonvar link row _ caseRead
    exact map (combine (combine (alias link) (exact_row row)) caseRead)
      (fun _ h => .expose nonvar h.1.1 h.1.2 h.2)
  · intro _ _ _ _ _ _ xs
    exact map xs (fun _ => .primitive)
  · intro _ _ _ _ _ _ xs
    exact map xs (fun _ => .nominal)
  · intro _ _ _ _ _ _ sub
    exact map sub (fun _ => .variant)
  · intro _ _ _ _ _ _ _ _ _ x y
    exact map (combine x y) (fun _ h => .join h.1 h.2)
  · intro _ _ _ _ _ _ _ _ _ _ raw disj nonempty ordered _ tail _ first last
    exact map (combine (combine (closed raw) first) last)
      (fun _ h => .record h.1.1 disj nonempty ordered h.1.2 tail h.2)
  · intro _
    exact pure (fun _ => .nil)
  · intro _ _ _ _ _ _ _ _ _ one many
    exact map (combine one many) (fun _ h => .cons h.1 h.2)
  · intro _
    exact pure (fun _ => .nil)
  · intro _ _ _ _ _ _ _ _ _ _ one many
    exact map (combine one many) (fun _ h => .cons h.1 h.2)

end Yulang.GeneralDeclarativeInlineFootprint331
