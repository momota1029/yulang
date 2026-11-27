import Yulang.GeneralDeclarativeGraphRows321
import Yulang.GeneralDeclarativeK2Alias321

namespace Yulang.GeneralDeclarativeI65.I72.PreparationFootprint467
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeK2Graph321 (View Descends Path aliasView)
open GeneralDeclarativeLowerKnown321 (Alias)
open GeneralDeclarativeK2Alias321 (AliasCycle)

structure ObservedFootprint (view : View) (live : Nat → Prop) : Prop where
  owner : ∀ {a shape}, view a shape → live a
  child : ∀ {a b shape}, view a shape → b ∈ shape.children → live b

theorem descends_from_pinned_owner
    {s t : State} {view : View} {live : Nat → Prop}
    (foot : ObservedFootprint view live)
    (agreement : ∀ a b, live a → live b → (Alias s a b ↔ Alias t a b))
    {a b : Nat} (ha : live a) :
    Descends (aliasView s view) a b ↔ Descends (aliasView t view) a b := by
  constructor
  · rintro ⟨shape,⟨owner,links,seen⟩,child⟩
    exact ⟨shape,⟨owner,(agreement a owner ha (foot.owner seen)).mp links,seen⟩,child⟩
  · rintro ⟨shape,⟨owner,links,seen⟩,child⟩
    exact ⟨shape,⟨owner,(agreement a owner ha (foot.owner seen)).mpr links,seen⟩,child⟩

theorem descends_arrives_in_footprint
    {s : State} {view : View} {live : Nat → Prop}
    (foot : ObservedFootprint view live) {a b : Nat}
    (d : Descends (aliasView s view) a b) : live b := by
  obtain ⟨shape,⟨owner,_links,seen⟩,child⟩ := d
  exact foot.child seen child

theorem path_from_pinned_owner_transports
    {s t : State} {view : View} {live : Nat → Prop}
    (foot : ObservedFootprint view live)
    (agreement : ∀ a b, live a → live b → (Alias s a b ↔ Alias t a b))
    {a b : Nat} (p : Path (aliasView s view) a b) :
    live a → Path (aliasView t view) a b ∧ live b := by
  induction p with
  | refl a => exact fun ha => ⟨.refl a,ha⟩
  | @next x y z edge rest ih =>
    intro hx
    obtain ⟨back,hz⟩ := ih (descends_arrives_in_footprint foot edge)
    exact ⟨.next ((descends_from_pinned_owner foot agreement hx).mp edge) back,hz⟩

theorem raw_cycles_at_original_footprint_depend_only_on_restricted_alias
    {s t : State} {view : View} {live : Nat → Prop}
    (foot : ObservedFootprint view live)
    (agreement : ∀ a b, live a → live b → (Alias s a b ↔ Alias t a b))
    {root : Nat} (hr : live root) :
    AliasCycle s view root ↔ AliasCycle t view root := by
  have oneWay (s t : State)
      (eqs : ∀ a b, live a → live b → (Alias s a b ↔ Alias t a b))
      (h : AliasCycle s view root) : AliasCycle t view root := by
    obtain ⟨first,last,edge,rest,close⟩ := h
    obtain ⟨back,hl⟩ := path_from_pinned_owner_transports foot eqs rest
      (descends_arrives_in_footprint foot edge)
    exact ⟨first,last,(descends_from_pinned_owner foot eqs hr).mp edge,back,
      (eqs last root hl hr).mp close⟩
  exact ⟨oneWay s t agreement,oneWay t s (fun a b ha hb => (agreement a b ha hb).symm)⟩

theorem raw_cycles_with_same_existing_rows_and_restricted_alias
    {s t : State} {live : Nat → Prop} {root : Nat}
    (sameRows : s.equations = t.equations)
    (foot : ObservedFootprint (GeneralDeclarativeGraphRows321.observed s) live)
    (agreement : ∀ a b, live a → live b → (Alias s a b ↔ Alias t a b))
    (hr : live root) :
    AliasCycle s (GeneralDeclarativeGraphRows321.observed s) root ↔
    AliasCycle t (GeneralDeclarativeGraphRows321.observed t) root := by
  have views : GeneralDeclarativeGraphRows321.observed s =
      GeneralDeclarativeGraphRows321.observed t := by
    funext a shape
    unfold GeneralDeclarativeGraphRows321.observed
    rw [sameRows]
  rw [← views]
  exact raw_cycles_at_original_footprint_depend_only_on_restricted_alias foot agreement hr



open GeneralDeclarativeBounds319 (Bound)
open GeneralDeclarativeHead320 (Equation)

/-- A projection back to already supplied names at the two explicit
ordinary snapshots. No endpoint or native issuer follows from it. -/
structure OrdinaryRetraction (s t : State) (p : Nat → Nat) : Prop where
  backInterval : ∀ {a b}, (a,b) ∈ t.normal.intervals → Bound s.normal (p a) (p b)
  backAtom : ∀ {a b}, PresenceNormalForm.Atom.tyLe (.var a) (.var b) ∈ t.normal.ordinary →
    Bound s.normal (p a) (p b)
  backVariable : ∀ {a b}, (⟨a,.variable b⟩ : Equation) ∈ t.equations → Alias s (p a) (p b)
  forwardInterval : ∀ {a b}, (a,b) ∈ s.normal.intervals → Bound t.normal a b
  forwardAtom : ∀ {a b}, PresenceNormalForm.Atom.tyLe (.var a) (.var b) ∈ s.normal.ordinary →
    Bound t.normal a b
  forwardVariable : ∀ {a b}, (⟨a,.variable b⟩ : Equation) ∈ s.equations → Alias t a b

theorem OrdinaryRetraction.bound_back
    {s t : State} {p : Nat → Nat} (r : OrdinaryRetraction s t p)
    {a b : Nat} (h : Bound t.normal a b) : Bound s.normal (p a) (p b) := by
  induction h with
  | interval h => exact r.backInterval h
  | constraint h => exact r.backAtom h
  | refl a => exact .refl _
  | trans _ _ ab bc => exact .trans ab bc

theorem OrdinaryRetraction.bound_forward
    {s t : State} {p : Nat → Nat} (r : OrdinaryRetraction s t p)
    {a b : Nat} (h : Bound s.normal a b) : Bound t.normal a b := by
  induction h with
  | interval h => exact r.forwardInterval h
  | constraint h => exact r.forwardAtom h
  | refl a => exact .refl _
  | trans _ _ ab bc => exact .trans ab bc

theorem OrdinaryRetraction.alias_back
    {s t : State} {p : Nat → Nat} (r : OrdinaryRetraction s t p)
    {a b : Nat} (h : Alias t a b) : Alias s (p a) (p b) := by
  induction h with
  | bounds ab ba => exact .bounds (r.bound_back ab) (r.bound_back ba)
  | forward h => exact r.backVariable h
  | backward h => exact GeneralDeclarativeLowerKnown321.alias_symm (r.backVariable h)
  | trans _ _ ab bc => exact .trans ab bc

theorem OrdinaryRetraction.alias_forward
    {s t : State} {p : Nat → Nat} (r : OrdinaryRetraction s t p)
    {a b : Nat} (h : Alias s a b) : Alias t a b := by
  induction h with
  | bounds ab ba => exact .bounds (r.bound_forward ab) (r.bound_forward ba)
  | forward h => exact r.forwardVariable h
  | backward h => exact GeneralDeclarativeLowerKnown321.alias_symm (r.forwardVariable h)
  | trans _ _ ab bc => exact .trans ab bc

theorem OrdinaryRetraction.raw_cycle_same_rows_on_unchanged_footprint
    {s t : State} {p : Nat → Nat} (r : OrdinaryRetraction s t p)
    {live : Nat → Prop} {root : Nat} (sameRows : s.equations = t.equations)
    (foot : ObservedFootprint (GeneralDeclarativeGraphRows321.observed s) live)
    (fixes : ∀ a, live a → p a = a) (hr : live root) :
    AliasCycle s (GeneralDeclarativeGraphRows321.observed s) root ↔
    AliasCycle t (GeneralDeclarativeGraphRows321.observed t) root := by
  apply raw_cycles_with_same_existing_rows_and_restricted_alias sameRows foot _ hr
  intro a b ha hb
  refine ⟨r.alias_forward,fun h => ?_⟩
  simpa [fixes a ha,fixes b hb] using r.alias_back h



/-- Exact appended ordinary bound rows may be harmless at original points
even when the enlarged space gains genuine aliases/knowledge at fresh points.
All explicit variable rows and intervals keep their original endpoints. -/
theorem ordinary_retraction_of_collapsing_appended_atoms
    {s t : State} {project : Nat → Nat} {added : List (PresenceNormalForm.Atom Nat)}
    (sameRows : s.equations = t.equations)
    (sameIntervals : s.normal.intervals = t.normal.intervals)
    (exactAtoms : t.normal.ordinary = s.normal.ordinary ++ added)
    (keepOldInterval : ∀ {a b}, (a,b) ∈ s.normal.intervals →
      project a = a ∧ project b = b)
    (keepOldAtom : ∀ {a b}, PresenceNormalForm.Atom.tyLe (.var a) (.var b) ∈ s.normal.ordinary →
      project a = a ∧ project b = b)
    (keepOldVariable : ∀ {a b}, (⟨a,.variable b⟩ : Equation) ∈ s.equations →
      project a = a ∧ project b = b)
    (collapseNew : ∀ {a b}, PresenceNormalForm.Atom.tyLe (.var a) (.var b) ∈ added →
      project a = project b) :
    OrdinaryRetraction s t project := by
  constructor
  · intro a b mem
    rw [← sameIntervals] at mem
    obtain ⟨ha,hb⟩ := keepOldInterval mem
    simpa [ha,hb] using (Bound.interval mem)
  · intro a b mem
    rw [exactAtoms, List.mem_append] at mem
    rcases mem with old|new
    · obtain ⟨ha,hb⟩ := keepOldAtom old
      simpa [ha,hb] using (Bound.constraint old)
    · rw [collapseNew new]
      exact .refl _
  · intro a b mem
    rw [← sameRows] at mem
    obtain ⟨ha,hb⟩ := keepOldVariable mem
    simpa [ha,hb] using (Alias.forward mem)
  · intro a b mem
    exact .interval (sameIntervals ▸ mem)
  · intro a b mem
    apply Bound.constraint
    rw [exactAtoms,List.mem_append]
    exact Or.inl mem
  · intro a b mem
    exact .forward (sameRows ▸ mem)



open GeneralDeclarativeGraphRows321 (shapeOf observed)

def rowObservedFootprint (row : Equation) : List Nat :=
  match shapeOf row.right with
  | none => []
  | some shape => row.left :: shape.children

def observedFootprint (s : State) : List Nat :=
  s.equations.flatMap rowObservedFootprint

theorem observed_footprint_covers_every_actual_ordinary_shape (s : State) :
    ObservedFootprint (observed s) (· ∈ observedFootprint s) := by
  constructor
  · intro a shape seen
    obtain ⟨e,mem,shapeEq⟩ := seen
    apply List.mem_flatMap.mpr
    exact ⟨⟨a,e⟩,mem,by simp [rowObservedFootprint,shapeEq]⟩
  · intro a b shape seen child
    obtain ⟨e,mem,shapeEq⟩ := seen
    apply List.mem_flatMap.mpr
    exact ⟨⟨a,e⟩,mem,by simp [rowObservedFootprint,shapeEq,child]⟩

theorem observed_footprint_is_least (s : State) (live : Nat → Prop)
    (cover : ObservedFootprint (observed s) live) :
    ∀ n ∈ observedFootprint s, live n := by
  intro n member
  obtain ⟨row,mem,here⟩ := List.mem_flatMap.mp member
  cases row with | mk a e =>
  cases shapeEq : shapeOf e with
  | none =>
    simp [rowObservedFootprint,shapeEq] at here
  | some shape =>
    have seen : observed s a shape := ⟨e,mem,shapeEq⟩
    simp only [rowObservedFootprint,shapeEq,List.mem_cons] at here
    cases here with
    | inl h => exact h ▸ cover.owner seen
    | inr child => exact cover.child seen child

def fixesNamedScope (s : State) (p : Nat → Nat) (r : Nat) : Bool :=
  (r :: observedFootprint s).all (fun n => decide (p n = n))

theorem actual_original_cycle_same_if_finite_pinned_names_fixed
    {s t : State} {p : Nat → Nat} (r : OrdinaryRetraction s t p)
    (sameRows : s.equations = t.equations) {root : Nat}
    (fixes : fixesNamedScope s p root = true) :
    AliasCycle s (observed s) root ↔ AliasCycle t (observed t) root := by
  have pin : ∀ n ∈ root :: observedFootprint s, p n = n := by
    intro n mem
    have good := List.all_eq_true.mp fixes n mem
    exact of_decide_eq_true good
  have scope : ObservedFootprint (observed s) (· ∈ root :: observedFootprint s) :=
    ⟨fun seen => List.mem_cons_of_mem _ ((observed_footprint_covers_every_actual_ordinary_shape s).owner seen),
     fun seen child => List.mem_cons_of_mem _ ((observed_footprint_covers_every_actual_ordinary_shape s).child seen child)⟩
  exact r.raw_cycle_same_rows_on_unchanged_footprint sameRows scope pin List.mem_cons_self


end Yulang.GeneralDeclarativeI65.I72.PreparationFootprint467
