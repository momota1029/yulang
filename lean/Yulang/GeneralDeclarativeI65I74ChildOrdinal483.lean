import Yulang.GeneralDeclarativeI65I74EquivalentObservations473
import Yulang.GeneralDeclarativeI65I74ProducerTrail479

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.ChildOrdinal483
open ObservationSyntax471 (Slot Label ReadsDescription codeLabel sortedFields RecordEntries readDescription description_exact)
open ObservationAlternatives473 (Positions oldPosition graphOf readNodeAt readTermAt findPosition anchorFor
  found_position_is_literal)
open CommonRoleRegularGraph (Node successors)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open Producer479 (Site Hop)
open LiteralVisits473 (StepWire childSlot)

def labelSlots : Label → List Slot
  | .scalar _ => []
  | .nominal _ => [.argument 0]
  | .structural (.record labels) => labels.map Slot.field
  | .structural .pair => [.argument 0,.argument 1]
  | .structural (.variant _) => [.variant]
  | .structural _ => []

theorem actual_constructor_description_has_exact_ordered_slots
    {s : GeneralDeclarativeI65.State} {e : Expr} {label : Label} {children : List (Slot × Expr)}
    (read : ReadsDescription s e label children) :
    children.map Prod.fst = labelSlots label := by
  cases read <;> simp [RecordEntries,labelSlots,List.map_map,Function.comp_def]

theorem actual_constructor_slots_are_distinct
    {s : GeneralDeclarativeI65.State} {e : Expr} {label : Label} {children : List (Slot × Expr)}
    (read : ReadsDescription s e label children) :
    (children.map Prod.fst).Nodup := by
  rw [actual_constructor_description_has_exact_ordered_slots read]
  cases read <;> simp [labelSlots]
  rw [List.nodup_iff_pairwise_ne,List.pairwise_map]
  refine List.Pairwise.imp (R := fun (a b : Nat × Expr) => a.1 < b.1)
    (fun h same => (Nat.ne_of_lt h) (Slot.field.inj same)) ?_
  exact List.pairwise_map.mp (ObservationSyntax471.sorted_labels_are_canonical _)

private theorem output_at_nth_mapM {A B : Type} (f : A → Option B) {xs : List A} {ys : List B}
    (all : xs.mapM f = some ys) (k : Nat) {item : A} (found : xs[k]? = some item) :
    ∃ got, ys[k]? = some got ∧ f item = some got := by
  induction xs generalizing ys k with
  | nil => cases found
  | cons a rest ih =>
    cases x : f a with
    | none => simp [List.mapM_cons,x,bind,Option.bind] at all
    | some first =>
      cases xs : rest.mapM f with
      | none => simp [List.mapM_cons,x,xs,bind,Option.bind] at all
      | some tail =>
        have shape : first::tail = ys := by simpa [List.mapM_cons,x,xs,bind,Option.bind,pure] using all
        subst ys
        cases k with
        | zero =>
          have eq := Option.some.inj found
          exact ⟨first,rfl,eq ▸ x⟩
        | succ k => exact ih xs k found

private theorem coded_node_has_exact_children {n : Nat}
    {s : GeneralDeclarativeI65.State} {e : Expr} {branches : List (Slot × Expr)}
    (palette : List GeneralNormalizedObservation.Shape) (label : Label) (child : List (Fin n))
    (node : Node n) (meant : codeLabel palette label child = some node) (root : Fin n)
    (desc : ReadsDescription s e label branches) (kids : branches ≠ []) :
    successors (fun _ => node) root = child := by
  cases label with
  | scalar =>
    cases desc
    exact False.elim (kids rfl)
  | nominal code =>
    simp only [codeLabel,Option.some.injEq] at meant
    subst node
    rfl
  | structural label =>
    simp only [codeLabel] at meant
    split at meant
    · have same := Option.some.inj meant
      subst node
      rfl
    · cases meant

theorem raw_position_reads_exact_literal_child_at_its_original_ordinal
    {n : Nat} {s : GeneralDeclarativeI65.State} {pos : Positions n} (here : Fin n)
    (term : Expr) (label : Label) (children : List (Slot × Expr)) (choice : Nat)
    (selector : Slot) (raw : Expr)
    (atTerm : readTermAt s pos here = some term)
    (described : ReadsDescription s term label children)
    (found : children[choice]? = some (selector,raw))
    (known : graphOf s pos here ≠ .unresolved) :
    ∃ reached : Fin n,
      (successors (graphOf s pos) here)[choice]? = some reached ∧
      oldPosition pos reached = anchorFor (pos.cells.get here) selector raw := by
  cases resolved : readNodeAt s pos here with
  | none => exact False.elim (known (by simp [graphOf,resolved]))
  | some n =>
    have legalCode := description_exact.mpr described
    let f := fun x : Slot × Expr => findPosition pos (anchorFor (pos.cells.get here) x.1 x.2)
    cases chose : children.mapM f with
    | none => simp [readNodeAt,atTerm,legalCode,f,chose,bind,Option.bind] at resolved
    | some kids =>
      have reduced : (do let vs ← children.mapM f; codeLabel pos.signs label vs) = some n := by
        simpa [readNodeAt,atTerm,legalCode,bind,Option.bind,f] using resolved
      rw [chose] at reduced
      have yes : codeLabel pos.signs label kids = some n := reduced
      have rest : successors (graphOf s pos) here = kids := by
        have only : successors (fun _ => n) here = kids :=
          coded_node_has_exact_children pos.signs label kids n yes here described
            (fun nil => by simp [nil] at found)
        have same : graphOf s pos here = n := by simp [graphOf,resolved]
        simpa [successors,same] using only
      obtain ⟨child,atOrdinal,picked⟩ := output_at_nth_mapM f chose choice found
      exact ⟨child,rest.symm ▸ atOrdinal,found_position_is_literal picked⟩


theorem unique_observation_coordinates_are_injective
    {n : Nat} {pos : Positions n} (distinct : (List.ofFn (oldPosition pos)).Nodup) :
    Function.Injective (oldPosition pos) := by
  intro a b eq
  apply Fin.ext
  have eqAt : (List.ofFn (oldPosition pos))[a.val]'(by simp) =
      (List.ofFn (oldPosition pos))[b.val]'(by simp) := by simpa using eq
  exact (List.Nodup.getElem_inj distinct).mp eqAt

theorem actual_hop_uses_the_unique_requested_slot_at_a_real_graph_ordinal
    {n : Nat} {s : GeneralDeclarativeI65.State} {pos : Positions n}
    {here next : Site s pos} {move : StepWire}
    (known : graphOf s pos here.index ≠ .unresolved)
    (distinct : (List.ofFn (oldPosition pos)).Nodup) (h : Hop here next move) :
    ∃ i : Nat,
      (labelSlots h.typed.rawLabel)[i]? = some (childSlot move.action) ∧
      (successors (graphOf s pos) here.index)[i]? = some next.index := by
  obtain ⟨k,index⟩ := List.mem_iff_getElem?.mp h.typed.exactRawChild
  obtain ⟨actual,read,location⟩ :=
    raw_position_reads_exact_literal_child_at_its_original_ordinal here.index here.term h.typed.rawLabel
      h.typed.rawChildren k (childSlot move.action) h.typed.actualRawChild here.exactTerm h.typed.exactRaw index known
  have candidate := unique_observation_coordinates_are_injective distinct (location.trans h.position)
  refine ⟨k,?_,candidate ▸ read⟩
  rw [←actual_constructor_description_has_exact_ordered_slots h.typed.exactRaw]
  simp [List.getElem?_map,index]


open CommonRoleGraphBisimulation (View observe)

private def shapeKey : View → Option (Bool × Nat)
  | .structural key _ => some (false,key)
  | .nominal key _ => some (true,key)
  | _ => none

private def labelKey (palette : List GeneralNormalizedObservation.Shape) : Label → Option (Bool × Nat)
  | .nominal k => some (true,k)
  | .structural k => some (false,palette.idxOf k)
  | .scalar _ => none

private theorem raw_head_decodes_site_shape
    {n : Nat} {s : GeneralDeclarativeI65.State} {pos : Positions n} {site : Fin n}
    {e : Expr} {label : Label} {branches : List (Slot × Expr)}
    (known : graphOf s pos site ≠ .unresolved)
    (term : readTermAt s pos site = some e)
    (descriptor : ReadsDescription s e label branches) :
    shapeKey (observe (graphOf s pos) 1 site) = labelKey pos.signs label ∧
    ∀ k, label = .structural k → k ∈ pos.signs := by
  cases read : readNodeAt s pos site with
  | none => exact False.elim (known (by simp [graphOf,read]))
  | some node =>
    have desc := description_exact.mpr descriptor
    let f := fun (x : Slot × Expr) => findPosition pos (anchorFor (pos.cells.get site) x.1 x.2)
    have run : (do let got ← branches.mapM f; codeLabel pos.signs label got) = some node := by
      simpa [readNodeAt,term,desc,f,bind,Option.bind] using read
    cases got : branches.mapM f with
    | none => simp [got,bind,Option.bind] at run
    | some kids =>
      rw [got] at run
      have coded : codeLabel pos.signs label kids = some node := run
      have current : graphOf s pos site = node := by simp [graphOf,read]
      cases label with
      | scalar b =>
        have equal := Option.some.inj coded
        rw [←equal] at current
        exact ⟨by simp [observe,current,shapeKey,labelKey],by intro _ impossible; cases impossible⟩
      | nominal k =>
        have equal := Option.some.inj coded
        rw [←equal] at current
        exact ⟨by simp [observe,current,shapeKey,labelKey],by intro _ impossible; cases impossible⟩
      | structural k =>
        simp only [codeLabel] at coded
        split at coded
        · rename_i present
          have equal := Option.some.inj coded
          rw [←equal] at current
          exact ⟨by simp [observe,current,shapeKey,labelKey],by intro j h; cases h; exact present⟩
        · cases coded

private theorem equal_shape_keys_give_the_same_slot_layout
    (palette : List GeneralNormalizedObservation.Shape) (left right : Label)
    (leftPresent : ∀ k, left = .structural k → k ∈ palette)
    (rightPresent : ∀ k, right = .structural k → k ∈ palette)
    (keys : labelKey palette left = labelKey palette right) :
    labelSlots left = labelSlots right := by
  cases left <;> cases right <;> simp [labelKey] at keys <;> try rfl
  case structural.structural a b =>
    have aka := ObservationSyntax471.node_encoding_never_collides_on_distinct_structural_signatures
      (leftPresent a rfl) (rightPresent b rfl) keys
    rw [aka]

theorem paired_actual_constructors_pull_the_exact_selected_slot_to_the_same_ordinal
    {n : Nat} {s : GeneralDeclarativeI65.State} {pos : Positions n}
    {left right a b : Site s pos} {action other : StepWire}
    (loc : (List.ofFn (oldPosition pos)).Nodup)
    (leftKnown : graphOf s pos left.index ≠ .unresolved)
    (rightKnown : graphOf s pos right.index ≠ .unresolved)
    (same : CommonRoleGraphBisimulation.ObservationallyEqual (graphOf s pos) left.index right.index)
    (one : Hop left a action) (two : Hop right b other)
    (selected : childSlot action.action = childSlot other.action) :
    ∃ ix : Nat,
      (successors (graphOf s pos) left.index)[ix]? = some a.index ∧
      (successors (graphOf s pos) right.index)[ix]? = some b.index := by
  have l := raw_head_decodes_site_shape leftKnown left.exactTerm one.typed.exactRaw
  have r := raw_head_decodes_site_shape rightKnown right.exactTerm two.typed.exactRaw
  have marks := congrArg shapeKey (same 1)
  have sameLayout := equal_shape_keys_give_the_same_slot_layout pos.signs one.typed.rawLabel
    two.typed.rawLabel l.2 r.2 (l.1.symm.trans (marks.trans r.1))
  obtain ⟨ix,declared,found⟩ := actual_hop_uses_the_unique_requested_slot_at_a_real_graph_ordinal
    leftKnown loc one
  obtain ⟨otherIx,another,foundOther⟩ := actual_hop_uses_the_unique_requested_slot_at_a_real_graph_ordinal
    rightKnown loc two
  have uniqueLayout : (labelSlots one.typed.rawLabel).Nodup :=
    actual_constructor_description_has_exact_ordered_slots one.typed.exactRaw ▸
      actual_constructor_slots_are_distinct one.typed.exactRaw
  rw [←sameLayout,←selected] at another
  have sameIx := (List.Nodup.getElem?_inj (List.getElem?_eq_some_iff.mp declared).1 uniqueLayout).mp
    (declared.trans another.symm)
  subst otherIx
  exact ⟨ix,found,foundOther⟩

end Yulang.GeneralDeclarativeI65.I72.ChildOrdinal483
