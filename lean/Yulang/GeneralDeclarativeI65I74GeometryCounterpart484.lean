import Yulang.GeneralDeclarativeI65I74ChildOrdinal483

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.Counterpart484
open ObservationSyntax471 (Slot Label ReadsDescription codeLabel readDescription description_exact)
open ObservationAlternatives473 (Positions oldPosition graphOf readNodeAt readTermAt findPosition anchorFor
  found_position_is_literal)
open CommonRoleRegularGraph (Node successors)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open Producer479 (Site Hop readHop)
open LiteralVisits473 (StepWire childSlot ReadStep)
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


private theorem known_site_has_a_literal_descriptor
    {n : Nat} {s : GeneralDeclarativeI65.State} {pos : Positions n}
    (site : Site s pos) (known : graphOf s pos site.index ≠ .unresolved) :
    ∃ label branches, ReadsDescription s site.term label branches := by
  cases desc : readDescription s site.term with
  | none =>
    exfalso
    exact known (by simp [graphOf,readNodeAt,site.exactTerm,desc,bind,Option.bind])
  | some picked =>
    exact ⟨picked.1,picked.2,description_exact.mp (by cases picked; exact desc)⟩

private theorem equal_key_of_a_nonscalar_head_gives_the_same_constructor
    (palette : List GeneralNormalizedObservation.Shape) (left right : Label)
    (leftPresent : ∀ k, left = .structural k → k ∈ palette)
    (rightPresent : ∀ k, right = .structural k → k ∈ palette)
    (notScalar : ∀ b, left ≠ .scalar b)
    (keys : labelKey palette left = labelKey palette right) : left = right := by
  cases left <;> cases right <;> simp [labelKey] at keys
  case scalar.scalar => exact False.elim (notScalar _ rfl)
  case structural.structural =>
    exact congrArg Label.structural (ObservationSyntax471.node_encoding_never_collides_on_distinct_structural_signatures
        (leftPresent _ rfl) (rightPresent _ rfl) keys)
  case nominal.nominal => exact congrArg Label.nominal keys

theorem same_selected_literal_step_exists_in_a_resolved_equal_presentation
    {s : GeneralDeclarativeI65.State} {pos : Positions n} {left right a : Site s pos}
    {w : StepWire}
    (leftKnown : graphOf s pos left.index ≠ .unresolved)
    (rightKnown : graphOf s pos right.index ≠ .unresolved)
    (same : CommonRoleGraphBisimulation.ObservationallyEqual (graphOf s pos) left.index right.index)
    (samePattern : left.pattern = right.pattern) (sameCode : left.query = right.query)
    (one : Hop left a w) :
    ∃ read : ReadStep s w right.pattern right.query right.term,
      read.writtenChild = a.pattern ∧ read.childQuery = a.query := by
  obtain ⟨head,kids,described⟩ := known_site_has_a_literal_descriptor right rightKnown
  let l := raw_head_decodes_site_shape leftKnown left.exactTerm one.typed.exactRaw
  let r := raw_head_decodes_site_shape rightKnown right.exactTerm described
  have xor := congrArg shapeKey (same 1)
  have nonScalar : ∀ b, one.typed.rawLabel ≠ .scalar b := by
    intro b h
    have noChildren := ChildOrdinal483.actual_constructor_description_has_exact_ordered_slots one.typed.exactRaw
    rw [h] at noChildren
    simp [ChildOrdinal483.labelSlots] at noChildren
    have member := List.mem_map_of_mem (f := Prod.fst) one.typed.exactRawChild
    simp [noChildren] at member
  have tags := equal_key_of_a_nonscalar_head_gives_the_same_constructor pos.signs
    one.typed.rawLabel head l.2 r.2 nonScalar (l.1.symm.trans (xor.trans r.1))
  obtain ⟨i, index⟩ := List.mem_iff_getElem?.mp one.typed.exactRawChild
  have rawSlot : (kids.map Prod.fst)[i]? = some (childSlot w.action) := by
    rw [ChildOrdinal483.actual_constructor_description_has_exact_ordered_slots described,←tags,
      ←ChildOrdinal483.actual_constructor_description_has_exact_ordered_slots one.typed.exactRaw]
    simp [List.getElem?_map,index]
  cases picked : kids[i]? with
  | none => simp [List.getElem?_map,picked] at rawSlot
  | some child =>
    have own : child.1 = childSlot w.action := by simpa [List.getElem?_map,picked] using rawSlot
    have branch : (childSlot w.action,child.2) ∈ kids := by
      rw [←own]; cases child; exact List.mem_of_getElem? picked
    let typed : ReadStep s w right.pattern right.query right.term :=
      ⟨one.typed.writtenChild,samePattern ▸ one.typed.writtenFrom,
        one.typed.childQuery,one.typed.exactCompile,
        one.typed.queryLabel,one.typed.queryChildren,sameCode ▸ one.typed.exactQuery,
        one.typed.actualQueryChild,head,kids,described,child.2,branch,tags ▸ one.typed.pathAllowed,
        one.typed.childInspected⟩
    exact ⟨typed,one.written,one.query⟩

private theorem resolved_site_has_ordinary_term
    {s : GeneralDeclarativeI65.State} {pos : Positions n} (i : Fin n)
    (known : graphOf s pos i ≠ .unresolved) :
    ∃ term, readTermAt s pos i = some term := by
  cases term : readTermAt s pos i with
  | none => exact False.elim (known (by simp [graphOf,readNodeAt,term,bind,Option.bind]))
  | some e => exact ⟨e,rfl⟩

/-- This is a geometric reifier, not a source author reifier. The supplied
original selector remains fixed, and the actual independent source card is
neither fabricated nor inferred from the class of its child. -/
theorem equal_presentations_reify_one_already_selected_original_geometric_hop
    {s : GeneralDeclarativeI65.State} {pos : Positions n} {left right a : Site s pos} {w : StepWire}
    (leftKnown : graphOf s pos left.index ≠ .unresolved)
    (rightKnown : graphOf s pos right.index ≠ .unresolved)
    (safeRead : ∀ i ∈ successors (graphOf s pos) right.index, graphOf s pos i ≠ .unresolved)
    (same : CommonRoleGraphBisimulation.ObservationallyEqual (graphOf s pos) left.index right.index)
    (samePattern : left.pattern = right.pattern) (sameCode : left.query = right.query)
    (one : Hop left a w) :
    ∃ b : Site s pos, Nonempty (Hop right b w) ∧ b.pattern = a.pattern ∧ b.query = a.query := by
  obtain ⟨typed,written,compiled⟩ :=
    same_selected_literal_step_exists_in_a_resolved_equal_presentation
      leftKnown rightKnown same samePattern sameCode one
  obtain ⟨i,slot⟩ := List.mem_iff_getElem?.mp typed.exactRawChild
  obtain ⟨child,index,address⟩ := ChildOrdinal483.raw_position_reads_exact_literal_child_at_its_original_ordinal
    right.index right.term typed.rawLabel typed.rawChildren i (childSlot w.action) typed.actualRawChild
    right.exactTerm typed.exactRaw slot rightKnown
  have next : child ∈ successors (graphOf s pos) right.index := List.mem_of_getElem? index
  obtain ⟨term,existsTerm⟩ := resolved_site_has_ordinary_term child (safeRead child next)
  exact ⟨⟨child,typed.writtenChild,typed.childQuery,term,existsTerm⟩,
    ⟨⟨typed,rfl,rfl,address.symm,next⟩⟩,written,compiled⟩

end Yulang.GeneralDeclarativeI65.I72.Counterpart484
