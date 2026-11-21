import Yulang.GeneralDeclarativeRecordK2326

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeGraphFootprint326
open GeneralDeclarativeTraceNames321 (names namesMany)
open GeneralDeclarativeGraphRows321 (fields shapeOf)
open GeneralDeclarativeK2Graph321 (arguments Shape)
open GeneralNominalCenteredHeadMatExpressions (Expr)

theorem arguments_used (written : arguments es = some childNames) :
    childNames ⊆ namesMany es := by
  induction es generalizing childNames with
  | nil =>
    cases Option.some.inj written
    exact fun _ h => h
  | cons p ps ih =>
    cases p with
    | «variable» n =>
      cases suffix : arguments ps with
      | none => simp [arguments,suffix] at written
      | some rest =>
        have same : n :: rest = childNames := by simpa [arguments,suffix] using written
        subst childNames
        intro child member
        rcases List.mem_cons.mp member with rfl|next
        · exact List.mem_append_left _ List.mem_cons_self
        · exact List.mem_append_right _ (ih suffix next)
    | primitive | nominal | record | variant | join => cases written

theorem fields_used (printed : fields e = some fs) (member : label ∈ fs) : label.2 ∈ names e := by
  cases e with
  | «variable» | nominal | variant | join => cases printed
  | primitive tag args =>
    cases tag with
    | scalar _ | pair | exactEmpty => cases printed
    | emptyRecord =>
      cases args with
      | nil =>
        cases Option.some.inj printed
        cases member
      | cons _ _ => cases printed
  | record key payload rest =>
    cases payload with
    | «variable» n =>
      cases tail : fields rest with
      | none => simp [fields,tail] at printed
      | some rows =>
        have same : (key,n) :: rows.filter (fun f => decide (f.1 ≠ key)) = fs := by
          simpa only [fields,tail,Option.map_some,Option.some.injEq] using printed
        subst fs
        rcases List.mem_cons.mp member with rfl|later
        · exact List.mem_append_left _ List.mem_cons_self
        · exact List.mem_append_right _ (fields_used tail ((List.mem_filter.mp later).1))
    | primitive | nominal | record | variant | join => cases printed

termination_by sizeOf e

/-- Every visible graph child is already a logical name in the
underlying ordinary equation. Shadow elimination may remove names,
but the normalized view never manufactures a new child name. -/
theorem shape_children (printed : shapeOf e = some shape) : shape.children ⊆ names e := by
  cases e with
  | «variable» | join => cases printed
  | primitive ctor args | nominal ctor args =>
    cases fn : arguments args with
    | none => simp [shapeOf,fn] at printed
    | some values =>
      simp [shapeOf,fn] at printed
      subst shape
      exact arguments_used fn
  | record label a b =>
    cases fn : fields (.record label a b) with
    | none => simp [shapeOf,fn] at printed
    | some f =>
      have h : Shape.record f = shape := by
        simpa only [shapeOf,fn,Option.map_some,Option.some.injEq] using printed
      subst shape
      intro name member
      obtain ⟨label,part,rfl⟩ := List.mem_map.mp member
      exact fields_used fn part
  | variant label payload =>
    cases payload with
    | «variable» child =>
      cases Option.some.inj printed
      intro name member
      exact member
    | primitive | nominal | record | variant | join => cases printed

end Yulang.GeneralDeclarativeGraphFootprint326
