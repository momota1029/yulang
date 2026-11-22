import Yulang.GeneralStoppedLower335
import Yulang.GeneralNominalRefinements

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralStoppedLowerOrigin335
open GeneralNominalState (State Descriptor Parameter)
open GeneralDeclarativeHead320 (Equation)
open GeneralStoppedLower335 (record collect lower slotRows headAt descriptorAt)
open GeneralStoppedShape335 (one point headExpr descriptorExpr)
open GeneralNominalRefinements (Refines renameDescriptor renameParameter)
open Core.PresenceGeneration (TyTerm)
open GeneralNominalCenteredHeadMatExpressions (Expr)

theorem collect_rows
    (made : collect f xs = some es) :
    row ∈ es ↔ ∃ key ∈ xs, ∃ rows, f key = some rows ∧ row ∈ rows := by
  induction xs generalizing es with
  | nil =>
    have same : es = [] := (Option.some.inj made).symm
    subst es
    simp
  | cons k rest ih =>
    cases first : f k with
    | none => simp [collect,first] at made
    | some current =>
      cases last : collect f rest with
      | none => simp [collect,first,last] at made
      | some other =>
        have sy : current ++ other = es := by simpa [collect,first,last] using made
        subst es
        constructor
        · intro h
          rcases List.mem_append.mp h with left|right
          · exact ⟨k,List.mem_cons_self,_,first,left⟩
          · obtain ⟨x,there,t,ran,seen⟩ := (ih last).mp right
            exact ⟨x,List.mem_cons_of_mem _ there,t,ran,seen⟩
        · rintro ⟨key,which,rows,ran,inRows⟩
          rcases List.mem_cons.mp which with rfl|later
          · have sy := Option.some.inj (first.symm.trans ran)
            cases sy
            exact List.mem_append_left _ inRows
          · exact List.mem_append_right _ ((ih last).mpr ⟨key,later,rows,ran,inRows⟩)

theorem exists_entry {xs : List α} (made : collect f xs = some es) (which : key ∈ xs) :
    ∃ rows, f key = some rows := by
  induction xs generalizing es with
  | nil => cases which
  | cons k rest ih =>
    cases first : f k with
    | none => simp [collect,first] at made
    | some current =>
      cases last : collect f rest with
      | none => simp [collect,first,last] at made
      | some other =>
        rcases List.mem_cons.mp which with rfl|later
        · exact ⟨_,first⟩
        · exact ih last later

theorem record_rows {rec : Option α} (made : record name encode rec = some es) :
    row ∈ es ↔ ∃ value expr, rec = some value ∧ encode value = some expr ∧ row = ⟨name,expr⟩ := by
  cases rec with
  | none =>
    have eq := (Option.some.inj made).symm
    subst es
    simp
  | some value =>
    unfold record at made
    obtain ⟨expr,encoded,rfl⟩ := Option.map_eq_some_iff.mp made
    constructor
    · intro hit
      exact ⟨value,expr,rfl,encoded,List.mem_singleton.mp hit⟩
    · rintro ⟨other,shape,same,printed,matched⟩
      cases Option.some.inj same
      cases Option.some.inj (printed.symm.trans encoded)
      exact List.mem_singleton.mpr matched

/-- Literal source shape, distinct from logical entailment. The tag
and all type names come from stored source head/descriptor records. -/
def ScalarRow (raw : State) (row : Equation) : Prop :=
  ∃ k term e, (raw.base.heads k).equation = some term ∧ headExpr term = some e ∧
    row = ⟨raw.base.source k,e⟩

def NominalRow (raw : State) (row : Equation) : Prop :=
  ∃ k d e, raw.nominals k = some d ∧ descriptorExpr raw.base d = some e ∧
    row = ⟨raw.base.source k,e⟩

theorem exact_rows {raw : State} (ok : lower raw = some q) (row : Equation) :
    row ∈ q.equations ↔ ScalarRow raw row ∨ NominalRow raw row := by
  unfold lower at ok
  obtain ⟨es,computed,rfl⟩ := Option.map_eq_some_iff.mp ok
  have both {k} {rows} (made : slotRows raw k = some rows) :
      ∃ hs ds, headAt raw k = some hs ∧ descriptorAt raw k = some ds ∧ rows = hs ++ ds := by
    cases h : headAt raw k with
    | none => simp [slotRows,h] at made
    | some hs =>
      cases d : descriptorAt raw k with
      | none => simp [slotRows,h,d] at made
      | some ds =>
        have eq : hs ++ ds = rows := by simpa [slotRows,h,d] using made
        exact ⟨hs,ds,rfl,rfl,eq.symm⟩
  constructor
  · intro hit
    obtain ⟨k,_here,rows,made,used⟩ := (collect_rows computed).mp hit
    obtain ⟨hs,ds,h,d,rfl⟩ := both made
    rcases List.mem_append.mp used with first|last
    · obtain ⟨term,e,value,shape,same⟩ := (record_rows h).mp first
      exact .inl ⟨k,term,e,value,shape,same⟩
    · obtain ⟨term,e,value,shape,same⟩ := (record_rows d).mp last
      exact .inr ⟨k,term,e,value,shape,same⟩
  · rintro (⟨k,term,e,value,shape,same⟩|⟨k,term,e,value,shape,same⟩)
    · have here : k ∈ List.ofFn (fun k : Fin raw.base.slots => k) := List.mem_ofFn.mpr ⟨k,rfl⟩
      obtain ⟨rows,runs⟩ := exists_entry computed here
      obtain ⟨hs,ds,head,_,rfl⟩ := both runs
      exact (collect_rows computed).mpr ⟨k,here,_,runs,
        List.mem_append_left _ ((record_rows head).mpr ⟨_,_,value,shape,same⟩)⟩
    · have here : k ∈ List.ofFn (fun k : Fin raw.base.slots => k) := List.mem_ofFn.mpr ⟨k,rfl⟩
      obtain ⟨rows,runs⟩ := exists_entry computed here
      obtain ⟨hs,ds,_,nominal,rfl⟩ := both runs
      exact (collect_rows computed).mpr ⟨k,here,_,runs,
        List.mem_append_right _ ((record_rows nominal).mpr ⟨_,_,value,shape,same⟩)⟩

theorem rename_point (embedding : Fin a → Fin b)
    (old : point ps = some indices) :
    point (ps.map (renameParameter embedding)) = some (indices.map embedding) := by
  induction ps generalizing indices with
  | nil =>
    cases Option.some.inj old
    rfl
  | cons p ps ih =>
    obtain ⟨first,rest,rfl,already,rfl⟩ := GeneralStoppedShape335.point_front p ps indices old
    have next := ih already
    simp [point,List.mapM_cons,one,renameParameter,show List.mapM one (ps.map (renameParameter embedding)) =
      some (rest.map embedding) from next]

theorem descriptor_names {before after : State} (g : Refines before after)
    (d : Descriptor before.base.slots) (encoded : descriptorExpr before.base d = some e) :
    descriptorExpr after.base (renameDescriptor g.base.embed d) = some e := by
  unfold descriptorExpr at encoded ⊢
  obtain ⟨sources,old,rfl⟩ := Option.map_eq_some_iff.mp encoded
  change (point (d.arguments.map (renameParameter g.base.embed))).map
    (fun ks => Expr.nominal d.declaration.name (ks.map fun j => .variable (after.base.source j))) =
    some (Expr.nominal d.declaration.name (sources.map fun j => .variable (before.base.source j)))
  rw [rename_point g.base.embed old]
  simp only [Option.map_some,List.map_map,Function.comp_def,g.base.source]

theorem literal_nominal_preserved {before after : State} (g : Refines before after)
    (source : NominalRow before row) :
    NominalRow after row := by
  obtain ⟨k,d,e,stored,code,same⟩ := source
  exact ⟨g.base.embed k,_,e,g.nominals k d stored,descriptor_names g d code,
    same.trans (congrArg (fun name => (⟨name,e⟩ : Equation)) (g.base.source k).symm)⟩

/-- Actual descriptor refinement transports the precise authored
nominal row, not merely a row with the same denotation. Scalar
heads are *not* inferred from Refines.heads, which is a Rewrites
fact rather than a positive current storage witness. -/
theorem named_origin_transport {before after : State} (g : Refines before after)
    (now : lower after = some t) (old : NominalRow before row) :
    row ∈ t.equations :=
  (exact_rows now _).mpr (.inr (literal_nominal_preserved g old))

end Yulang.GeneralStoppedLowerOrigin335
