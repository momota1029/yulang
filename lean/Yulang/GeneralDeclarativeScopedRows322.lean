import Yulang.GeneralDeclarationPatterns

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeScopedRows322
open GeneralDeclarationPatterns (Pattern WellScoped variantRow rowPattern hide mergePayload)
open Yulang.Variants.Merged (normalize)
open Yulang.Variants.Merged.Raw (insert)

theorem hide_scoped (label : Nat) (p : Pattern) (has : WellScoped c p) :
    WellScoped c (hide label p) := by
  cases p with
  | record current payload tail =>
    by_cases same : label = current
    · simpa [hide,same] using hide_scoped label tail has.2
    · simp only [hide,same,ite_false]
      exact ⟨has.1,hide_scoped label tail has.2⟩
  | var | app | variant | join => exact has
termination_by sizeOf p

theorem variant_entries (p : Pattern) (valid : WellScoped c p)
    (view : variantRow p = some rows) :
    rows ≠ [] ∧ ∀ item ∈ rows, WellScoped c item.2 := by
  cases p with
  | var | app | record => cases view
  | variant tag payload =>
    have eq : [(tag,payload)] = rows := Option.some.inj view
    subst rows
    refine ⟨by simp,?_⟩
    intro item taken
    cases List.mem_singleton.mp taken
    exact valid
  | join a b =>
    cases left : variantRow a with
    | none => simp [variantRow,left] at view
    | some xs =>
      cases right : variantRow b with
      | none => simp [variantRow,left,right] at view
      | some ys =>
        have eq : xs ++ ys = rows := by simpa [variantRow,left,right] using view
        subst rows
        have one := variant_entries a valid.1 left
        have two := variant_entries b valid.2 right
        refine ⟨?_,fun item found => (List.mem_append.mp found).elim (one.2 item) (two.2 item)⟩
        intro empty
        exact one.1 (List.append_eq_nil_iff.mp empty).1
termination_by sizeOf p

theorem row_pattern_scoped {rows : List (Nat × Pattern)} (nonempty : rows ≠ [])
    (ready : ∀ item ∈ rows, WellScoped c item.2) : WellScoped c (rowPattern rows) := by
  induction rows with
  | nil => exact False.elim (nonempty rfl)
  | cons first more ih =>
    cases more with
    | nil => exact ready first List.mem_cons_self
    | cons next rest =>
      exact ⟨ready first List.mem_cons_self,
        ih (by simp) (fun item member => ready item (List.mem_cons_of_mem _ member))⟩

theorem payload_scoped {a b : Pattern} (x : WellScoped c a) (y : WellScoped c b) :
    WellScoped c (mergePayload a b) := by
  by_cases same : a = b
  · simpa [mergePayload,same] using x
  · simpa [mergePayload,same] using (show WellScoped c (.join a b) from ⟨x,y⟩)

theorem insert_scoped (tag : Nat) (payload : Pattern) (rows : List (Nat × Pattern))
    (has : WellScoped c payload) (old : ∀ item ∈ rows, WellScoped c item.2) :
    ∀ item ∈ Yulang.Variants.Merged.Raw.insert mergePayload tag payload rows, WellScoped c item.2 := by
  induction rows with
  | nil =>
    intro item member
    cases List.mem_singleton.mp member
    exact has
  | cons first tail ih =>
    obtain ⟨key,value⟩ := first
    intro item found
    by_cases same : tag = key
    · simp only [Yulang.Variants.Merged.Raw.insert,same,ite_true] at found
      rcases List.mem_cons.mp found with rfl|later
      · exact payload_scoped has (old _ List.mem_cons_self)
      · exact old item (List.mem_cons_of_mem _ later)
    · simp only [Yulang.Variants.Merged.Raw.insert,same,ite_false] at found
      rcases List.mem_cons.mp found with rfl|later
      · exact old _ List.mem_cons_self
      · exact ih (fun e put => old e (List.mem_cons_of_mem _ put)) item later

theorem entries_scoped (rows : List (Nat × Pattern))
    (old : ∀ item ∈ rows, WellScoped c item.2) :
    ∀ item ∈ (normalize mergePayload rows).entries, WellScoped c item.2 := by
  induction rows with
  | nil => intro _ impossible; cases impossible
  | cons first more ih =>
    obtain ⟨key,val⟩ := first
    exact insert_scoped key val _ (old _ List.mem_cons_self)
      (ih (fun item found => old item (List.mem_cons_of_mem _ found)))

theorem nonempty_after {rows : List (Nat × Pattern)} (has : rows ≠ []) :
    (normalize mergePayload rows).entries ≠ [] := by
  cases rows with
  | nil => exact False.elim (has rfl)
  | cons first rest =>
    obtain ⟨tag,payload⟩ := first
    have found : tag ∈ ((normalize mergePayload ((tag,payload)::rest)).entries.map Prod.fst) :=
      (Yulang.Variants.Merged.tags_normalize mergePayload tag _).mpr (List.mem_cons_self)
    intro empty
    simp [empty] at found

end Yulang.GeneralDeclarativeScopedRows322
