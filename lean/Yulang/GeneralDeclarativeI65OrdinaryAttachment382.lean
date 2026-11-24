import Yulang.GeneralDeclarativeWitnessOrigins350

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeWitnessOrigins350 (Table Attached attach support visible_iff)
open GeneralDeclarativeOrigins321 (restriction)

/-- The ordinary attachment only checks that the source table's two row
lists are present in the current equations. It checks no completion. -/
theorem ordinary_attach_present_iff382 {s : GeneralDeclarativeHead320.State} {t : Table} :
    (attach s t).isSome = true ↔ Nonempty (Attached s t) := by
  constructor
  · intro h
    cases result : attach s t with
    | none => simp [result] at h
    | some attached => exact ⟨attached⟩
  · rintro ⟨attached⟩
    have authored : t.authored.all (fun e => decide (e ∈ s.equations)) = true := by
      apply List.all_eq_true.mpr
      intro e occurs
      exact decide_eq_true (attached.authored occurs)
    have produced : t.produced.all (fun p => decide (p.1 ∈ s.equations)) = true := by
      apply List.all_eq_true.mpr
      intro p occurs
      exact decide_eq_true (attached.produced p occurs)
    simp [attach,authored,produced]

/-- Change neither source row list. An attachment can be transported to
the new independent completion table without proving any completions. -/
def reattach_same_ordinary_rows382 {s : GeneralDeclarativeHead320.State} {a b : Table}
    (attached : Attached s a) (written : a.authored = b.authored)
    (produced : a.produced = b.produced) : Attached s b :=
  ⟨written ▸ attached.authored, produced ▸ attached.produced⟩

theorem ordinary_support_requires_actual_origin382
    {s : GeneralDeclarativeHead320.State} {t : Table} (a : Attached s t) (row : Equation) :
    row ∈ (restriction (support a)).equations ↔
      row ∈ t.authored ∨ ∃ owner, (row,owner) ∈ t.produced ∧ owner ∈ t.released := by
  rw [visible_iff]
  unfold GeneralDeclarativeWitnessOrigins350.visible
  constructor
  · intro here
    rcases List.mem_append.mp here with direct|release
    · exact .inl direct
    · obtain ⟨⟨e,owner⟩,existsHere,equal⟩ := List.mem_map.mp release
      have fact := List.mem_filter.mp existsHere
      change e = row at equal
      subst e
      exact .inr ⟨owner,fact.1,by simpa using fact.2⟩
  · intro evidence
    rcases evidence with direct|⟨owner,whereFrom,done⟩
    · exact List.mem_append_left _ direct
    · exact List.mem_append_right _ (List.mem_map.mpr
        ⟨(row,owner),List.mem_filter.mpr ⟨whereFrom,by simpa using done⟩,rfl⟩)

/-- Refines the ordinary no-erasure cut at the actual attachment
operation. Both manifests are supplied; nothing produces a released
owner, changes a graph equation, or returns a language verdict. -/
theorem exact_ordinary_attachment_cannot_authenticate_release382
    {s : GeneralDeclarativeHead320.State} {allowed denied : Table} {row : Equation} {owner : Nat}
    (a : Attached s allowed) (authored : allowed.authored = denied.authored)
    (produced : allowed.produced = denied.produced)
    (output : (row,owner) ∈ allowed.produced) (yes : owner ∈ allowed.released)
    (notAuthored : row ∉ allowed.authored)
    (no : ∀ k, (row,k) ∈ denied.produced → k ∉ denied.released) :
    (attach s allowed).isSome = true ∧ (attach s denied).isSome = true ∧
      row ∈ (restriction (support a)).equations ∧
      row ∉ (restriction (support (reattach_same_ordinary_rows382 a authored produced))).equations := by
  let deniedAttached := reattach_same_ordinary_rows382 a authored produced
  refine ⟨ordinary_attach_present_iff382.mpr ⟨a⟩,
    ordinary_attach_present_iff382.mpr ⟨deniedAttached⟩,
    (ordinary_support_requires_actual_origin382 a row).mpr (.inr ⟨owner,output,yes⟩),?_⟩
  intro wrong
  rcases (ordinary_support_requires_actual_origin382 deniedAttached row).mp wrong with direct|⟨k,e,isDone⟩
  · exact notAuthored (authored.symm ▸ direct)
  · exact no k e isDone

end Yulang.GeneralDeclarativeI65
