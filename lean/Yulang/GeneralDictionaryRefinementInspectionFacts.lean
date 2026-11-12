import Yulang.GeneralDictionaryRefreshDescriptors

/-! Small source facts for finished inspection under fixed-view refinement.
A visible scalar or structural head cannot acquire a nominal descriptor, since
nominal bodies are hidden in the normalized view. -/
namespace Yulang.GeneralDictionaryRefinementInspectionFacts
open GeneralDictionaryInspectionTransport
open GeneralNominalRecursiveCandidates (Context)
open GeneralNominalRecursiveInspection

theorem none_of_visible (context : Context) (next : Observation context.state)
    (view : next.view = context.state.view) (slot : Fin context.state.base.slots)
    (visible : context.state.view.heads slot ≠ .deferred .unresolved) : next.nominals slot = none := by
  cases found : next.nominals slot with
  | none => rfl
  | some descriptor =>
    have hidden := next.bodiesOpaque slot descriptor found
    rw [view] at hidden
    exact False.elim (visible hidden)

theorem finished_append (first last : Report state) :
    Finished (first.append last) ↔ Finished first ∧ Finished last := by
  simp only [Finished,Report.append,List.append_eq_nil_iff]
  constructor
  · intro h
    exact ⟨⟨h.1.1,h.2.1.1,h.2.2.1⟩,h.1.2,h.2.1.2,h.2.2.2⟩
  · rintro ⟨one,two⟩
    exact ⟨⟨one.1,two.1⟩,⟨one.2.1,two.2.1⟩,one.2.2,two.2.2⟩

theorem finished_visit (bounds : GeneralNominalInspection.Bounds state) (origin : Option Origin)
    (test : Test) (value : Report state) :
    Finished (Report.visit bounds origin test value) ↔ Finished value := Iff.rfl

theorem block_not_finished (bounds : GeneralNominalInspection.Bounds state) : ¬ Finished (block bounds) := by
  simp [Finished,block]

end Yulang.GeneralDictionaryRefinementInspectionFacts
