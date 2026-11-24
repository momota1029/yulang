import Yulang.GeneralDeclarativeI65I72Obligations402

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72

open CommonRoleOutermostResolver (Tree Summarizes Result All₂ Dictionary)

structure ExactOutputSupport (R : SourcePrimitives) (s : State) (need : OutputNeed s) where
  event : Event s need.producer
  diagnostic : Tree
  source : SourceTrace R s need.producer diagnostic (some event)
  completion : Summarizes diagnostic (.selected need.dictionary)
  sameTypedOutput : (event.outputs need.ordinal).receipt = need.expected

/-- Reads the actual entry in the supplied proof forest. In particular,
the result is not obtained by choosing another proof at the same output
number or target. -/
def SupportForest.atOriginal {R s needs} (forest : SupportForest R s needs)
    (index : Nat) {need : OutputNeed s} (found : needs[index]? = some need) :
    ExactOutputSupport R s need := by
  cases forest with
  | nil => simp at found
  | cons chosen completed literal rest =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at found
      subst need
      exact ⟨_,_,chosen,completed,literal⟩
    | succ i => exact rest.atOriginal i (by simpa using found)

theorem exact_output_support_cannot_use_root_k2 {R s need} (supported : ExactOutputSupport R s need) :
    ¬ RootCycle s need.producer := by
  intro cycle
  have diagnostic := root_k2_forces_original_trace_verdict cycle supported.source
  have summary := supported.completion
  rw [diagnostic] at summary
  cases summary

/-- A family with no independent base cannot justify a finite selected
derivation. An ordinary and native mixture may appear in the family;
where choices and read-producer choices are still separate subtrees.
This is well-founded use of one given derivation, not solver termination. -/
theorem closed_source_family_cannot_complete {R s} (closed : Request → Prop)
    (needsFamily : ∀ q (e : Event s q) needs, R.elected s q e needs → closed q →
      (∃ n ∈ needs, closed n.producer) ∨ (∃ child ∈ e.kids, closed child))
    {q t e} (trace : SourceTrace R s q t e) (d : Dictionary)
    (completed : Summarizes t (.selected d)) : ¬ closed q := by
  exact SourceTrace.rec
    (motive_1 := fun q t _ _ => ∀ d, Summarizes t (.selected d) → ¬ closed q)
    (motive_2 := fun qs ts _ => ∀ (ds : List Dictionary), All₂ Summarizes ts (ds.map Result.selected) →
      ∀ q ∈ qs, ¬ closed q)
    (motive_3 := fun needs _ => ∀ n ∈ needs, ¬ closed n.producer)
    (fun _ _ impossible => by cases impossible)
    (fun verdict _ _ _ _ _ impossible => by cases verdict <;> cases impossible)
    (fun event _ choose _ _ aux children _ summary closedRoot => by
      rcases needsFamily _ event _ choose closedRoot with ⟨n,hit,same⟩ | ⟨child,hit,same⟩
      · exact aux n hit same
      · cases summary with
        | selected rows combine =>
          cases combine with
          | selected exacts =>
            rw [exacts] at rows
            exact children _ rows child hit same)
    (fun _ _ q unseen => by cases unseen)
    (fun _ _ first later ds summary q found => by
      cases ds with
      | nil => cases summary
      | cons d ds =>
        cases summary with
        | cons atD after =>
          rcases List.mem_cons.mp found with rfl | tail
          · exact first d atD
          · exact later ds after q tail)
    (fun n unseen => by cases unseen)
    (fun _ completed _ _ first later n found => by
      rcases List.mem_cons.mp found with rfl | tail
      · exact first _ completed
      · exact later n tail)
    trace d completed

end Yulang.GeneralDeclarativeI65.I72
