import Yulang.GeneralNominalTotalLocation304
import Yulang.GeneralRebaseCandidateChecks267
import Yulang.GeneralRebaseRawK2Probe268

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalPendingReindex304
open GeneralNominalRefinements (Refines)
open GeneralNominalKnownBit304 (knownBit known_exact)
open GeneralNominalTotalLocation304 (known_reindex)
open GeneralNominalState (State RootPending)
open GeneralSourceState (Demand)

def pending (s : State) (d : Demand roles) : Bool :=
  (List.finRange (roles d.role).arity).any fun i => !knownBit s (d.arguments i).1

theorem pending_exact (s : State) (d : Demand roles) :
    pending s d = true ↔ RootPending s d := by
  have one source : (!knownBit s source) = true ↔ ¬ GeneralNominalState.Known s source := by
    cases h : knownBit s source
    · refine ⟨fun _ yes => ?_,fun _ => rfl⟩
      have bit := (known_exact s source).mpr yes
      rw [h] at bit
      cases bit
    · refine ⟨?_,fun no => False.elim (no ((known_exact s source).mp h))⟩
      intro impossible
      cases impossible
  unfold pending RootPending
  simp only [List.any_eq_true,List.mem_finRange,true_and,one]

theorem pending_reflect (s : State) (d : Demand roles) :
    GeneralRebasePartialBool268.Reflect (RootPending s d) (some (pending s d)) :=
  GeneralRebaseRawK2Probe268.bool_reflect _ _ (pending_exact s d)

theorem pending_reindex (forward : Refines a b) (inverse : Refines b a) (d : Demand roles) :
    pending a d = pending b d := by
  unfold pending
  simp only [known_reindex forward inverse]

theorem old_compiler_agrees (s : State) (d : Demand roles) :
    (!GeneralRebaseCandidateChecks267.allKnown s d) = pending s d := by
  have selected : GeneralRebaseCandidateChecks267.allKnown s d = true ↔ ¬ RootPending s d :=
    GeneralRebaseCandidateChecks267.allKnown_exact s d
  have observed := pending_exact s d
  by_cases h : RootPending s d
  · rw [observed.mpr h]
    cases old : GeneralRebaseCandidateChecks267.allKnown s d
    · rfl
    · exact False.elim ((selected.mp old) h)
  · rw [selected.mpr h]
    cases now : pending s d
    · rfl
    · exact False.elim (h (observed.mp now))

end Yulang.GeneralNominalPendingReindex304
