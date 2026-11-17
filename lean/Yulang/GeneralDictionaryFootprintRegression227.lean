import Yulang.GeneralDictionaryEffectProvenance227
import Yulang.GeneralDictionaryDefaultRegression208

/-! Concrete default-install regression for the semantic footprint. The real
state change still removes the bottom default model and retains the integer
model; finite-support reductions have not silently weakened that obligation. -/
namespace Yulang.GeneralDictionaryFootprintRegression227
open GeneralDictionarySemanticTrace227
open GeneralDictionarySemanticDelta223 (Depends)

namespace Default206
open GeneralDictionaryDefaultGap206Source GeneralDictionaryDefaultGap206Local
open GeneralDictionaryDefaultGap206State GeneralDictionaryDefaultRegression208
open GeneralNominalCenteredHeadMatStepJournal

noncomputable def pool : List Nat := initialSources context root ++
  GeneralDictionaryOriginJournal227.installDelta start effect

theorem footprint : Footprint registry context root after pool :=
  .tail .initial (.install effect .root enabled not_committed)

theorem dependency : Depends after pool := footprint.depends

theorem strict_default_change : Depends after pool ∧ Models after model ∧ ¬ Models after counter :=
  ⟨dependency,int_retained,bottom_removed⟩

/-- An unchanged default-only request class contributes no new body reads or
cross-output target reads to its historical effect delta. -/
theorem unchanged_delta : GeneralDictionaryOriginClass227.deltaSources start.core start.core root plan = [] := by
  classical
  have fresh : GeneralDictionaryClassDelta227.newRequests start.core start.core root = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro output member
    have parts := GeneralDictionaryClassDelta227.mem_new.mp member
    exact parts.2 parts.1
  have affected : GeneralDictionaryClassDelta227.affected start.core start.core root = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro output member
    obtain ⟨_,other,present,_⟩ := GeneralDictionaryClassDelta227.mem_affected.mp member
    simp [fresh] at present
  rw [GeneralDictionaryOriginClass227.names_covered (fun output member => ⟨output,member,rfl⟩),affected]
  rfl
end Default206

end Yulang.GeneralDictionaryFootprintRegression227
