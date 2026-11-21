import Yulang.GeneralLiveCompoundStable316

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27000
set_option maxHeartbeats 36000000
namespace Yulang.GeneralLiveCompoundPostLeafCycles316
open GeneralNominalMixedRecurrence
open GeneralLiveCompoundPost316 (raw raw_models)
open GeneralLiveCompoundUpperSnapshot316 (snap)
open GeneralLiveCompoundLeafInstall316 (after after_model)
open GeneralLiveCompoundLeafProof316 (w center_value)
open GeneralDictionaryCompoundBase239 (lo)
open GeneralMixedCompoundChildEquality307 (mid)
open GeneralNominalVersionedCycles232 (Cyclic)

theorem earlier_edge {a b : Fin 8} (e : Edge raw a b) : Edge snap a b := by
  rcases e with concrete|⟨descriptor,present,index,semantic⟩
  · exact Or.inl concrete
  · exact Or.inr ⟨descriptor,present,index,fun m h => semantic m ((raw_models m).mpr h)⟩

private theorem path_target {state : GeneralNominalState.State} (target : Fin state.base.slots)
    (no : ∀ a, ¬ Edge state a target)
    {a b : Fin state.base.slots} (path : Path state a b) : b = target → a = target := by
  induction path with
  | nil => exact id
  | cons e rest ih =>
    intro isLast
    have same := ih isLast
    cases same
    exact False.elim (no _ e)

theorem map_path {first last : GeneralNominalState.State} (f : Fin first.base.slots → Fin last.base.slots)
    (lift : ∀ a b, Edge first a b → Edge last (f a) (f b))
    {a b : Fin first.base.slots} (p : Path first a b) : Path last (f a) (f b) := by
  induction p with
  | nil => exact .nil _
  | cons e _ ih => exact .cons (lift _ _ e) ih

theorem old_edge {a b : Fin 8} (edge : Edge raw a b) :
    Edge GeneralMixedCompoundUpperSnapshot307.snap a b := by
  rcases earlier_edge edge with structural|⟨desc,present,index,proof⟩
  · exact Or.inl structural
  · exact Or.inr ⟨desc,present,index,proof⟩

theorem no_raw : ¬ GeneralNominalCycleK2.RecursAt raw (5 : Fin 8) := by
  intro bad
  have none (a : Fin 8) : ¬ Edge raw a (5 : Fin 8) := fun edge =>
    GeneralLiveCompoundLeafCycles316.no_raw_incoming a (earlier_edge edge)
  obtain ⟨next,edge,tail⟩ := GeneralNominalCycleK2.recurs_cycle _ _ bad
  have eq := path_target (state := raw) (5 : Fin 8) none tail rfl
  subst next
  exact none _ edge

theorem no_lo : ¬ Cyclic after (.source lo) :=
  GeneralLiveCompoundDepth316.headless_variant_no_cycle after_model GeneralLiveCompoundLeafCycles316.lower_actual
    GeneralDictionaryOptionalOutput229.no_test

theorem no_mid : ¬ Cyclic after (.source mid) :=
  GeneralRebaseTreeAcyclic272.acyclic _ _ after_model _ _ GeneralLiveCompoundLeafCycles316.canonical
    (GeneralRebaseInstalledReadback271.source_at _ _ _ center_value)

end Yulang.GeneralLiveCompoundPostLeafCycles316
