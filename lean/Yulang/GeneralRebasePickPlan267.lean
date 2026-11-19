import Yulang.GeneralRebaseSourceClassification267

namespace Yulang.GeneralRebasePickPlan267
open GeneralNominalCenters (Plan)
open GeneralSourceDictionaries (Occurrence)
open GeneralRebaseHeadProbe267 (Match observation positive positive_exact)
open GeneralRebaseSourceClassification267 (verdict structural_valid)
open GeneralRebasePartialClassification267 (Verdict)

local instance : DecidableEq (Occurrence roles) := GeneralRebaseOccurrenceEq267.occurrenceEq

def matching (probe : Plan roles → Option Bool) (target : Match roles) (plan : Plan roles) : Bool :=
 decide (probe plan = some true ∧ observation plan = target)

theorem matches_exact (probe : Plan roles → Option Bool) (target : Match roles) (plan : Plan roles) :
 matching probe target plan = true ↔ probe plan = some true ∧ observation plan = target := by
 simp [matching]

def pick (probe : Plan roles → Option Bool) (entries : List (Plan roles)) (target : Match roles) :
 Option (Plan roles) := entries.find? (matching probe target)

theorem pick_sound (probe : Plan roles → Option Bool) (entries : List (Plan roles)) (target : Match roles)
 (found : pick probe entries target = some plan) :
 plan ∈ entries ∧ probe plan = some true ∧ observation plan = target :=
 ⟨List.mem_of_find?_eq_some found,(matches_exact ..).mp (List.find?_some found)⟩

theorem pick_complete (probe : Plan roles → Option Bool) (entries : List (Plan roles)) (target : Match roles)
 (listed : target ∈ positive probe entries) : ∃ plan, pick probe entries target = some plan := by
 obtain ⟨plan,inside,yes,observation⟩ := (positive_exact ..).mp listed
 cases result : pick probe entries target with
 | some found => exact ⟨found,rfl⟩
 | none =>
   exfalso
   exact (List.find?_eq_none.mp result plan inside) ((matches_exact ..).mpr ⟨yes,observation⟩)

theorem picks_unique (probe : Plan roles → Option Bool) (entries : List (Plan roles)) (target : Match roles)
 (chosen : verdict probe entries = .unique target) : ∃ plan, pick probe entries target = some plan := by
 have valid := structural_valid probe entries
 rw [chosen] at valid
 exact pick_complete probe entries target valid.1

end Yulang.GeneralRebasePickPlan267
