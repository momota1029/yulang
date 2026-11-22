import Yulang.GeneralDeclarativeFreshValues343

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 15400
set_option maxHeartbeats 6500000
namespace Yulang.GeneralDeclarativePlacement343
open GeneralDeclarativeLogicalChild343 (stage protect fresh output child)
open GeneralDeclarativeFreshModel343 (kept fixed_output_model)
open GeneralDeclarativeFreshValues343 (mode_match)
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeEntailment320 (appendFacts model_append Holds)
open GeneralDeclarativeLowerKnown321 (Alias)
open GeneralDeclarativeVersionedPhysical342 (new_registered)
open GeneralDeclarativeVersionedChildView342 (arg d actual_arguments)
open GeneralDeclarativeVersionedTree342 (child_requests)
open GeneralDeclarativeStoppedPaired341 (Placement activeDemand)
open GeneralWherePhysicalCommit319 (final newChild)
open GeneralWhereVersionInstall317 (Models)
open GeneralNominalCommonBridge (Assignment)
open GeneralStoppedPlacement335 (Meaning)
open CommonNominalFullCarrier (Equivalent)
open GeneralDeclarativeNewNames321 (before_after)

noncomputable abbrev actual := arg
noncomputable abbrev symbolic := GeneralDeclarativeLogicalChild343.arg kept
abbrev bridge (old new : Nat) : Equation := ⟨old,.variable new⟩
noncomputable abbrev rows : List Equation :=
  [bridge actual.lower symbolic.lower,bridge actual.center symbolic.center,bridge actual.upper symbolic.upper]
noncomputable abbrev view : State := appendFacts (output kept) rows

theorem fresh_lower {n : Nat} (valid : n ∈ kept) : n < symbolic.lower := by
  change n < fresh kept
  unfold fresh GeneralDeclarativeFreshWhere325.seed
  apply before_after
  exact List.mem_append_left _ (List.mem_append_right _ (List.mem_append_right _ valid))

theorem avoids_history {n : Nat} (valid : n ∈ kept) :
    n ≠ symbolic.lower ∧ n ≠ symbolic.center ∧ n ≠ symbolic.upper := by
  have lo := fresh_lower valid
  change n < fresh kept at lo
  change n ≠ fresh kept ∧ n ≠ fresh kept + 1 ∧ n ≠ fresh kept + 2
  omega

theorem aliases_valid (n : Assignment) (raw : Models final n)
    (ordinary : GeneralDeclarativeHead320.Models (output kept) n) :
    GeneralDeclarativeHead320.Models view n := by
  have common := mode_match n raw ordinary
  refine (model_append n).mpr ⟨ordinary,?_⟩
  intro row used
  rcases List.mem_cons.mp used with first|rest
  · cases first
    exact common.1
  · rcases List.mem_cons.mp rest with mid|last
    · cases mid
      exact common.2.1
    · cases List.mem_singleton.mp last
      exact common.2.2

theorem kept_model (m : Assignment) (fit : Models final m) :
    ∃ n, GeneralDeclarativeHead320.Models view n ∧
      (∀ k ∈ kept, n k = m k) ∧ Models final n := by
  obtain ⟨n,ordinary,agrees,raw⟩ := fixed_output_model m fit
  exact ⟨n,aliases_valid n raw ordinary,agrees,raw⟩

theorem read_aliases :
    Alias view actual.lower symbolic.lower ∧
    Alias view actual.center symbolic.center ∧
    Alias view actual.upper symbolic.upper :=
  ⟨.forward (List.mem_append_right _ List.mem_cons_self),
   .forward (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)),
   .forward (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))⟩

theorem actual_place :
    Placement final.mixed view newChild.occurrence (child kept) := by
  refine ⟨newChild,new_registered,rfl,?_⟩
  have eq : activeDemand final.mixed newChild = d := by
    unfold activeDemand
    rw [actual_arguments,child_requests] <;> rfl
  rw [eq]
  exact ⟨rfl,.cons ⟨read_aliases.1,read_aliases.2.1,read_aliases.2.2⟩ .nil,rfl⟩

end Yulang.GeneralDeclarativePlacement343
