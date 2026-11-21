import Yulang.GeneralDeclarativeTrace321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeRepresentatives321
open GeneralDeclarativeHead320 (State byMode)
open GeneralDeclarativeLowerKnown321 (Alias alias_refl)
open GeneralDeclarativeTrace321 (Occurrence Links Trace TraceArgs)
open GeneralDeclarativeWhere319 (Capture)
open GeneralNominalMaterialization (Mode)

def namesOf (seen : List Occurrence) (binder : Nat) (mode : Mode) : List Nat :=
  seen.filterMap fun occ =>
    if occ.binder = binder ∧ occ.mode = mode then some occ.argument else none

theorem namesOf_exact {seen : List Occurrence} {binder : Nat} {mode : Mode} {name : Nat} :
    name ∈ namesOf seen binder mode ↔ (⟨binder,mode,name⟩ : Occurrence) ∈ seen := by
  constructor
  · intro found
    obtain ⟨⟨b,md,n⟩,present,one⟩ := List.mem_filterMap.mp found
    change (if b = binder ∧ md = mode then some n else none) = some name at one
    split at one
    next matchKey =>
      obtain ⟨rfl,rfl⟩ := matchKey
      cases one
      exact present
    next =>
      cases one
  · intro present
    exact List.mem_filterMap.mpr ⟨⟨binder,mode,name⟩,present,by simp⟩

/-- No default fictitious name: if there is no occurrence of this binder
in this mode, the supplied fallback is retained, unchanged and explicit. -/
def choose (seen : List Occurrence) (fallback : Nat → Mode → Nat) (binder : Nat) (mode : Mode) : Nat :=
  (namesOf seen binder mode).headD (fallback binder mode)

def captureOf (seen : List Occurrence) (fallback : Nat → Mode → Nat) (binder : Nat) : Capture :=
  ⟨choose seen fallback binder .lower, choose seen fallback binder .actual,
    choose seen fallback binder .upper⟩

theorem used_mode {seen : List Occurrence} {fallback : Nat → Mode → Nat} {o : Occurrence}
    (found : o ∈ seen) : (⟨o.binder,o.mode,choose seen fallback o.binder o.mode⟩ : Occurrence) ∈ seen := by
  rcases o with ⟨binder,mode,name⟩
  have h := namesOf_exact.mpr found
  cases shape : namesOf seen binder mode with
  | nil =>
    rw [shape] at h
    cases h
  | cons first rest =>
    apply namesOf_exact.mp
    simp [choose, shape]

theorem chosen_reads (seen : List Occurrence) (fallback : Nat → Mode → Nat)
    (consistent : ∀ first ∈ seen, ∀ second ∈ seen, first.binder = second.binder →
      first.mode = second.mode → Alias s first.argument second.argument) :
    Links s (captureOf seen fallback) seen := by
  intro o occurs
  have selected := used_mode (fallback := fallback) occurs
  have same := consistent o occurs _ selected rfl rfl
  rcases o with ⟨binder,mode,name⟩
  cases mode <;> exact same

theorem actual_occurrence_tracked (seen : List Occurrence) (fallback : Nat → Mode → Nat)
    {binder : Nat} (occurs : ∃ name, (⟨binder,.actual,name⟩ : Occurrence) ∈ seen) :
    (⟨binder,.actual,(captureOf seen fallback binder).center⟩ : Occurrence) ∈ seen := by
  obtain ⟨name,found⟩ := occurs
  exact used_mode (fallback := fallback) found

/-- Selected actual centers come from source occurrences, not an interval
interpolation or a model witness. Equivalent occurrences can be used in
place of each other without changing the all-model read. -/
theorem chosen_entails {s : State} (seen : List Occurrence) (fallback : Nat → Mode → Nat)
    (sub : used ⊆ seen)
    (consistent : ∀ first ∈ seen, ∀ second ∈ seen, first.binder = second.binder →
      first.mode = second.mode → Alias s first.argument second.argument)
    (trace : Trace s mode arg expr used) :
    GeneralDeclarativeEntailment320.Entails s
      ⟨arg,GeneralDeclarativeSubstitution320.logical (captureOf seen fallback) mode expr⟩ :=
  GeneralDeclarativeTrace321.trace_equation trace
    (fun occurrence inTrace => chosen_reads seen fallback consistent occurrence (sub inTrace))

end Yulang.GeneralDeclarativeRepresentatives321
