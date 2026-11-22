import Yulang.GeneralStoppedDisplayCut335
import Yulang.GeneralStoppedPlacement335

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 24000
set_option maxHeartbeats 16000000
namespace Yulang.GeneralStoppedDisplayExtended335
open GeneralStoppedDisplayProjection335
open GeneralStoppedDisplayCut335
open GeneralNominalExamples (registry interpretation intDisplay)
open GeneralDeclarationExamples (display)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeOrigins321 (Supported from_source)
open GeneralDeclarativeGrowth327 (Extends restrict)
open GeneralDeclarativeBounds319 (Bound)
open GeneralDeclarativeLowerKnown321 (Alias alias_refl)
open GeneralDeclarativeNestedBody332 (compileBody)
open GeneralDeclarativeFootprint321 (stateNames preserves_models)
open GeneralDeclarativeOpaqueNominal328 (point)
open GeneralStoppedPlacement335 (SameDemand)
open CommonNominalFullCarrier (subtype_refl)
open GeneralNominalCommonBridge (Assignment)
open PresenceNormalForm (Atom)

abbrev extra : List (Atom Nat) :=
  [.tyLe (.var 1) (.var 1),.tyLe (.var 1) (.var 1),
   .tyLe (.var 2) (.var 1),.tyLe (.var 1) (.var 2),
   .tyLe (.var 3) (.var 1),.tyLe (.var 1) (.var 3),
   .tyLe (.var 2) (.var 1),.tyLe (.var 1) (.var 3)]

abbrev expanded : State := ⟨⟨closed.normal.ordinary ++ extra,closed.normal.intervals⟩,closed.equations⟩

theorem written :
    compileBody registry interpretation parentDemand display ordinary sourceSpans protect fallback targets =
      some (expanded,[reminted]) := by
  rw [literal_state] <;> rfl

theorem child_compiles :
    compileBody registry interpretation reminted intDisplay expanded [] protect fallback targets =
      some (expanded,[]) := rfl

theorem contains_closed : Extends closed expanded :=
  ⟨fun _ used => List.mem_append_left _ used,fun _ used => used,fun _ used => used⟩

theorem contains_raw : Extends ordinary expanded := literal_state.symm ▸ contains_closed

/-- This expansion records no new source row and gives no origin
credit to the extra ordinary interval edges. -/
def augmented (done : Nat → Prop) : Supported expanded done :=
  GeneralStoppedLower335.original initialOrdinary expanded (fun _ used => used) done

theorem keeps_original_rows (done : Nat → Prop) :
    (GeneralDeclarativeOrigins321.restriction (augmented done)).equations =
      (GeneralDeclarativeOrigins321.restriction (supported done)).equations := rfl

theorem placement : SameDemand expanded childDemand reminted := by
  refine ⟨rfl,.cons ⟨.bounds (.constraint ?_) (.constraint ?_),alias_refl _,
    .bounds (.constraint ?_) (.constraint ?_)⟩ .nil,rfl⟩
  all_goals apply List.mem_append_right _; decide +kernel

def extend (m : Assignment) : Assignment := fun n =>
  if n = 2 ∨ n = 3 then ((m 1).1,(m n).2) else m n

theorem existing_names {m : Assignment} {name : Nat}
    (prev : name ∈ stateNames closed) : extend m name = m name := by
  change name ∈ [1,1,1,1,0,0,0,0,1,1,0,0,1,1,0,1,1] at prev
  simp only [List.mem_cons,List.not_mem_nil,or_false] at prev
  rcases prev with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst name <;> rfl

theorem augmented_models {m : Assignment} (valid : Models closed m) :
    Models expanded (extend m) := by
  have held := (preserves_models closed (first := extend m) (last := m)
    (fun _ same => existing_names same)).mpr valid
  refine ⟨⟨(PresenceNormalForm.all_append _ _ _ _).mpr ⟨held.1.1,?_⟩,held.1.2⟩,held.2⟩
  intro a seen
  simp only [extra,List.mem_cons,List.not_mem_nil,or_false] at seen
  rcases seen with h|h|h|h|h|h|h|h <;> cases ‹_› <;> exact subtype_refl _

/-- The unchanged compiler preserves the stopped raw model on all
preexisting ordinary names, not on unconstrained fresh names 2,3. -/
theorem conservative (m : Assignment) :
    GeneralNominalVersionedJournal232.Models GeneralRebaseDisplayFrame276.after m ↔
      ∃ n, Models expanded n ∧ ∀ name ∈ stateNames closed, n name = m name := by
  constructor
  · intro raw
    have h := (actual_model m).mpr raw
    rw [literal_state] at h
    exact ⟨extend m,augmented_models h,fun _ listed => existing_names listed⟩
  · rintro ⟨n,ordinary,kept⟩
    apply (actual_model m).mp
    rw [literal_state]
    exact (preserves_models closed kept).mp (restrict contains_closed n ordinary)

end Yulang.GeneralStoppedDisplayExtended335
