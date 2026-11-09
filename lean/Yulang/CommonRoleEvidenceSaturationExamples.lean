import Yulang.CommonRoleEvidenceNormalization

/-! Real three-slot ordinary states. A two-edge chain requires repeated evidence
transfer; reciprocal cycles do not require caller-provided depth. -/
namespace Yulang.CommonRoleEvidenceSaturationExamples
open Core.PresenceGeneration (Comp TyTerm)
open PresenceNormalForm (All Atom)
open CommonRoleSettledConstraints (State)
open CommonRoleCandidateStateFrontier (extend extend_exact)
open CommonRoleEvidenceNormalization (normalize)

def atoms : List (Atom (Fin 3)) :=
  [.tyLe (.var 0) (.var 1), .tyLe (.var 1) (.var 0),
   .tyLe (.var 1) (.var 2), .tyLe (.var 2) (.var 1)]
def chain : State 3 where
  atoms := atoms
  child := by
    intro a h
    simp only [atoms, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl <;> trivial
  width := by
    intro a b h tail ht
    simp only [atoms, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h <;> cases h <;> cases ht
  rows := by
    intro a h
    simp only [atoms, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl <;> trivial

def input : State 3 := extend chain 2 .int

theorem before_unknown : CommonRoleOrdinaryKnownness.materialize input.atoms 0 = none := by decide

theorem after_all_int (i : Fin 3) :
    CommonRoleOrdinaryKnownness.materialize (normalize input).atoms i = some Roles.Examples.int := by
  revert i
  decide

theorem all_int_model : All Common.model
    (fun (_ : Fin 3) => Comp.pure Common.model (.base .int)) input.atoms := by
  rw [input, extend_exact]
  constructor
  · intro a h
    simp only [chain, atoms, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl <;> exact Common.subtype_refl _
  · exact Common.equivalent_refl _

theorem same_models (a : Fin 3 → Comp Common.model) :
    All Common.model a (normalize input).atoms ↔ All Common.model a input.atoms :=
  CommonRoleEvidenceNormalization.normalize_models input a

/-- No new scalar fact appears on a second saturation pass, even with cycles. -/
theorem second_pass (f : CommonRoleEvidenceSaturation.Fact 3) :
    f ∈ CommonRoleEvidenceSaturation.saturate (normalize input) ↔
      f ∈ CommonRoleEvidenceSaturation.saturate input :=
  CommonRoleEvidenceNormalization.saturate_fixedpoint input f

end Yulang.CommonRoleEvidenceSaturationExamples
