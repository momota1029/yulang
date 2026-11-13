import Yulang.GeneralNominalValueSupport

/-! A journal equation between existing source identities supplies a certified
nominal head. The two-slot snapshot is only a witness for HeadSupported; it
adds no solver variable or interval center to the tracked state. -/
namespace Yulang.GeneralNominalValueHeadCertificate
open GeneralNominalSupport
open CommonNominalFullCarrier

private def base (parent child : Nat) (different : parent ≠ child) : GeneralSourceState.State where
  slots := 2
  source := fun slot => if slot.val = 0 then parent else child
  source_injective := by
    intro first last same
    have one : first = 0 ∨ first = 1 := by
      have := first.isLt
      by_cases zero : first.val = 0
      · exact Or.inl (Fin.ext zero)
      · exact Or.inr (Fin.ext (by omega))
    have two : last = 0 ∨ last = 1 := by
      have := last.isLt
      by_cases zero : last.val = 0
      · exact Or.inl (Fin.ext zero)
      · exact Or.inr (Fin.ext (by omega))
    rcases one with rfl | rfl <;> rcases two with rfl | rfl
    · rfl
    · exact False.elim (different (by simpa using same))
    · exact False.elim (different (by simpa using same.symm))
    · rfl
  rowSource := fun slot => slot.val
  ordinary := []
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro kind; exact Fin.elim0 kind
  heads := fun _ => .unresolved
  intervals := []
  heads_sound := by intro _ _ _ _ impossible; cases impossible
  intervals_sound := by intro _ _ _ impossible; cases impossible

private def view (parent child : Nat) (different : parent ≠ child) :
    GeneralNormalizedObservation.Snapshot (base parent child different) where
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro kind; exact Fin.elim0 kind
  canonical := by intro kind; exact Fin.elim0 kind
  heads := fun _ => .deferred .unresolved
  checked := by intro _ _ impossible; cases impossible

private def descriptor (name : Nat) : GeneralNominalState.Descriptor 2 :=
  ⟨name,⟨[.type],name⟩,[.type (1,1)],rfl⟩

private def snapshot (parent child name : Nat) (different : parent ≠ child) : GeneralNominalState.State where
  base := base parent child different
  view := view parent child different
  constructors := fun key => if key = name then some ⟨[.type],name⟩ else none
  nominals := fun slot => if slot.val = 0 then some (descriptor name) else none
  catalogue := by
    intro slot actual recorded
    split at recorded
    · have same := Option.some.inj recorded
      subst actual
      simp [descriptor]
    · cases recorded
  bodies_opaque := by intro _ _ _; rfl

theorem of_nominal_equation (state : Tracked roles) (support : List (GeneralSourceDictionaries.Occurrence roles))
    (parent child name : Nat) (different : parent ≠ child)
    (entailed : ∀ model, Slice state support model →
      Equivalent (model parent).1 (nominal name [.inl (model child).1])) :
    HeadSupported state support parent (.nominal name 1) := by
  refine ⟨snapshot parent child name different,
    .nominal (base parent child different) (0 : Fin 2) (descriptor name),
    Head.nominal (snapshot := snapshot parent child name different) (0 : Fin 2) (descriptor name) rfl,?_⟩
  intro model valid
  exact (GeneralNominalState.denotes_singleton_exact (base parent child different) model (0 : Fin 2) (1 : Fin 2)
    (descriptor name) rfl).mpr (entailed model valid)

end Yulang.GeneralNominalValueHeadCertificate
