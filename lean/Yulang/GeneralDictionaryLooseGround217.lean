import Yulang.GeneralDictionaryLooseVariant217
import Yulang.GeneralNominalGroundAccessibility
import Yulang.GeneralDeclarationExamples

/-! Two real models of a loose nominal source refute GroundRoots, not I40.
Merely choosing a ground witness cannot discharge universal source grounding. -/
namespace Yulang.GeneralDictionaryLooseGround217
open CommonNominalFullCarrier GeneralDictionaryLooseVariant217
open GeneralNominalState GeneralNominalCommonBridge

abbrev base : GeneralSourceState.State where
  slots := 3
  source := Fin.val
  source_injective := fun _ _ equal => Fin.ext equal
  rowSource := Fin.val
  ordinary := []
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro i; exact Fin.elim0 i
  heads := fun _ => .unresolved
  intervals := []
  heads_sound := by intro _ _ _ _ impossible; cases impossible
  intervals_sound := by intro _ _ _ impossible; cases impossible

abbrev view : GeneralNormalizedObservation.Snapshot base where
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro i; exact Fin.elim0 i
  canonical := by intro i; exact Fin.elim0 i
  heads := fun _ => .deferred .unresolved
  checked := by intro _ _ impossible; cases impossible

abbrev constructor : GeneralDeclarationPatterns.Constructor := ⟨[.type,.type],0⟩
abbrev descriptor : Descriptor 3 := ⟨0,constructor,[.type (0,1),.type (0,1)],rfl⟩
abbrev snapshot : State where
  base := base
  view := view
  constructors := fun _ => some constructor
  nominals := fun slot => if slot.val = 2 then some descriptor else none
  catalogue := by intro slot d found; split at found <;> cases found; rfl
  bodies_opaque := by intro _ _ _; rfl

def assignment (a b : Ty) : Assignment := fun source =>
  (if source = 0 then low else if source = 1 then high else nominal 0 [.inl a,.inl b],Common.rowEmpty)

theorem models (a b : Ty) (one : Subtype low a ∧ Subtype a high)
    (two : Subtype low b ∧ Subtype b high) : Models snapshot (assignment a b) := by
  refine ⟨⟨?_,?_,?_⟩,?_,?_⟩
  · intro _ impossible; cases impossible
  · intro _ _ impossible; cases impossible
  · intro _ impossible; cases impossible
  · intro slot d found
    change (if slot.val = 2 then some descriptor else none) = some d at found
    split at found
    · rename_i isRoot
      cases Option.some.inj found
      refine ⟨[.inl a,.inl b],.cons ?_ (.cons ?_ .nil),?_⟩
      · exact one
      · exact two
      · change Equivalent (assignment a b slot.val).1 _
        rw [isRoot]
        exact ⟨subtype_refl _,subtype_refl _⟩
    · cases found
  · intro _ impossible; cases impossible

theorem distinct_roots : ¬ Equivalent (assignment first second 2).1 (assignment second first 2).1 := by
  intro same
  have invariant := (nominal_regular_invariant_exact 0 0 [.inl first,.inl second] [.inl second,.inl first]).mp same.1
  exact unequal (invariant.2.2 0 (.inl first) (.inl second) rfl rfl)

theorem no_uniform_root : ¬ ∃ value : Ty, ∀ model, Models snapshot model → Equivalent (model 2).1 value := by
  rintro ⟨value,uniform⟩
  have one := uniform (assignment first second) (models first second fits_first fits_second)
  have two := uniform (assignment second first) (models second first fits_second fits_first)
  exact distinct_roots ⟨subtype_trans one.1 two.2,subtype_trans two.1 one.2⟩

abbrev roles : Roles.RoleDecls := fun _ => GeneralDeclarationExamples.bareRole
abbrev interpretation : GeneralNominalInspection.Interpretation :=
  ⟨fun _ => none,fun _ => false,by intro _ impossible; cases impossible⟩
abbrev context : GeneralNominalCandidates.Context := ⟨snapshot,interpretation⟩
abbrev root : GeneralSourceDictionaries.Occurrence roles := ⟨0,⟨0,fun _ => (2,2),[],by intro _ impossible; cases impossible⟩⟩

theorem not_ground (labels : List GeneralDeclarationPatterns.Pattern) :
    ¬ GeneralNominalGroundAccessibility.GroundRoots context root labels := by
  rintro ⟨_,ground⟩
  obtain ⟨term,_,fixed⟩ := ground ⟨0,by decide⟩
  exact no_uniform_root ⟨_,fixed⟩
end Yulang.GeneralDictionaryLooseGround217
