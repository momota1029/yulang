import Yulang.GeneralPresenceReadback245
import Yulang.GeneralPresenceOwnerOwnership244

/-! Fresh replacement with targets drawn from an external old block cannot
change a term already inlined with that old block. These are syntax laws;
no reflexivity or antisymmetry of semantic subtyping is assumed. -/
namespace Yulang.GeneralPresenceAbsorb245
open Core.PresenceGeneration
open GeneralPresenceDefinitionRewrite244 GeneralPresenceSubstitutionSupport244
open GeneralPresenceOwnerRewrite244 GeneralPresenceCrossRead244
open GeneralPresenceFixedInline244 GeneralPresenceReadback245
open GeneralPresenceOwnerOwnership244
variable {Name : Type} [DecidableEq Name]

omit [DecidableEq Name] in
theorem avoid_within (old fresh : List (Entry Name))
    (within : TargetsWithin fresh old) (sources : List Name)
    (outside : Avoid old sources) : Avoid fresh sources := by
  intro source member target present
  obtain ⟨original, originalMem, equal⟩ := within target present
  rw [← equal]
  exact outside source member original originalMem

theorem mapping_absorb (old fresh : List (Entry Name))
    (external : External old) (coherent : Coherent old)
    (within : TargetsWithin fresh old) (name : Name) :
    (substitution old name).ty.subst (substitution fresh) =
      (substitution old name).ty := by
  cases found : lookup old name with
  | some term =>
    have outside := avoid_within old fresh within _
      (external (name,term) (lookup_member found))
    simpa [substitution,found] using type_fixed fresh term outside
  | none =>
    have outside : ∀ entry ∈ fresh, entry.1 ≠ name := by
      intro entry member same
      obtain ⟨original,originalMem,equal⟩ := within entry member
      have oldFound := lookup_of_member old coherent original originalMem
      rw [equal,same,found] at oldFound
      cases oldFound
    simpa [substitution,found,TyTerm.subst] using target_unchanged outside

theorem type_absorb (old fresh : List (Entry Name))
    (external : External old) (coherent : Coherent old)
    (within : TargetsWithin fresh old) (term : TyTerm Name) :
    (term.subst (substitution old)).subst (substitution fresh) =
      term.subst (substitution old) := by
  induction term with
  | var name => exact mapping_absorb old fresh external coherent within name
  | base | bottom | top | emptyRecord | exactEmpty => rfl
  | union a b one two => simp only [TyTerm.subst,one,two]
  | inter a b one two => simp only [TyTerm.subst,one,two]
  | pair a b one two => simp only [TyTerm.subst,one,two]
  | record label a b one two => simp only [TyTerm.subst,one,two]
  | recordDefault label a b one two => simp only [TyTerm.subst,one,two]
  | required label a ih => simp only [TyTerm.subst,ih]
  | variant label a ih => simp only [TyTerm.subst,ih]
  | arrow a incoming b outgoing one two =>
    simp only [TyTerm.subst,one,two,row_fixed]

theorem atom_absorb (old fresh : List (Entry Name))
    (external : External old) (coherent : Coherent old)
    (within : TargetsWithin fresh old) (atom : PresenceNormalForm.Atom Name) :
    atomSubst (substitution fresh) (atomSubst (substitution old) atom) =
      atomSubst (substitution old) atom := by
  cases atom <;>
    simp only [atomSubst,type_absorb old fresh external coherent within,row_fixed]

theorem block_absorb (old fresh : List (Entry Name))
    (external : External old) (coherent : Coherent old)
    (within : TargetsWithin fresh old) (atoms : List (PresenceNormalForm.Atom Name)) :
    (atoms.map (atomSubst (substitution old))).map (atomSubst (substitution fresh)) =
      atoms.map (atomSubst (substitution old)) := by
  simp only [List.map_map,Function.comp_def,atom_absorb old fresh external coherent within]

end Yulang.GeneralPresenceAbsorb245
