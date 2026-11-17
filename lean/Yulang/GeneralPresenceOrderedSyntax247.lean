import Yulang.GeneralPresenceOrderedSubstitution247
import Yulang.GeneralPresenceOrderedDependence247
/-! Typed support of finite ordered expansion. Row-only references are deliberately
not eliminated: substitutions preserve them literally. These results concern a
fixed finite block, not growth or normalization of changing source definitions. -/
namespace Yulang.GeneralPresenceOrderedSyntax247
open Core.PresenceGeneration PresenceNormalForm
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOwnerRewrite244
open GeneralPresenceOrderedBlock247 GeneralPresenceOrderedSubstitution247
open GeneralPresenceUsedSupport245
variable {Name : Type} [DecidableEq Name]

omit [DecidableEq Name] in
theorem typed_subst (term : TyTerm Name) (replacement : Name → CompTerm Name) :
 typedReads (term.subst replacement) = (typedReads term).flatMap (fun name => typedReads (replacement name).ty) := by
 induction term <;> simp_all [typedReads,TyTerm.subst,List.flatMap_append]

theorem mapping_outside (entries : List (Entry Name)) (name : Name)
 (outside : ∀ entry ∈ entries, entry.1 ≠ name) : (mapping entries name).ty = .var name := by
 induction entries with
 | nil => rfl
 | cons entry rest ih =>
   have unequal := outside entry (by simp)
   have tail := ih (fun next member => outside next (by simp [member]))
   simp only [mapping,tail,TyTerm.subst]
   simp [substitution,lookup,unequal]

theorem mapping_closed (entries : List (Entry Name)) (safe : SafeOrder entries) (name : Name) :
 ∀ source ∈ typedReads (mapping entries name).ty, ∀ entry ∈ entries, entry.1 ≠ source := by
 induction entries with
 | nil => simp
 | cons head rest ih =>
   obtain ⟨noSelf,distinct,unread,tailSafe⟩ := safe
   intro source present entry member
   change source ∈ typedReads ((mapping rest name).ty.subst (substitution [head])) at present
   rw [typed_subst] at present
   obtain ⟨read,used,found⟩ := List.mem_flatMap.mp present
   by_cases same : head.1 = read
   · subst read
     have rhsRead : source ∈ typedReads head.2 := by simpa [substitution,lookup] using found
     rcases List.mem_cons.mp member with rfl | member
     · intro equal
       exact noSelf (equal ▸ rhsRead)
     · intro equal
       exact unread entry member (equal ▸ rhsRead)
   · have equal : source = read := by simpa [substitution,lookup,same,typedReads] using found
     subst source
     rcases List.mem_cons.mp member with rfl | member
     · exact same
     · exact ih tailSafe read used entry member
theorem type_fixed (entries : List (Entry Name)) (term : TyTerm Name)
 (outside : ∀ source ∈ typedReads term, ∀ entry ∈ entries, entry.1 ≠ source) :
 term.subst (mapping entries) = term := by
 induction term with
 | var name => exact mapping_outside entries name (outside name (by simp [typedReads]))
 | base | bottom | top | emptyRecord | exactEmpty => rfl
 | union first last one two | inter first last one two | pair first last one two
 | record label first last one two | recordDefault label first last one two =>
   have left : ∀ source ∈ typedReads first, ∀ entry ∈ entries, entry.1 ≠ source :=
     fun source member => outside source (List.mem_append_left _ member)
   have right : ∀ source ∈ typedReads last, ∀ entry ∈ entries, entry.1 ≠ source :=
     fun source member => outside source (List.mem_append_right _ member)
   simp only [TyTerm.subst,one left,two right]
 | required label child ih | variant label child ih => simp only [TyTerm.subst,ih outside]
 | arrow first incoming last outgoing one two =>
   have left : ∀ source ∈ typedReads first, ∀ entry ∈ entries, entry.1 ≠ source :=
     fun source member => outside source (List.mem_append_left _ member)
   have right : ∀ source ∈ typedReads last, ∀ entry ∈ entries, entry.1 ≠ source :=
     fun source member => outside source (List.mem_append_right _ member)
   simp only [TyTerm.subst,one left,two right,row_fixed]

theorem type_idempotent (entries : List (Entry Name)) (safe : SafeOrder entries) (term : TyTerm Name) :
 (term.subst (mapping entries)).subst (mapping entries) = term.subst (mapping entries) := by
 apply type_fixed
 rw [typed_subst]
 intro source member entry present
 obtain ⟨name,_,read⟩ := List.mem_flatMap.mp member
 exact mapping_closed entries safe name source read entry present

theorem atom_idempotent (entries : List (Entry Name)) (safe : SafeOrder entries) (atom : Atom Name) :
 atomSubst (mapping entries) (atomSubst (mapping entries) atom) = atomSubst (mapping entries) atom := by
 cases atom <;> simp only [atomSubst,type_idempotent entries safe,row_fixed]

theorem rewrite_idempotent (entries : List (Entry Name)) (safe : SafeOrder entries) (atoms : List (Atom Name)) :
 rewrite entries (rewrite entries atoms) = rewrite entries atoms := by
 simp only [rewrite,List.map_map,Function.comp_def,atom_idempotent entries safe]

theorem type_absorbs (old fresh : List (Entry Name)) (safe : SafeOrder old)
 (within : GeneralPresenceOrderedDependence247.TargetsWithin fresh old) (term : TyTerm Name) :
 (term.subst (mapping old)).subst (mapping fresh) = term.subst (mapping old) := by
 apply type_fixed
 rw [typed_subst]
 intro source member entry present
 obtain ⟨name,_,read⟩ := List.mem_flatMap.mp member
 obtain ⟨original,oldPresent,equal⟩ := within entry present
 rw [← equal]
 exact mapping_closed old safe name source read original oldPresent

theorem atom_absorbs (old fresh : List (Entry Name)) (safe : SafeOrder old)
 (within : GeneralPresenceOrderedDependence247.TargetsWithin fresh old) (atom : Atom Name) :
 atomSubst (mapping fresh) (atomSubst (mapping old) atom) = atomSubst (mapping old) atom := by
 cases atom <;> simp only [atomSubst,type_absorbs old fresh safe within,row_fixed]

theorem rewrite_absorbs (old fresh : List (Entry Name)) (safe : SafeOrder old)
 (within : GeneralPresenceOrderedDependence247.TargetsWithin fresh old) (atoms : List (Atom Name)) :
 rewrite fresh (rewrite old atoms) = rewrite old atoms := by
 simp only [rewrite,List.map_map,Function.comp_def,atom_absorbs old fresh safe within]

end Yulang.GeneralPresenceOrderedSyntax247
