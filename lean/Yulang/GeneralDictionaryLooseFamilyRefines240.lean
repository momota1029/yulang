import Yulang.GeneralDictionaryLooseFamilySnapshot240
set_option backward.isDefEq.respectTransparency false
/-! A uniform source-preserving structural refinement exposes one additional
aggregate lower as a non-point Foo(0,1). This is the exact Refines certificate,
not yet a trusted mixed Refresh certificate or a reachable iteration. -/
namespace Yulang.GeneralDictionaryLooseFamilyRefines240
open GeneralDictionaryLooseFamilyBase240 GeneralDictionaryLooseFamilySnapshot240
open GeneralNominalRefinements
variable (n : Nat) (allocated : List GeneralNominalIdentities.Origin)
 (reserved : List Nat) (ordinary : List (PresenceNormalForm.Atom Nat))
abbrev rootDescriptor : GeneralNominalState.Descriptor ((n+1)+5) := renameDescriptor (embed n) (pair n)
abbrev looseDescriptor : GeneralNominalState.Descriptor ((n+1)+5) :=
 ⟨0,⟨[.type],0⟩,[.type (original (n+1) 0,original (n+1) 1)],rfl⟩
abbrev state : GeneralNominalState.State where
 base := base (n+1)
 view := view (n+1)
 constructors := GeneralDeclarationExamples.constructors
 nominals := fun slot => if slot.val = n+5 then some (looseDescriptor n) else
   if slot.val=3 then some (rootDescriptor n) else
   if slot.val=2 ∨ 4 ≤ slot.val then some (foo (n+1)) else none
 catalogue := by
   intro slot d found
   split at found
   · cases Option.some.inj found; rfl
   · split at found
     · cases Option.some.inj found; rfl
     · split at found
       · cases Option.some.inj found; rfl
       · cases found
 bodies_opaque := by intro _ _ _; rfl
 allocated := allocated
 reserved := reserved
 ordinary := ordinary
 seed := 4

theorem nominals (slot : Fin (n+5)) (descriptor)
 (found : (snapshot n allocated reserved ordinary).nominals slot = some descriptor) :
 (state n allocated reserved ordinary).nominals (embed n slot) = some (renameDescriptor (embed n) descriptor) := by
 have notLast : (embed n slot).val ≠ n+5 := by have := slot.isLt; change slot.val ≠ n+5; omega
 change (if slot.val=3 then some (pair n) else if slot.val=2 ∨ 4 ≤ slot.val then some (foo n) else none) = some descriptor at found
 change (if (embed n slot).val = n+5 then _ else _) = _
 rw [ite_eq_right notLast]
 split at found
 · rename_i three
   cases Option.some.inj found
   simp only [embed,three,ite_true]
 · rename_i notThree
   split at found
   · rename_i supported
     cases Option.some.inj found
     simp only [embed,notThree,supported,ite_false,ite_true]
     rfl
   · cases found

noncomputable def refines : Refines (snapshot n allocated reserved ordinary) (state n allocated reserved ordinary) := by
 refine ⟨?_,?_,?_,?_,?_,?_,?_,rfl,rfl⟩
 · refine ⟨embed n,source_embed n,source_embed n,?_,?_,?_⟩
   · intro atom member
     change atom ∈ GeneralDictionaryLooseLoopSource240.atoms.map (PresenceNormalForm.Atom.rename (original n)) at member
     obtain ⟨old,present,rfl⟩ := List.mem_map.mp member
     simp only [GeneralDictionaryLooseLoopSource240.atoms,GeneralDictionaryLooseLoopSource240.equations,
       List.flatMap_cons,List.flatMap_nil,List.cons_append,List.nil_append,
       GeneralSourceState.equationAtoms,List.mem_cons,List.not_mem_nil,or_false] at present
     rcases present with rfl | rfl | rfl | rfl
     all_goals simp [base,GeneralDictionaryLooseLoopSource240.atoms,GeneralDictionaryLooseLoopSource240.equations,
       GeneralSourceState.equationAtoms,PresenceNormalForm.Atom.rename,Core.PresenceGeneration.TyTerm.rename,original,embed]
   · intro slot known; exact False.elim (known rfl)
   · intro pair member; cases member
 · intro slot term found; cases found
 · exact nominals n allocated reserved ordinary
 · intro atom member; exact member
 · intro identity known
   obtain ⟨slot,same,normalized | ⟨descriptor,found⟩⟩ := known
   · exact False.elim (normalized rfl)
   · exact ⟨embed n slot,(source_embed n slot).trans same,Or.inr
       ⟨renameDescriptor (embed n) descriptor,nominals n allocated reserved ordinary slot descriptor found⟩⟩
 · intro identity member; exact member
 · intro key member; exact member
end Yulang.GeneralDictionaryLooseFamilyRefines240
