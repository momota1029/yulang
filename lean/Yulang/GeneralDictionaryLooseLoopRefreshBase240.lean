import Yulang.GeneralDictionaryLooseLoopFrame240
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryLooseLoopRefreshBase240
open GeneralDictionaryLooseLoopSource240
open GeneralDictionaryLooseLoopPacket240 (lo)
open GeneralDictionaryLooseLoopFrame240 (installed)
abbrev embed (slot : Fin 5) : Fin 6 := ⟨slot.val,Nat.lt_succ_of_lt slot.isLt⟩
def source (slot : Fin 6) : Nat := if slot.val < 5 then slot.val else lo

theorem lo_large : 4 < lo := GeneralNominalAggregateVersion231.above_seed ..
theorem source_embed (slot : Fin 5) : source (embed slot) = slot.val := by simp only [source,slot.isLt,ite_true]
theorem source_injective : Function.Injective source := by
 intro a b equal
 by_cases first : a.val < 5
 · by_cases last : b.val < 5
   · exact Fin.ext (by simpa only [source,first,last,ite_true] using equal)
   · have same : a.val = lo := by simpa only [source,first,last,ite_true,ite_false] using equal
     have large := lo_large; omega
 · by_cases last : b.val < 5
   · have same : lo = b.val := by simpa only [source,first,last,ite_true,ite_false] using equal
     have large := lo_large; omega
   · have one := a.isLt; have two := b.isLt
     apply Fin.ext; omega
abbrev extendedBase : GeneralSourceState.State where
 slots := 6
 source := source
 source_injective := source_injective
 rowSource := source
 ordinary := base.ordinary.map (PresenceNormalForm.Atom.rename embed)
 kinds := 0
 shapes := Fin.elim0
 shapes_injective := by intro i; exact Fin.elim0 i
 heads := fun _ => .unresolved
 intervals := []
 heads_sound := by intro _ _ _ _ h; cases h
 intervals_sound := by intro _ _ _ h; cases h
abbrev extendedView : GeneralNormalizedObservation.Snapshot extendedBase where
 kinds := 0
 shapes := Fin.elim0
 shapes_injective := by intro i; exact Fin.elim0 i
 canonical := by intro i; exact Fin.elim0 i
 heads := fun _ => .deferred .unresolved
 checked := by intro _ _ h; cases h
abbrev fooOld : GeneralNominalState.Descriptor 6 := GeneralNominalRefinements.renameDescriptor embed foo
abbrev pairOld : GeneralNominalState.Descriptor 6 := GeneralNominalRefinements.renameDescriptor embed pair
abbrev loose : GeneralNominalState.Descriptor 6 := ⟨0,⟨[.type],0⟩,[.type (0,1)],rfl⟩
noncomputable abbrev extendedSnapshot : GeneralNominalState.State where
 base := extendedBase
 view := extendedView
 constructors := GeneralDeclarationExamples.constructors
 nominals := fun slot => if slot = 2 then some fooOld else if slot = 3 then some pairOld else if slot = 4 then some fooOld else if slot = 5 then some loose else none
 catalogue := by
   intro slot d found
   split at found
   · cases Option.some.inj found; rfl
   · split at found
     · cases Option.some.inj found; rfl
     · split at found
       · cases Option.some.inj found; rfl
       · split at found
         · cases Option.some.inj found; rfl
         · cases found
 bodies_opaque := by intro _ _ _; rfl
 allocated := installed.core.erased.current.context.state.allocated
 reserved := installed.core.erased.current.context.state.reserved
 ordinary := installed.core.erased.current.context.state.ordinary
 seed := 4
noncomputable abbrev extendedContext : GeneralNominalCandidates.Context := ⟨extendedSnapshot,interpretation⟩
noncomputable def refines : GeneralNominalRefinements.Refines installed.core.erased.current.context.state extendedSnapshot := by
 refine ⟨?_,?_,?_,?_,?_,?_,?_,rfl,rfl⟩
 · refine ⟨embed,source_embed,source_embed,?_,?_,?_⟩
   · intro atom member; exact List.mem_map.mpr ⟨atom,member,rfl⟩
   · intro slot known; exact False.elim (known rfl)
   · intro pair member; cases member
 · intro slot term found; cases found
 · intro slot d found
   change Fin 5 at slot
   change (if slot = 2 then some foo else if slot = 3 then some pair else if slot = 4 then some foo else none) = some d at found
   split at found
   · rename_i same; subst slot; cases Option.some.inj found; rfl
   · split at found
     · rename_i same; subst slot; cases Option.some.inj found; rfl
     · split at found
       · rename_i same; subst slot; cases Option.some.inj found; rfl
       · cases found
 · intro atom member; exact member
 · intro identity known
   obtain ⟨slot,same,normalized | ⟨d,nominal⟩⟩ := known
   · exact False.elim (normalized rfl)
   · change Fin 5 at slot
     refine ⟨embed slot,(source_embed slot).trans same,Or.inr ?_⟩
     change (if slot = 2 then some foo else if slot = 3 then some pair else if slot = 4 then some foo else none) = some d at nominal
     split at nominal
     · rename_i same; subst slot; exact ⟨fooOld,rfl⟩
     · split at nominal
       · rename_i same; subst slot; exact ⟨pairOld,rfl⟩
       · split at nominal
         · rename_i same; subst slot; exact ⟨fooOld,rfl⟩
         · cases nominal
 · intro identity member; exact member
 · intro key member; exact member

theorem assignment_transport (m : GeneralNominalCommonBridge.Assignment) :
 GeneralNominalCommonBridge.assignment extendedBase m ∘ embed = GeneralNominalCommonBridge.assignment base m := by
 funext slot
 change ((m (source (embed slot))).1,(m (source (embed slot))).2) = ((m slot.val).1,(m slot.val).2)
 rw [source_embed]
end Yulang.GeneralDictionaryLooseLoopRefreshBase240
