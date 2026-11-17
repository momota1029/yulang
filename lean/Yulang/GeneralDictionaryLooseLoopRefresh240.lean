import Yulang.GeneralDictionaryLooseLoopRefreshBase240
import Yulang.GeneralNominalVersionedAggregateEntries236
import Yulang.GeneralNominalVersionedMixedObservations233
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryLooseLoopRefresh240
open GeneralDictionaryLooseLoopSource240
open GeneralDictionaryLooseLoopPacket240 (packet plan lo bindings_exact)
open GeneralDictionaryLooseLoopFrame240 (installed input_trusted)
open GeneralDictionaryLooseLoopRefreshBase240
open GeneralNominalVersionedSupport233
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)

theorem raw_zero_one (m : Assignment) (valid : GeneralNominalState.Models snapshot m) :
 Equivalent (m 0).1 (m 1).1 := by
 have zero : Equivalent (m 0).1 S := ⟨valid.1.1 (.tyLe (.var 0) (.base .int)) (by decide +kernel),valid.1.1 (.tyLe (.base .int) (.var 0)) (by decide +kernel)⟩
 have one : Equivalent (m 1).1 S := ⟨valid.1.1 (.tyLe (.var 1) (.base .int)) (by decide +kernel),valid.1.1 (.tyLe (.base .int) (.var 1)) (by decide +kernel)⟩
 exact ⟨subtype_trans zero.1 one.2,subtype_trans one.1 zero.2⟩

theorem lower_equal (m : Assignment) (valid : SliceModels installed [.input plan] m) :
 Equivalent (m lo).1 (m 2).1 := by
 have input := valid.2.2 (.input plan) (List.mem_singleton_self _)
 have merges := input.1.2.1
 have equation := (GeneralNominalVersionedAggregateEntries236.holds_iff snapshot registry 0 declaration packet.bindings m).mp merges
     (lo,Core.PresenceGeneration.TyTerm.union (.var 2) (.var 2)) (by decide +kernel)
 have equal := (GeneralNominalCaptureMerges.equations_exact ..).mp equation
 change Equivalent (m lo).1 (.union (m 2).1 (m 2).1) at equal
 have union : Equivalent (.union (m 2).1 (m 2).1) (m 2).1 :=
   ⟨(common_union_is_join _ _ _).mpr ⟨subtype_refl _,subtype_refl _⟩,
     (common_union_is_join _ _ _).mp (subtype_refl _) |>.1⟩
 exact ⟨subtype_trans equal.1 union.1,subtype_trans union.2 equal.2⟩

theorem lower_nominal (m : Assignment) (valid : SliceModels installed [.input plan] m) :
 ∃ values, GeneralNominalState.FitsAll extendedBase m loose.arguments values ∧
   Equivalent (m lo).1 (nominal 0 values) := by
 have sourceValid : GeneralNominalState.Models snapshot m := valid.1
 have scalar := raw_zero_one m sourceValid
 have lower := lower_equal m valid
 obtain ⟨values,fits,equal⟩ := sourceValid.2.1 2 foo rfl
 change GeneralNominalState.FitsAll base m [.type (0,0)] values at fits
 cases fits with
 | @cons _ a _ rest one tail =>
   cases tail
   cases a with
   | inr => cases one
   | inl a =>
     refine ⟨[.inl a],.cons ?_ .nil,?_⟩
     · exact ⟨one.1,subtype_trans one.2 scalar.1⟩
     · exact ⟨subtype_trans lower.1 equal.1,subtype_trans equal.2 lower.2⟩

theorem lower_supported : lo ∈ GeneralNominalState.sources installed.core.erased.current.context.state := by
 apply List.mem_append_left
 apply List.mem_append_right
 change lo ∈ GeneralNominalVersionedInstallation231.reserved packet
 change lo ∈ GeneralNominalVersionedAllocation231.reserved snapshot registry 0 packet.bindings
 simpa only [bindings_exact] using (GeneralNominalVersionedAllocation231.aggregate_reserved (registry := registry) (state := snapshot) (root := 0) (bindings := packet.bindings) (by exact List.mem_singleton_self declaration)
   (by decide +kernel : 0 ∈ declaration.inputNames)).1

theorem move_fits (m : Assignment) (parameters : List (GeneralNominalState.Parameter base.slots)) (values : List CommonNominalFullCarrier.Argument)
 (fits : GeneralNominalState.FitsAll base m parameters values) :
 GeneralNominalState.FitsAll extendedBase m (parameters.map (GeneralNominalRefinements.renameParameter embed)) values := by
 induction parameters generalizing values with
 | nil => cases fits; exact .nil
 | cons parameter rest ih =>
   cases fits with
   | cons head tail => exact .cons ((GeneralNominalRefinements.fits_transport refines m _ _).mpr head) (ih _ tail)

noncomputable def certificate : GeneralNominalVersionedObservations233.Refresh installed extendedContext where
 refines := refines
 interpretation := rfl
 support := by
   intro identity member
   simp only [GeneralNominalState.sources,List.mem_append] at member ⊢
   rcases member with ((type | row) | reserved) | ordinary
   · obtain ⟨slot,rfl⟩ := List.mem_ofFn.mp type
     by_cases old : slot.val < 5
     · exact Or.inl (Or.inl (Or.inl (List.mem_ofFn.mpr ⟨⟨slot.val,old⟩,by change slot.val = source slot; simp [GeneralDictionaryLooseLoopRefreshBase240.source,old]⟩)))
     · simpa only [GeneralNominalState.sources,List.mem_append,GeneralDictionaryLooseLoopRefreshBase240.source,old,ite_false] using lower_supported
   · obtain ⟨slot,rfl⟩ := List.mem_ofFn.mp row
     by_cases old : slot.val < 5
     · exact Or.inl (Or.inl (Or.inr (List.mem_ofFn.mpr ⟨⟨slot.val,old⟩,by change slot.val = source slot; simp [GeneralDictionaryLooseLoopRefreshBase240.source,old]⟩)))
     · simpa only [GeneralNominalState.sources,List.mem_append,GeneralDictionaryLooseLoopRefreshBase240.source,old,ite_false] using lower_supported
   · exact Or.inl (Or.inr reserved)
   · exact Or.inr ordinary
 constraints := by
   intro m valid
   refine ⟨And.intro ?_ (And.intro (by intro _ _ h; cases h) (by intro _ h; cases h)),valid.1.1.2.2⟩
   rw [PresenceNormalForm.all_rename,assignment_transport]
   exact valid.1.1.1.1
 cache := by
   intro observation recorded
   cases recorded with
   | scalar slot scalar found => cases found
   | structural slot kind children found => cases found
   | nominal slot d found =>
     change (if slot = 2 then some fooOld else if slot = 3 then some pairOld else if slot = 4 then some fooOld else if slot = 5 then some loose else none) = some d at found
     split at found
     · rename_i same; subst slot; cases Option.some.inj found
       refine ⟨[],.source,?_⟩
       intro m valid
       obtain ⟨values,fits,equal⟩ := (show GeneralNominalState.Models snapshot m from valid.1).2.1 2 foo rfl
       exact ⟨values,move_fits m _ _ fits,equal⟩
     · split at found
       · rename_i same; subst slot; cases Option.some.inj found
         refine ⟨[],.source,?_⟩
         intro m valid
         obtain ⟨values,fits,equal⟩ := (show GeneralNominalState.Models snapshot m from valid.1).2.1 3 pair rfl
         exact ⟨values,move_fits m _ _ fits,equal⟩
       · split at found
         · rename_i same; subst slot; cases Option.some.inj found
           refine ⟨[],.source,?_⟩
           intro m valid
           obtain ⟨values,fits,equal⟩ := (show GeneralNominalState.Models snapshot m from valid.1).2.1 4 foo rfl
           exact ⟨values,move_fits m _ _ fits,equal⟩
         · split at found
           · rename_i same; subst slot; cases Option.some.inj found
             exact ⟨[.input plan],input_trusted,lower_nominal⟩
           · cases found

theorem lower_unknown : ¬ GeneralNominalState.Known installed.core.erased.current.context.state lo := by
 rintro ⟨slot,same,_⟩
 change Fin 5 at slot
 change slot.val = lo at same
 have high := lo_large
 omega

theorem lower_known : GeneralNominalState.Known extendedContext.state lo :=
 ⟨(5 : Fin 6),rfl,Or.inr ⟨loose,rfl⟩⟩
end Yulang.GeneralDictionaryLooseLoopRefresh240
