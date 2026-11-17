import Yulang.GeneralNominalPointKernel240
import Yulang.GeneralDictionaryLooseLoopRefresh240
import Yulang.GeneralDictionaryLooseLoopFull240
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryLooseLoopRetarget240
open GeneralDictionaryLooseLoopSource240
open GeneralDictionaryLooseLoopPacket240 (lo plan)
open GeneralDictionaryLooseLoopFrame240 (installed)
open GeneralDictionaryLooseLoopRefreshBase240
open GeneralDictionaryLooseLoopRefresh240
open GeneralNominalVersionedSupport233 CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
noncomputable abbrev refreshed := GeneralNominalVersionedRefresh232.refresh installed extendedContext
abbrev exactFoo : GeneralNominalState.Descriptor 6 := ⟨0,⟨[.type],0⟩,[.type (0,0)],rfl⟩
abbrev retarget : GeneralNominalState.Descriptor 6 := ⟨5,⟨[.type,.type],5⟩,[.type (5,4),.type (5,4)],rfl⟩
noncomputable def revision : GeneralNominalReobservationSteps.Revision refreshed.core.erased.current where
 entries := fun (slot : Fin 6) => if slot = 2 then some fooOld else if slot = 3 then some retarget else if slot = 4 then some fooOld else if slot = 5 then some exactFoo else none
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
 opaqueHeads := by intro _ _ _; rfl
 domain := by
   intro slot
   change Fin 6 at slot
   change (if slot = 2 then some fooOld else if slot = 3 then some retarget else if slot = 4 then some fooOld else if slot = 5 then some exactFoo else none) = none ↔
     (if slot = 2 then some fooOld else if slot = 3 then some pairOld else if slot = 4 then some fooOld else if slot = 5 then some loose else none) = none
   by_cases a : slot=2 <;> by_cases b : slot=3 <;> by_cases c : slot=4 <;> by_cases d : slot=5 <;> simp [a,b,c,d]

theorem raw_equal (m : Assignment) (valid : GeneralNominalState.Models revision.snapshot m) :
 Equivalent (m lo).1 (m 2).1 ∧ Equivalent (m 0).1 (m 1).1 := by
 have lower : Equivalent (m lo).1 (.union (m 2).1 (m 2).1) :=
  ⟨valid.2.2 (.tyLe (.var lo) (.union (.var 2) (.var 2))) (by decide +kernel),
   valid.2.2 (.tyLe (.union (.var 2) (.var 2)) (.var lo)) (by decide +kernel)⟩
 have union : Equivalent (.union (m 2).1 (m 2).1) (m 2).1 :=
  ⟨(common_union_is_join _ _ _).mpr ⟨subtype_refl _,subtype_refl _⟩,
    (common_union_is_join _ _ _).mp (subtype_refl _) |>.1⟩
 have zero : Equivalent (m 0).1 S :=
  ⟨valid.1.1 (.tyLe (.var (0 : Fin 6)) (.base .int)) (by decide +kernel),valid.1.1 (.tyLe (.base .int) (.var (0 : Fin 6))) (by decide +kernel)⟩
 have one : Equivalent (m 1).1 S :=
  ⟨valid.1.1 (.tyLe (.var (1 : Fin 6)) (.base .int)) (by decide +kernel),valid.1.1 (.tyLe (.base .int) (.var (1 : Fin 6))) (by decide +kernel)⟩
 exact ⟨⟨subtype_trans lower.1 union.1,subtype_trans union.2 lower.2⟩,
   ⟨subtype_trans zero.1 one.2,subtype_trans one.1 zero.2⟩⟩

theorem point_fit_change (m : Assignment) (a b : Fin 6) (value : Argument)
 (equal : Equivalent (m (source a)).1 (m (source b)).1)
 (fits : GeneralNominalState.Fits extendedBase m (.type (a,4)) value) :
 GeneralNominalState.Fits extendedBase m (.type (b,4)) value := by
 cases value with
 | inr => cases fits
 | inl value => exact ⟨subtype_trans equal.2 fits.1,fits.2⟩

theorem pair_fits (m : Assignment) (a b : Fin 6) (values : List Argument)
 (equal : Equivalent (m (source a)).1 (m (source b)).1)
 (fits : GeneralNominalState.FitsAll extendedBase m [.type (a,4),.type (a,4)] values) :
 GeneralNominalState.FitsAll extendedBase m [.type (b,4),.type (b,4)] values := by
 cases fits with
 | cons one tail =>
   cases tail with
   | cons two tail =>
     cases tail
     exact .cons (point_fit_change m a b _ equal one) (.cons (point_fit_change m a b _ equal two) .nil)

theorem raw_back (m : Assignment) (valid : GeneralNominalState.Models revision.snapshot m) :
 GeneralNominalState.Models extendedSnapshot m := by
 have equal := raw_equal m valid
 refine ⟨valid.1,?_,valid.2.2⟩
 intro slot d found
 change (if slot=2 then some fooOld else if slot=3 then some pairOld else if slot=4 then some fooOld else if slot=5 then some loose else none) = some d at found
 split at found
 · rename_i same; subst slot; cases Option.some.inj found
   exact valid.2.1 (2 : Fin 6) fooOld rfl
 · split at found
   · rename_i same; subst slot; cases Option.some.inj found
     obtain ⟨values,fits,meaning⟩ := valid.2.1 (3 : Fin 6) retarget rfl
     exact ⟨values,pair_fits m 5 2 values equal.1 fits,meaning⟩
   · split at found
     · rename_i same; subst slot; cases Option.some.inj found
       exact valid.2.1 (4 : Fin 6) fooOld rfl
     · split at found
       · rename_i same; subst slot; cases Option.some.inj found
         obtain ⟨values,fits,meaning⟩ := valid.2.1 (5 : Fin 6) exactFoo rfl
         change GeneralNominalState.FitsAll extendedBase m [.type (0,0)] values at fits
         cases fits with
         | @cons _ a _ rest one tail =>
           cases tail
           cases a with
           | inl a => exact ⟨[.inl a],.cons ⟨one.1,subtype_trans one.2 equal.2.1⟩ .nil,meaning⟩
           | inr => cases one
       · cases found

theorem input_trusted : Trusted refreshed [.input plan] := by
 apply Trusted.input plan .source List.mem_cons_self
 intro slot member test observation head assignment valid
 exact GeneralCanonicalObservations.recorded_sound _ _ valid.1 (GeneralNominalSupport.head_recorded head)

theorem preserves : GeneralNominalPointRevision240.Preserves revision := by
 intro slot descriptor found point
 change Fin 6 at slot
 change (if slot=2 then some fooOld else if slot=3 then some pairOld else if slot=4 then some fooOld else if slot=5 then some loose else none)=some descriptor at found
 split at found
 · rename_i same; subst slot; cases Option.some.inj found; rfl
 · split at found
   · rename_i same; subst slot; cases Option.some.inj found
     have impossible := point (.type ((2 : Fin 6),(4 : Fin 6))) (List.mem_cons_self)
     cases impossible
   · split at found
     · rename_i same; subst slot; cases Option.some.inj found; rfl
     · split at found
       · rename_i same; subst slot; cases Option.some.inj found
         have impossible := point (.type ((0 : Fin 6),(1 : Fin 6))) (List.mem_singleton_self _)
         cases impossible
       · cases found

theorem improved : GeneralNominalReobservationSteps.Improves revision := by
 refine ⟨fun slot point => GeneralNominalPointRevision240.point_retained preserves point,?_⟩
 refine ⟨(5 : Fin 6),?_,exactFoo,rfl,by intro p present; cases List.mem_singleton.mp present; rfl⟩
 rintro ⟨d,found,point⟩
 have same : d = loose := Option.some.inj found.symm
 subst d
 have impossible := point (.type ((0 : Fin 6),(1 : Fin 6))) (List.mem_singleton_self _)
 cases impossible

theorem certificate : GeneralNominalVersionedMixedObservations233.Reobserve refreshed revision := by
 refine ⟨raw_back,?_⟩
 apply GeneralNominalVersionedMixedObservations233.versioned_cache
 intro observation recorded
 cases recorded with
 | scalar slot scalar found => cases found
 | structural slot kind children found => cases found
 | nominal slot d found =>
   change Fin 6 at slot
   change (if slot=2 then some fooOld else if slot=3 then some retarget else if slot=4 then some fooOld else if slot=5 then some exactFoo else none) = some d at found
   split at found
   · rename_i same; subst slot; cases Option.some.inj found
     refine ⟨[],.source,?_⟩
     intro m valid
     obtain ⟨values,fits,equal⟩ := (show GeneralNominalState.Models snapshot m from valid.1).2.1 2 foo rfl
     exact ⟨values,move_fits m _ _ fits,equal⟩
   · split at found
     · rename_i same; subst slot; cases Option.some.inj found
       refine ⟨[.input plan],input_trusted,?_⟩
       intro m valid
       have low := lower_equal m (show SliceModels installed [.input plan] m from valid)
       obtain ⟨values,fits,equal⟩ := (show GeneralNominalState.Models snapshot m from valid.1).2.1 3 pair rfl
       exact ⟨values,pair_fits m 2 5 values ⟨low.2,low.1⟩ (move_fits m _ _ fits),equal⟩
     · split at found
       · rename_i same; subst slot; cases Option.some.inj found
         refine ⟨[],.source,?_⟩
         intro m valid
         obtain ⟨values,fits,equal⟩ := (show GeneralNominalState.Models snapshot m from valid.1).2.1 4 foo rfl
         exact ⟨values,move_fits m _ _ fits,equal⟩
       · split at found
         · rename_i same; subst slot; cases Option.some.inj found
           refine ⟨[.input plan],input_trusted,?_⟩
           intro m valid
           have low := lower_equal m (show SliceModels installed [.input plan] m from valid)
           obtain ⟨values,fits,equal⟩ := (show GeneralNominalState.Models snapshot m from valid.1).2.1 2 foo rfl
           exact ⟨values,move_fits m _ _ fits,⟨subtype_trans low.1 equal.1,subtype_trans equal.2 low.2⟩⟩
         · cases found

noncomputable abbrev retargeted := GeneralNominalVersionedRefresh232.reobserve refreshed revision

theorem refreshed_model : GeneralNominalVersionedJournal232.Models refreshed model :=
 (GeneralNominalVersionedObservationTransport233.refresh_models GeneralDictionaryLooseLoopRefresh240.certificate).mpr
   GeneralDictionaryLooseLoopFull240.installed_model

theorem retargeted_model : GeneralNominalVersionedJournal232.Models retargeted model :=
 (GeneralNominalVersionedMixedObservations233.reobserve_models certificate).mpr refreshed_model

theorem refresh_step : GeneralNominalPointKernel240.Step registry root installed refreshed :=
 ⟨root,.root,.refresh root extendedContext
   (GeneralNominalVersionedMixedObservations233.of_versioned_refresh GeneralDictionaryLooseLoopRefresh240.certificate)
   lo lower_supported lower_unknown lower_known⟩

theorem retarget_step : GeneralNominalPointKernel240.Step registry root refreshed retargeted :=
 ⟨root,.root,.administrative (.reobserve root revision certificate improved preserves)⟩

/-- Two real mixed steps from this nonempty installed journal. The missing
initial installation guard/source path is NOT supplied by this theorem. -/
theorem local_steps : B4Target.Steps (GeneralNominalPointKernel240.Step registry root) installed retargeted :=
 .tail (.tail .refl refresh_step) retarget_step
end Yulang.GeneralDictionaryLooseLoopRetarget240
