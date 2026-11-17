import Yulang.GeneralDictionaryVersionLoopSafety238
import Yulang.GeneralNominalVersionedMixedKernel234
import Yulang.GeneralDictionaryDefaultRawSupport213
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryVersionLoopInstall238
open GeneralDictionaryVersionLoopSource237 GeneralDictionaryVersionLoopPacket237
open GeneralDictionaryVersionLoopFrame237 GeneralDictionaryVersionLoopFull237
open GeneralDictionaryVersionLoopSafety238 GeneralDictionaryVersionLoopInitial238
open GeneralNominalVersionedMixedKernel234
open CommonNominalFullCarrier

theorem frame_plan {candidate : GeneralNominalCenters.Plan roles} {key}
 (framed : GeneralNominalVersionedEvidence231.Frame registry initial.core root key candidate) : candidate = plan := by
 rcases candidate with ⟨⟨reg,ctx,site,decl,check,bounds⟩,input,inputEq⟩
 have regEq : reg = registry := framed.registry_eq
 have ctxEq : ctx = context := framed.context_eq
 have declEq : decl = declaration := List.mem_singleton.mp framed.visible
 have siteEq : site = GeneralNominalDemandMerging.pointSite root := List.mem_singleton.mp framed.raw_recorded
 have inputSame : input = GeneralNominalCenters.rootSite snapshot.seed root := List.mem_singleton.mp framed.center_recorded
 subst reg; subst ctx; subst decl; subst site; subst input
 have boundsEq : [(3,3)] = bounds := Option.some.inj framed.located
 subst bounds; rfl

theorem positions : GeneralNominalVersionedCycles232.Safe initial plan :=
 ⟨by decide +kernel,fun entry _ => acyclic entry.1⟩
theorem installable : Installable registry initial effect := by
 refine ⟨rfl,rfl,safe,?_,?_,?_,positions,?_,model,installation_models⟩
 · exact GeneralNominalVersionedMixedObservations233.legacy_cache
     (GeneralDictionaryDefaultCache208.initial_valid context root)
 · change (GeneralNominalVersionedPlans231.emittedSchema plan).unknown = false
   rw [emitted_empty]
 · intro packet member; cases member
 · intro candidate input framed
   change GeneralNominalVersionedEvidence231.Frame registry initial.core root candidate.packet.declaration.id candidate at framed
   cases frame_plan framed
   exact positions

noncomputable def bad : GeneralNominalCommonBridge.Assignment :=
 fun name => if name = actual then (.bottom,Common.rowEmpty) else model name

theorem bad_small (name : Nat) (small : name ≤ 3) : bad name = model name := by
 have big := GeneralNominalIdentities.source_above_seed 3 (0,0,8,0,0)
 have different : name ≠ actual := by change name ≠ GeneralNominalIdentities.source 3 (0,0,8,0,0); omega
 simp [bad,different]
theorem bad_raw : GeneralNominalState.Models snapshot bad := by
 apply (GeneralDictionaryDefaultRawSupport213.models_iff snapshot ?_).mp source_model
 intro name member
 apply (bad_small name ?_).symm
 have := source.below_seed name (GeneralDictionaryDefaultRawSupport213.subset snapshot member)
 exact this

theorem bad_initial : GeneralNominalVersionedJournal232.Models initial bad :=
 (GeneralNominalVersionedJournal232.initial_models context root bad).mpr
   ⟨bad_raw,fun _ => ⟨subtype_refl _,subtype_refl _⟩⟩
theorem novel : ¬ Committed initial plan := by
 intro committed
 have valid := (committed.1 bad bad_initial).1
 have fits := GeneralNominalVersionedPlans231.shared_center valid.2.1 (name := 0) (Or.inl (by decide +kernel))
 rw [GeneralNominalVersionedFrame231.binder_eq,binder_exact] at fits
 change GeneralNominalCaptureMerges.Fits bad ((GeneralNominalVersionedAllocation231.capture _ _ _ _ packet.bindings).inputs 0) (bad actual).1 at fits
 rw [bindings_exact] at fits
 change Subtype (bad lo).1 (bad actual).1 ∧ Subtype (bad actual).1 (bad hi).1 at fits
 have ne : lo ≠ actual := GeneralNominalAggregateVersion231.not_legacy_slot 3 0 0 0 0 _ 0 0 8 0
 have lower : (bad lo).1 = F := by simp [bad,ne,lower_value]
 have center : (bad actual).1 = .bottom := by simp [bad]
 rw [lower,center] at fits
 exact GeneralNominalCenteredHeadMatHeadShape.bottom_no_head (.nominal 0 1)
   ⟨[.inl S],rfl,(by
     intro depth
     apply (CommonNominalFullDemand.producerLe_iff_probe _ _).mpr
     intro rank env observation accepted
     exact CommonNominalFullDemand.probeAt_bottom rank observation),fits.1⟩
theorem step : Step registry root initial installed := ⟨root,.root,.install effect installable novel⟩
theorem reachable_installed : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) sourceRegistry root installed :=
 ⟨initial,initial_source,.tail .refl step⟩
end Yulang.GeneralDictionaryVersionLoopInstall238
