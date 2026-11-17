import Yulang.GeneralDictionaryVersionLoopSecondFull238
import Yulang.GeneralDictionaryVersionLoopSecondFrame238
import Yulang.GeneralNominalVersionedJournalFrame236
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
namespace Yulang.GeneralDictionaryVersionLoopSecondNovel238
open GeneralDictionaryVersionLoopSource237
open GeneralDictionaryVersionLoopRetarget237 (retargeted retargeted_model)
open GeneralDictionaryVersionLoopSecondPacket238 (packet plan lo hi)
open GeneralDictionaryVersionLoopPacket237 (actual actual_value)
open GeneralNominalVersionedJournal232
open CommonNominalFullCarrier

theorem fresh_upper : hi ∉ GeneralNominalVersionedJournalFrame236.sources retargeted := by
 change hi ∉ (GeneralDictionaryDefaultJournalSupport213.journalSources retargeted.legacy ++
   [GeneralDictionaryVersionLoopPacket237.plan].flatMap GeneralNominalVersionedPacketFrame236.sources ++
   [GeneralDictionaryVersionLoopFrame237.effect].flatMap (GeneralNominalVersionedJournalFrame236.effectSources retargeted))
 simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,
   GeneralNominalVersionedJournalFrame236.effectSources,GeneralDictionaryDefault214ActualBodyFrame.classSources]
 change hi ∉ (GeneralDictionaryDefaultJournalSupport213.journalSources retargeted.legacy ++
   GeneralNominalVersionedPacketFrame236.sources GeneralDictionaryVersionLoopPacket237.plan ++
   ((GeneralNominalVersionedPacketFrame236.headSources GeneralDictionaryVersionLoopPacket237.packet ++
   (GeneralNominalCenteredHeadOutputs.requests initial.core root).flatMap _) ++
   (GeneralNominalCenteredHeadOutputs.requests retargeted.core root).flatMap _))
 rw [GeneralDictionaryVersionLoopFrame237.requests_empty,GeneralDictionaryVersionLoopSecondFrame238.requests_empty]
 simp only [List.flatMap_nil,List.append_nil]
 decide +kernel

noncomputable def bad : GeneralNominalCommonBridge.Assignment :=
 fun name => if name = hi then (.bottom,(model name).2) else model name

theorem preserved : Models retargeted bad := by
 apply (GeneralNominalVersionedJournalFrame236.models_iff retargeted ?_).mp retargeted_model
 intro name member
 have different : name ≠ hi := by intro equal; subst name; exact fresh_upper member
 simp only [bad,different,ite_false]

theorem novel : ¬ GeneralNominalVersionedKernel232.Committed retargeted plan := by
 intro committed
 have valid := (committed.1 bad preserved).1
 have fits := GeneralNominalVersionedPlans231.shared_center valid.2.1 (name := 0) (Or.inl (by decide +kernel))
 rw [GeneralNominalVersionedFrame231.binder_eq,GeneralDictionaryVersionLoopSecondFull238.binder_exact] at fits
 change GeneralNominalCaptureMerges.Fits bad ((GeneralNominalVersionedAllocation231.capture _ _ _ _ packet.bindings).inputs 0) (bad actual).1 at fits
 rw [GeneralDictionaryVersionLoopNext237.bindings_exact] at fits
 change Subtype (bad lo).1 (bad actual).1 ∧ Subtype (bad actual).1 (bad hi).1 at fits
 have ne : actual ≠ hi := Ne.symm (GeneralNominalAggregateVersion231.not_legacy_slot 3 0 0 1 0 _ 0 0 8 0)
 have center : (bad actual).1 = F := by simp only [bad,ne,ite_false,actual_value]
 have upper : (bad hi).1 = .bottom := by simp only [bad,ite_true]
 rw [center,upper] at fits
 exact GeneralNominalCenteredHeadMatHeadShape.bottom_no_head (.nominal 0 1)
   ⟨[.inl S],rfl,(by
     intro depth
     apply (CommonNominalFullDemand.producerLe_iff_probe _ _).mpr
     intro rank env observation accepted
     exact CommonNominalFullDemand.probeAt_bottom rank observation),fits.2⟩
end Yulang.GeneralDictionaryVersionLoopSecondNovel238
