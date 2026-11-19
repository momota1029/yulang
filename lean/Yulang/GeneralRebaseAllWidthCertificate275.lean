import Yulang.GeneralRebaseAllWidthRefinement275
import Yulang.GeneralRebaseWidthCertificate275

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 17000
set_option maxHeartbeats 6600000
namespace Yulang.GeneralRebaseAllWidthCertificate275
open Core.PresenceGeneration (TyTerm)
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
open GeneralCanonicalObservations (Recorded Observation)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedMixedObservations233 (Refresh CacheSound Justified justified_sound)
open GeneralDictionaryVersionedSecondInstall233 (installed)
open GeneralDictionaryJournalRefinement228Source (width_two)
open GeneralDictionaryJournalRefinement228Reobserve (pointSnapshot exactCopy point_models_iff)
open GeneralRebaseTerminalMixedRefresh274 (raw widthCandidates)
open GeneralRebaseTerminalTrustedWidth274 (width width_justified)
open GeneralRebaseAllWidthRegistration275
open GeneralRebaseAllWidthRefinement275

noncomputable def context : GeneralNominalCandidates.Context :=
 ⟨snapshot,installed.core.erased.current.context.interpretation⟩

theorem just_width (slot : Fin 8) (known : widthSlot slot) :
 Justified installed (width base slot) := by
 rcases known with rfl|rfl|rfl|rfl
 · exact ⟨[],[],.source,.source,fun m past _ => width_two m past.1⟩
 · exact width_justified _ 5 (by decide +kernel)
 · exact width_justified _ 6 (by decide +kernel)
 · exact width_justified _ 7 (by decide +kernel)

theorem width_atoms (slot : Fin 8) (known : widthSlot slot) (m : Assignment)
 (valid : Models installed m) :
 PresenceNormalForm.All CommonNominalFullCarrier.model (GeneralNominalCommonBridge.assignment base m)
   (GeneralSourceState.equationAtoms slot .emptyRecord) := by
 have size := justified_sound (just_width slot known) valid
 change Equivalent (m (source slot)).1 .emptyRecord at size
 intro atom present
 simp only [GeneralSourceState.equationAtoms,List.mem_cons,List.not_mem_nil,or_false] at present
 rcases present with rfl|rfl
 · exact size.1
 · exact size.2

theorem base_models (m : Assignment) (valid : Models installed m) :
 GeneralNominalCommonBridge.Models base m := by
 have before := valid.1.1.1
 let A := GeneralNominalCommonBridge.assignment base m
 have same : A ∘ embed = GeneralNominalCommonBridge.assignment raw.base m :=
   GeneralNominalRefinements.assignment_transport refines m
 refine ⟨?_,?_,?_⟩
 · change PresenceNormalForm.All CommonNominalFullCarrier.model A atoms
   apply (PresenceNormalForm.all_append ..).mpr
   constructor
   · apply (PresenceNormalForm.all_append ..).mpr
     constructor
     · apply (PresenceNormalForm.all_append ..).mpr
       constructor
       · intro atom present
         have sameAtoms :
             raw.base.ordinary.map (PresenceNormalForm.Atom.rename embed) =
               GeneralSourceState.equationAtoms (0 : Fin 8) (.var 1) ++
               GeneralSourceState.equationAtoms 2 .emptyRecord ++
               GeneralSourceState.equationAtoms 3 .top ++ [.tyLe (.var 4) (.var 2)] := rfl
         rw [← sameAtoms] at present
         obtain ⟨original,member,rfl⟩ := List.mem_map.mp present
         apply (PresenceNormalForm.Atom.holds_rename _ A embed original).mpr
         rw [same]
         exact before.1 _ member
       · exact width_atoms 5 (Or.inr (Or.inl rfl)) m valid
     · exact width_atoms 6 (Or.inr (Or.inr (Or.inl rfl))) m valid
   · exact width_atoms 7 (Or.inr (Or.inr (Or.inr rfl))) m valid
 · intro slot term seen
   have known := head_at slot term seen
   rw [known.2]
   exact justified_sound (just_width slot known.1) valid
 · intro pair present
   cases present

theorem old_nominal (m : Assignment)
 (rawModel : GeneralNominalState.Models pointSnapshot m) (slot : Fin 5)
 (whereAt : slot = 0 ∨ slot = 1) :
 GeneralNominalState.Denotes base m (embed slot) descriptor := by
 have found : pointSnapshot.nominals slot = some exactCopy := ite_eq_left whereAt
 obtain ⟨values,fits,equal⟩ := rawModel.2.1 _ _ found
 exact ⟨values,GeneralRebaseWidthCertificate275.fits_forward refines m _ _ fits,by simpa only [source_embed,descriptor,GeneralNominalRefinements.renameDescriptor] using equal⟩

theorem cache : CacheSound installed snapshot := by
 intro observation given
 cases given with
 | scalar slot scalar seen =>
   change Fin 8 at slot
   change viewHeads slot = .scalar scalar at seen
   have term := view_at slot (.base scalar) (by rw [seen]; rfl)
   cases term.2
 | structural slot kind children seen =>
   change Fin 8 at slot
   change Fin 1 at kind
   change viewHeads slot = .structural kind children at seen
   have term := view_at slot ((viewShapes kind).term children) (by rw [seen]; rfl)
   exact term.2 ▸ just_width slot term.1
 | nominal slot d seen =>
   obtain ⟨whereAt,rfl⟩ := nominal_at slot d seen
   refine ⟨[],[],.source,.source,?_⟩
   intro m previous _
   rcases whereAt with rfl|rfl
   · exact old_nominal m ((point_models_iff m).mpr previous.1) 0 (Or.inl rfl)
   · exact old_nominal m ((point_models_iff m).mpr previous.1) 1 (Or.inr rfl)

noncomputable def certificate : Refresh installed (context) where
 refines := refines
 interpretation := rfl
 support := support
 constraints := fun m valid => ⟨base_models m valid,valid.1.1.2.2⟩
 cache := cache

end Yulang.GeneralRebaseAllWidthCertificate275
