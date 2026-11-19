import Yulang.GeneralRebaseWidthRefinement275

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 17000
set_option maxHeartbeats 6600000
namespace Yulang.GeneralRebaseWidthCertificate275
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
open GeneralRebaseWidthRegistration275
open GeneralRebaseWidthRefinement275

noncomputable def context (id : Nat) (tracked : id ∈ widthCandidates) : GeneralNominalCandidates.Context :=
 ⟨snapshot id tracked,installed.core.erased.current.context.interpretation⟩

theorem just_width (id : Nat) (tracked : id ∈ widthCandidates) (slot : Fin 6) (known : widthSlot slot) :
 Justified installed (width (base id (large id tracked)) slot) := by
 rcases known with rfl|rfl
 · exact ⟨[],[],.source,.source,fun m past _ => width_two m past.1⟩
 · exact width_justified _ 5 tracked

theorem base_models (id : Nat) (tracked : id ∈ widthCandidates) (m : Assignment) (valid : Models installed m) :
 GeneralNominalCommonBridge.Models (base id (large id tracked)) m := by
 have before := valid.1.1.1
 let A := GeneralNominalCommonBridge.assignment (base id (large id tracked)) m
 have same : A ∘ embed = GeneralNominalCommonBridge.assignment raw.base m :=
   GeneralNominalRefinements.assignment_transport (refines id tracked) m
 refine ⟨?_,?_,?_⟩
 · change PresenceNormalForm.All CommonNominalFullCarrier.model A atoms
   apply (PresenceNormalForm.all_append ..).mpr
   constructor
   · intro atom present
     have sameAtoms :
         raw.base.ordinary.map (PresenceNormalForm.Atom.rename embed) =
           GeneralSourceState.equationAtoms (0 : Fin 6) (.var 1) ++
           GeneralSourceState.equationAtoms 2 .emptyRecord ++
           GeneralSourceState.equationAtoms 3 .top ++ [.tyLe (.var 4) (.var 2)] := rfl
     rw [← sameAtoms] at present
     obtain ⟨original,member,rfl⟩ := List.mem_map.mp present
     apply (PresenceNormalForm.Atom.holds_rename _ A embed original).mpr
     rw [same]
     exact before.1 _ member
   · have size := justified_sound (just_width id tracked 5 (Or.inr rfl)) valid
     change Equivalent (A 5).1 .emptyRecord at size
     intro atom present
     simp only [GeneralSourceState.equationAtoms,List.mem_cons,List.not_mem_nil,or_false] at present
     rcases present with rfl|rfl
     · exact size.1
     · exact size.2
 · intro slot term seen
   have known := head_at slot term seen
   rw [known.2]
   exact justified_sound (just_width id tracked slot known.1) valid
 · intro pair present
   cases present

theorem fits_forward {before after : GeneralNominalState.State}
 (refinement : GeneralNominalRefinements.Refines before after) (m : Assignment)
 (params : List (GeneralNominalState.Parameter before.base.slots)) (values : List Argument)
 (valid : GeneralNominalState.FitsAll before.base m params values) :
 GeneralNominalState.FitsAll after.base m
    (params.map (GeneralNominalRefinements.renameParameter refinement.base.embed)) values := by
 induction params generalizing values with
 | nil => cases valid; exact .nil
 | cons p tail ih =>
   cases valid with
   | cons first rest =>
     exact .cons ((GeneralNominalRefinements.fits_transport refinement m _ _).mpr first) (ih _ rest)

theorem old_nominal (id : Nat) (tracked : id ∈ widthCandidates) (m : Assignment)
 (rawModel : GeneralNominalState.Models pointSnapshot m) (slot : Fin 5)
 (whereAt : slot = 0 ∨ slot = 1) :
 GeneralNominalState.Denotes (base id (large id tracked)) m (embed slot) descriptor := by
 have found : pointSnapshot.nominals slot = some exactCopy := ite_eq_left whereAt
 obtain ⟨values,fits,equal⟩ := rawModel.2.1 _ _ found
 exact ⟨values,fits_forward (refines id tracked) m _ _ fits,by simpa only [source_embed,descriptor,GeneralNominalRefinements.renameDescriptor] using equal⟩

theorem cache (id : Nat) (tracked : id ∈ widthCandidates) : CacheSound installed (snapshot id tracked) := by
 intro observation given
 cases given with
 | scalar slot scalar seen =>
   change Fin 6 at slot
   change viewHeads slot = .scalar scalar at seen
   have term := view_at slot (.base scalar) (by rw [seen]; rfl)
   cases term.2
 | structural slot kind children seen =>
   change Fin 6 at slot
   change Fin 1 at kind
   change viewHeads slot = .structural kind children at seen
   have term := view_at slot ((viewShapes kind).term children) (by rw [seen]; rfl)
   exact term.2 ▸ just_width id tracked slot term.1
 | nominal slot d seen =>
   obtain ⟨whereAt,rfl⟩ := nominal_at slot d seen
   refine ⟨[],[],.source,.source,?_⟩
   intro m previous _
   rcases whereAt with rfl|rfl
   · exact old_nominal id tracked m ((point_models_iff m).mpr previous.1) 0 (Or.inl rfl)
   · exact old_nominal id tracked m ((point_models_iff m).mpr previous.1) 1 (Or.inr rfl)

noncomputable def certificate (id : Nat) (tracked : id ∈ widthCandidates) : Refresh installed (context id tracked) where
 refines := refines id tracked
 interpretation := rfl
 support := support id tracked
 constraints := fun m valid => ⟨base_models id tracked m valid,valid.1.1.2.2⟩
 cache := cache id tracked

end Yulang.GeneralRebaseWidthCertificate275
