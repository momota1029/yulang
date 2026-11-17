import Yulang.GeneralNominalPersistentOwner250
/-! New metadata interpreted at fresh aggregate values is attached AFTER the
owner update. Its old-side constraint is a computed fresh readback, never an
assumed existence of a second independent model. -/
namespace Yulang.GeneralNominalPostInstall250
open Core.PresenceGeneration PresenceNormalForm
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalJournalAppend250 (Delta attach subst)
open GeneralNominalMaterializedOwnerFrame249 (Frame Models)
open GeneralNominalMaterializedSequenceModels249 (PublicModels same_domain_protected subset_private)
open GeneralNominalPersistentOwner250 (update)
open GeneralPresenceOrderedBlock247 GeneralPresenceOrderedDependence247
open GeneralPresenceOrderedSubstitution247 GeneralPresenceOrderedRebase247
open GeneralPresenceDefinitionRewrite244
open CommonNominalFullCarrier GeneralPresenceCommonLaws245

theorem delta_iff (delta : Delta) (first last : Assignment)
 (same : GeneralNominalAssignmentCongruence238.Same first last) : delta.Holds first ↔ delta.Holds last :=
 and_congr (forall_congr' fun args => forall_congr' fun _ => GeneralNominalJournalViewCongruence250.observations_iff same args)
 (and_congr (forall_congr' fun site => forall_congr' fun _ => GeneralNominalSchemaViewCongruence250.site_iff same site)
 (and_congr (forall_congr' fun packet => forall_congr' fun _ => GeneralNominalJournalViewCongruence250.packet_iff same packet)
 (and_congr (forall_congr' fun effect => forall_congr' fun _ => GeneralNominalJournalViewCongruence250.effect_iff same effect)
 (GeneralNominalAssignmentCongruence238.all_iff same delta.ordinary))))

theorem delta_ordered (delta : Delta) (entries : List (Entry Nat)) (assignment : Assignment) :
 (subst (mapping entries) delta).Holds assignment ↔ delta.Holds (solve model entries assignment) := by
 rw [GeneralNominalJournalAppend250.subst_exact,GeneralNominalOrderedRaw248.read_mapping]

theorem post_public_models_iff (frame : Frame) (safe : SafeOrder frame.definitions)
 (raw : List (Entry Nat)) (delta : Delta) (shared : Nat → Prop)
 (privateNames : ∀ name, shared name → ∀ entry ∈ frame.definitions, entry.1 ≠ name)
 (boundary : Assignment) :
 (∃ assignment, Models frame assignment ∧
   (subst (mapping (update frame raw).definitions) delta).Holds assignment ∧
   Agrees model shared assignment boundary) ↔
 PublicModels (attach (update frame raw) delta) shared boundary := by
 let fresh := (update frame raw).definitions
 have freshSafe : SafeOrder fresh := GeneralNominalPersistentOwner250.safe_update frame safe raw
 have within : TargetsWithin fresh frame.definitions := GeneralPresencePersistentSnapshot250.refresh_within _ _
 have oldWithin : TargetsWithin frame.definitions fresh := GeneralPresencePersistentSnapshot250.old_within _ _
 constructor
 · rintro ⟨assignment,valid,extra,agree⟩
   refine ⟨solve model fresh assignment,?_,?_⟩
   · apply (GeneralNominalJournalAppend250.attach_models _ _ _).mpr
     refine ⟨?_,(delta_ordered delta fresh assignment).mp extra⟩
     exact GeneralNominalArbitraryOwnerFrame250.models_forward frame fresh freshSafe
       (same_domain_protected frame fresh safe within) assignment valid
   · intro name sharedName
     rw [solve_outside model fresh assignment name (subset_private _ _ within shared privateNames name sharedName)]
     exact agree name sharedName
 · rintro ⟨assignment,valid,agree⟩
   obtain ⟨updated,extra⟩ := (GeneralNominalJournalAppend250.attach_models _ _ _).mp valid
   refine ⟨solve model frame.definitions assignment,
     GeneralNominalMaterializedOwnerFrame249.models_backward frame safe fresh assignment updated,?_,?_⟩
   · apply (delta_ordered delta fresh _).mpr
     rw [solve_absorbs model fresh frame.definitions freshSafe oldWithin]
     exact (delta_iff delta _ assignment
       (GeneralPresenceOrderedRecovery247.solve_compatible model common_laws fresh assignment
         ((all_append model assignment _ _).mp updated.2).2)).mpr extra
   · intro name sharedName
     rw [solve_outside model frame.definitions assignment name (privateNames name sharedName)]
     exact agree name sharedName
end Yulang.GeneralNominalPostInstall250
