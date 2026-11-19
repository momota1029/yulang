import Yulang.GeneralRebaseCompoundOwnerStep273
import Yulang.GeneralRebaseCompoundOwnerMeaning273

set_option maxRecDepth 16000
set_option maxHeartbeats 2500000
namespace Yulang.GeneralRebaseCompoundOwnerBoundary273
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (Models)
open GeneralDictionaryCompoundSource238 (registry)
open GeneralDictionaryJournalRefinement228Source (root)
open GeneralDictionaryCompoundFrame238 (before installed)
open GeneralDictionaryCompoundPoint238 (point)
open GeneralDictionaryCompoundObstruction238 (oldPlan currentPlan)
open GeneralRebaseCompoundRows273 (Agrees)
open GeneralRebaseCompoundRowsMeaning273 (Public)
open GeneralRebaseCompoundOwnerStep273 (Stage PublicMeaning next)
open GeneralRebaseCompoundOwnerMeaning273 (Sound historical replacement)
open GeneralRebaseCompoundOwnerBlock273 (Slot eval loose)
open GeneralRebaseCompoundReplacementFrame273 (Meaning)
open GeneralRebaseCompoundReplacementPublic273 (complete completed agrees)
open GeneralRebaseCompoundSourceTypes273 (before_exact source_depends_on_types)

theorem initial_public (boundary : Assignment) : PublicMeaning .initial boundary ↔ Public before boundary := by
 have exact := before_exact boundary
 constructor
 · intro checked
   exact ⟨boundary,⟨fun _ _ => rfl,fun _ => rfl⟩,exact.mpr checked.1⟩
 · rintro ⟨m,agree,old⟩
   refine ⟨(source_depends_on_types m boundary (fun n h => congrArg Prod.fst (agree.1 n h))).mp
     ((before_exact m).mp old),?_⟩
   intro bad
   exact False.elim (bad rfl)

theorem installed_public (boundary : Assignment) :
 PublicMeaning .installed boundary ↔ Public installed boundary :=
 (GeneralRebaseCompoundOwnerStep273.install_meaning boundary).trans
  (GeneralRebaseCompoundRows273.public_exact boundary).symm

theorem point_public (boundary : Assignment) :
 PublicMeaning .replacement boundary ↔ Public point boundary :=
 (GeneralRebaseCompoundOwnerStep273.replacement_meaning boundary).trans
  ((GeneralRebaseCompoundReplacementPublic273.public_exact boundary).symm.trans
    (GeneralRebaseCompoundReplacementPublic273.same_public boundary))

theorem replacement_public (boundary : Assignment) :
 PublicMeaning .replacement boundary ↔ ∃ m, Agrees m boundary ∧ Meaning m :=
 (GeneralRebaseCompoundOwnerStep273.replacement_meaning boundary).trans
  (GeneralRebaseCompoundReplacementPublic273.public_exact boundary).symm

theorem proof_of_slots_loose (boundary : Assignment) (known : PublicMeaning .installed boundary) :
 ∃ m, Agrees m boundary ∧ Models installed m ∧ Sound m oldPlan loose := by
 obtain ⟨m,agree,held⟩ := (installed_public boundary).mp known
 exact ⟨m,agree,held,historical m (held.2.1 oldPlan (List.mem_cons_self ..))⟩

theorem proof_of_slots_point (boundary : Assignment) (known : PublicMeaning .replacement boundary) :
 Agrees (complete boundary) boundary ∧ Meaning (complete boundary) ∧
 Sound (complete boundary) currentPlan GeneralRebaseCompoundOwnerBlock273.point := by
 have fixed := (GeneralRebaseCompoundOwnerStep273.replacement_meaning _).mp known
 have same := agrees boundary
 have valid := completed boundary fixed
 exact ⟨same,valid,replacement _ valid.1⟩

/-- The second old step is the genuine Reobserve. Only the new finite
counterpart replaces the owner block; no claim is made that the old
kernel installs its incompatible current packet. -/
theorem exact_two_steps :
 GeneralNominalVersionedMixedKernel234.Step registry root before installed ∧
 GeneralNominalVersionedMixedKernel234.Step registry root installed point ∧
 next .initial GeneralDictionaryCompoundPacket238.packet.bindings 2 = some .installed ∧
 next .installed currentPlan.packet.bindings 2 = some .replacement ∧
 ∀ boundary, (PublicMeaning .initial boundary ↔ Public before boundary) ∧
  (PublicMeaning .installed boundary ↔ Public installed boundary) ∧
  (PublicMeaning .replacement boundary ↔ Public point boundary) :=
 ⟨GeneralDictionaryCompoundStep238.step,GeneralDictionaryCompoundPoint238.step,
  GeneralRebaseCompoundOwnerStep273.actual_install,GeneralRebaseCompoundOwnerStep273.actual_replacement,
  fun boundary => ⟨initial_public boundary,installed_public boundary,point_public boundary⟩⟩

end Yulang.GeneralRebaseCompoundOwnerBoundary273
