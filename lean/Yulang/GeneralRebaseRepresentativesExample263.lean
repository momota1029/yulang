import Yulang.GeneralRebaseSourceRepresentatives263
import Yulang.GeneralDictionaryCompoundStep238
namespace Yulang.GeneralRebaseRepresentativesExample263
open GeneralRebaseSourceRepresentatives263
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryCompoundSource238
open GeneralDictionaryCompoundFrame238
open GeneralDictionaryCompoundPacket238 (plan)

/-- Actual nonempty versioned source journal after a verified installation,
not a hypothetical Plan inhabitation or arbitrary initial table. -/
theorem actual_registered : RegisteredAt sourceRegistry root before
 (GeneralRebaseRegisteredOwners263.code plan) plan := by
 refine ⟨installed,.tail .refl GeneralDictionaryCompoundStep238.step,?_,rfl⟩
 exact List.mem_cons_self

theorem actual_inhabited : ∃ owner candidate, RegisteredAt sourceRegistry root before owner candidate :=
 ⟨_,plan,actual_registered⟩

theorem actual_representative_registered : RegisteredAt sourceRegistry root before
 (GeneralRebaseRegisteredOwners263.code plan)
 (representatives sourceRegistry root before actual_inhabited (GeneralRebaseRegisteredOwners263.code plan)) :=
 representatives_registered sourceRegistry root before actual_inhabited _ ⟨plan,actual_registered⟩
end Yulang.GeneralRebaseRepresentativesExample263
