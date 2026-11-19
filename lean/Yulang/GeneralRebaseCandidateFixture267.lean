import Yulang.GeneralRebaseEnumeratePlans267
import Yulang.GeneralRebaseSourceStrictFixture265

set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
namespace Yulang.GeneralRebaseCandidateFixture267
open GeneralDictionaryCompoundFrame238 (before frame)
open GeneralDictionaryCompoundPacket238 (plan)
open GeneralDictionaryCompoundSource238 (registry sourceRegistry declaration)
open GeneralDictionaryJournalRefinement228Source (root roles)
open GeneralRebaseEnumeratePlans267 (plans)

theorem checked : GeneralRebaseCandidatePlan267.DeclChecked registry roles :=
 (GeneralNominalCenteredHeadAllocEncoding.registry_checked GeneralDictionaryCompoundSource238.checked).2

noncomputable def inferred := plans registry before root checked

theorem actual_listed : plan ∈ inferred :=
 GeneralRebaseEnumeratePlans267.includes_frame registry before root checked plan .root frame

/-- Starts from the genuine pre-install journal and registry, not a stored
list of candidate plans. This tests structural discovery, not guard search. -/
theorem inferred_key :
 inferred.map (fun entry => (entry.packet.site.occurrence.identity,entry.packet.declaration.id)) =
 [(root.identity,declaration.id)] := by
 decide +kernel

theorem inferred_exact : inferred = [plan] := by
 have one : inferred.length = 1 := by
   have lengths := congrArg List.length inferred_key
   simpa only [List.length_map,List.length_cons,List.length_nil,Nat.zero_add] using lengths
 cases h : inferred with
 | nil => simp [h] at one
 | cons head rest =>
   have empty : rest = [] := by simpa [h] using one
   subst rest
   have same : plan = head := List.mem_singleton.mp (h ▸ actual_listed)
   cases same
   exact h

end Yulang.GeneralRebaseCandidateFixture267
