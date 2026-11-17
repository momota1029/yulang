import Yulang.GeneralNominalOrderedMergeExample248
import Yulang.GeneralPresenceOrderedDependence247

/-! Stable identities do not imply that actual merge-entry target domains are
unchanged. This finite representation regression is not a source reachability,
language rejection, or semantic counterexample. -/
namespace Yulang.GeneralNominalOrderedRefreshDomainLimit248
open Core.PresenceGeneration
open GeneralNominalAllocation (Bindings)
open GeneralPresenceOrderedDependence247
open GeneralPresenceOrderedBlock247 GeneralPresenceOrderedPrepared247

def oldBindings : Bindings := [(7,(0,1))]
def freshBindings : Bindings := [(7,(0,1)),(7,(1,0))]
def names : List Nat := [7]
def old := GeneralNominalRebaseDefinitions241.entries 10 0 0 oldBindings names
def fresh := GeneralNominalRebaseDefinitions241.entries 10 0 0 freshBindings names

theorem stable_slots (purpose name : Nat) :
 GeneralNominalRebaseDefinitions241.slot 10 0 0 purpose name oldBindings =
 GeneralNominalRebaseDefinitions241.slot 10 0 0 purpose name freshBindings := rfl

theorem old_empty : old = [] := rfl

theorem fresh_entries : fresh =
 [(GeneralNominalRebaseDefinitions241.slot 10 0 0 0 7 freshBindings,
     TyTerm.union (.var 0) (.var 1)),
  (GeneralNominalRebaseDefinitions241.slot 10 0 0 1 7 freshBindings,
     TyTerm.inter (.var 1) (.var 0))] := rfl

theorem targets_not_within : ¬ TargetsWithin fresh old := by
 intro within
 obtain ⟨entry,present,_⟩ := within _ (by rw [fresh_entries]; exact List.mem_cons_self)
 rw [old_empty] at present
 cases present

theorem old_prepares : prepare old = some [] := by
 rw [old_empty]
 simp [prepare,GeneralPresenceOrderedDedup247.dedup,GeneralPresenceOrderedSort247.sort,
   GeneralPresenceOrderedSort247.sortFuel]

theorem fresh_prepares : ∃ sorted, prepare fresh = some sorted ∧ SafeOrder sorted := by
 apply GeneralNominalOrderedMerge248.prepared 10 0 0 freshBindings names [0,1]
 · intro name named many
   exact GeneralNominalOrderedMergeExample248.protected_pool name
     (by simpa [names,GeneralNominalOrderedMergeExample248.names] using named) many
 · exact GeneralNominalOrderedMergeExample248.endpoints
end Yulang.GeneralNominalOrderedRefreshDomainLimit248
