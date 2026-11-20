import Yulang.GeneralRebaseWatchGuardQueries284

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseWatchGuardSteps284
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable)
open GeneralRebaseActualWatch284 (Cache)
open GeneralRebaseSliceJournal283 (journalReads)
open GeneralRebaseWatchGuardQueries284 (Cached siteReads equality same_inputs)
open GeneralNominalVersionedAdministrative232 (equate merge)
open GeneralNominalSaturationState (Generated Alias)
open GeneralNominalVersionedMixedKernel234 (Administrative At)
open GeneralRebaseMixedCounts277 (Actual)
open GeneralNominalState (sources)
open GeneralNominalFeedbackSteps (RawEqual)
open CommonNominalFullCarrier (Equivalent)

variable {roles : Roles.RoleDecls} {r : Registry} {root : Occurrence roles} {state : State roles}
  {watch : List Nat} {defs : List (GeneralPresenceDefinitionRewrite244.Entry Nat)}

structure EquateInput (state : State roles) (root focus : Occurrence roles) (a b : Nat) : Prop where
  generated : Generated state.core.erased.current root focus
  first : a ∈ sources state.core.erased.current.context.state
  last : b ∈ sources state.core.erased.current.context.state
  novel : ¬ RawEqual state.core.erased.current a b

theorem equate_sound (valid : Cache state watch defs) (seen : Reachable r root state)
    (reads : journalReads state ⊆ watch) {focus : Occurrence roles} {a b : Nat}
    (allowed : EquateInput state root focus a b) (seenA : a ∈ watch) (seenB : b ∈ watch)
    (agree : ∀ m, Cached state defs m → Equivalent (m a).1 (m b).1) :
    Actual r root state (equate state a b) :=
  ⟨focus,allowed.generated,.administrative
    (.equate focus a b allowed.first allowed.last ((equality valid seen reads a b seenA seenB).mpr agree) allowed.novel)⟩

structure MergeInput (state : State roles) (root : Occurrence roles) (first last : Site roles) : Prop where
  generated : Generated state.core.erased.current root first.occurrence
  first_seen : first ∈ state.core.sites
  last_seen : last ∈ state.core.sites
  novel : ¬ Alias state.core.erased.current first.occurrence.identity last.occurrence.identity

theorem merge_sound (valid : Cache state watch defs) (seen : Reachable r root state)
    (reads : journalReads state ⊆ watch) {first last : Site roles}
    (allowed : MergeInput state root first last) (coverage : siteReads first ++ siteReads last ⊆ watch)
    (agree : SameInputs (Cached state defs) first last) :
    Actual r root state (merge state first last) :=
  ⟨_,allowed.generated,.merge first last allowed.first_seen allowed.last_seen
    ((same_inputs valid seen reads first last coverage).mpr agree) allowed.novel⟩

end Yulang.GeneralRebaseWatchGuardSteps284
