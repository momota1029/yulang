import Yulang.GeneralRebaseMergeCenters267
import Yulang.GeneralRebaseCheckedLocal266

namespace Yulang.GeneralRebaseMergeScan267
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalCenters (Site SameInputs)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalSaturationState (Alias Generated)
open GeneralRebaseExecutableAlias267 (aliased aliased_exact)
open GeneralRebaseExecutableGenerated267 (discover discover_exact)
open GeneralNominalVersionedAdministrative232 (merge)
open GeneralRebaseLiveProjection264 (liveFacts project)
open GeneralRebaseCheckedLocal266 (FiniteBasis checked_merge affectedProposal)
open GeneralRebaseCheckedWrite259 (commit)
open GeneralSourceState (Output)

local instance : DecidableEq (Occurrence roles) := GeneralRebaseOccurrenceEq267.occurrenceEq

/-- Distinct class membership is an exact finite gate; semantic equality of
the two sites' inputs is separate. The target site need not itself be generated. -/
def linkedPairs (state : State roles) (root : Occurrence roles) : List (Site roles × Site roles) :=
 let known := discover state.core.erased.current root
 (state.core.sites.filter fun first => decide (first.occurrence ∈ known)).flatMap fun first =>
   (state.core.sites.filter fun last =>
     !(aliased state.core.erased.current first.occurrence.identity last.occurrence.identity)).map fun last => (first,last)

theorem linkedPairs_exact (state : State roles) (root : Occurrence roles) (first last : Site roles) :
 (first,last) ∈ linkedPairs state root ↔
 first ∈ state.core.sites ∧ last ∈ state.core.sites ∧
 Generated state.core.erased.current root first.occurrence ∧
 ¬ Alias state.core.erased.current first.occurrence.identity last.occurrence.identity := by
 unfold linkedPairs
 constructor
 · intro candidate
   obtain ⟨f,seen,within⟩ := List.mem_flatMap.mp candidate
   obtain ⟨l,paired,equal⟩ := List.mem_map.mp within
   cases equal
   obtain ⟨one,known⟩ := List.mem_filter.mp seen
   obtain ⟨two,notAliased⟩ := List.mem_filter.mp paired
   refine ⟨one,two,(discover_exact ..).mp (of_decide_eq_true known),?_⟩
   intro alias
   have h := (aliased_exact ..).mpr alias
   simp [h] at notAliased
 · rintro ⟨one,two,generated,notAliased⟩
   apply List.mem_flatMap.mpr
   refine ⟨first,List.mem_filter.mpr ⟨one,decide_eq_true ((discover_exact ..).mpr generated)⟩,?_⟩
   apply List.mem_map.mpr
   refine ⟨last,List.mem_filter.mpr ⟨two,?_⟩,rfl⟩
   have no := Bool.eq_false_iff.mpr (fun h => notAliased ((aliased_exact ..).mp h))
   simp [no]

def scan (state : State roles) (root : Occurrence roles) (semantic : Site roles → Site roles → Bool) :
 List (Site roles × Site roles) :=
 (linkedPairs state root).filter fun pair =>
   GeneralRebaseMergeCenters267.same pair.1 pair.2 || semantic pair.1 pair.2

theorem scan_exact (state : State roles) (root : Occurrence roles) (semantic : Site roles → Site roles → Bool)
 (first last : Site roles) :
 (first,last) ∈ scan state root semantic ↔
 (first,last) ∈ linkedPairs state root ∧
 (GeneralRebaseMergeCenters267.same first last = true ∨ semantic first last = true) := by
 simp only [scan,List.mem_filter,Bool.or_eq_true]

theorem source_step (registry : Registry) (state : State roles) (root : Occurrence roles)
 (semantic : Site roles → Site roles → Bool) (first last : Site roles)
 (listed : (first,last) ∈ scan state root semantic)
 (sound : semantic first last = true → SameInputs (Models state) first last) :
 GeneralNominalVersionedMixedKernel234.Step registry root state (merge state first last) := by
 obtain ⟨pair,verified⟩ := (scan_exact ..).mp listed
 obtain ⟨one,two,generated,openPair⟩ := (linkedPairs_exact ..).mp pair
 have matching := verified.elim (GeneralRebaseMergeCenters267.source_sound (Models state) first last) sound
 exact ⟨_,generated,.merge first last one two matching openPair⟩

theorem actual_covered (state : State roles) (root : Occurrence roles)
 (semantic : Site roles → Site roles → Bool) (first last : Site roles)
 (one : first ∈ state.core.sites) (two : last ∈ state.core.sites)
 (generated : Generated state.core.erased.current root first.occurrence)
 (openPair : ¬ Alias state.core.erased.current first.occurrence.identity last.occurrence.identity)
 (matching : SameInputs (Models state) first last) (complete : SameInputs (Models state) first last → semantic first last = true) :
 (first,last) ∈ scan state root semantic :=
 (scan_exact ..).mpr ⟨(linkedPairs_exact ..).mpr ⟨one,two,generated,openPair⟩,Or.inr (complete matching)⟩

theorem checked_source_merge (registry : Registry) (state : State roles) (root : Occurrence roles)
 (semantic : Site roles → Site roles → Bool) (first last : Site roles)
 (listed : (first,last) ∈ scan state root semantic)
 (sound : semantic first last = true → SameInputs (Models state) first last)
 (owners : List Nat) (pool : List Output)
 (closed : liveFacts (merge state first last) ⊆ FiniteBasis owners pool) :
 let before := project owners pool state
 let after := project owners pool (merge state first last)
 GeneralNominalVersionedMixedKernel234.Step registry root state (merge state first last) ∧
 commit before (affectedProposal state first last) =
   .ok (if after.remaining = before.remaining then none else some after) :=
 ⟨source_step registry state root semantic first last listed sound,
   checked_merge state first last owners pool closed⟩

end Yulang.GeneralRebaseMergeScan267
