import Yulang.GeneralRebaseSourceRepresentatives263
namespace Yulang.GeneralRebaseSourceLocalHeads263
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseSourceRepresentatives263 (Path RegisteredAt representatives representatives_registered)

/-- Choose one witnessing snapshot for the already chosen representative.
Unused owner codes use the initial snapshot. Noncomputable proof infrastructure,
not an executable search for a future source snapshot. -/
noncomputable def representativeSnapshot (registry : Registry) (root : Occurrence roles) (start : State roles)
 (inhabited : ∃ owner plan, RegisteredAt registry root start owner plan) (owner : Nat) : State roles := by
 classical
 exact if occurs : ∃ plan, RegisteredAt registry root start owner plan then
   Classical.choose (representatives_registered registry root start inhabited owner occurs)
 else start

theorem representativeSnapshot_spec (registry : Registry) (root : Occurrence roles) (start : State roles)
 (inhabited : ∃ owner plan, RegisteredAt registry root start owner plan)
 (owner : Nat) (occurs : ∃ plan, RegisteredAt registry root start owner plan) :
 Path registry root start (representativeSnapshot registry root start inhabited owner) ∧
 representatives registry root start inhabited owner ∈ (representativeSnapshot registry root start inhabited owner).plans ∧
 GeneralRebaseRegisteredOwners263.code (representatives registry root start inhabited owner) = owner := by
 classical
 simp only [representativeSnapshot,dite_eq_left occurs]
 exact Classical.choose_spec (representatives_registered registry root start inhabited owner occurs)

/-- Only finitely listed, actually occurring owners' chosen snapshots need
head support. This is not head support for every future source state. -/
def RepresentativeHeads (registry : Registry) (root : Occurrence roles) (start : State roles)
 (inhabited : ∃ owner plan, RegisteredAt registry root start owner plan)
 (owners : List Nat) (assignment : Assignment) : Prop :=
 ∀ owner ∈ owners, (∃ plan, RegisteredAt registry root start owner plan) →
 GeneralRebaseSourceCenters263.Heads (representativeSnapshot registry root start inhabited owner) assignment

/-- Local semantic transport uses just the selected representative's witness
snapshot and the actual observed snapshot. No global SourceHeads is required. -/
theorem representative_compatible (registry : Registry)
 (checked : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Checked registry)
 (root : Occurrence roles) (start : State roles)
 (source : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Initial registry root start)
 (inhabited : ∃ owner plan, RegisteredAt registry root start owner plan)
 (owners : List Nat) (state : State roles) (path : Path registry root start state)
 (plan : Plan roles) (member : plan ∈ state.plans)
 (listed : GeneralRebaseRegisteredOwners263.code plan ∈ owners)
 (assignment : Assignment)
 (representativeHeads : RepresentativeHeads registry root start inhabited owners assignment)
 (observedHeads : GeneralRebaseSourceCenters263.Heads state assignment) :
 GeneralRebaseNormalizedBody263.Compatible
   (representatives registry root start inhabited (GeneralRebaseRegisteredOwners263.code plan)) plan assignment := by
 have occurs : ∃ candidate, RegisteredAt registry root start (GeneralRebaseRegisteredOwners263.code plan) candidate :=
   ⟨plan,state,path,member,rfl⟩
 have witness := representativeSnapshot_spec registry root start inhabited _ occurs
 exact GeneralRebaseSourceCenters263.source_compatible_from_heads registry checked root start
   (representativeSnapshot registry root start inhabited (GeneralRebaseRegisteredOwners263.code plan)) state source
   witness.1 path _ plan witness.2.1 member
   ((GeneralRebaseRegisteredOwners263.code_eq_iff _ plan).mp witness.2.2)
   assignment (representativeHeads _ listed occurs) observedHeads

/-- A one-snapshot selection family, with explicit finite owner coverage. -/
theorem all_registered_compatible (registry : Registry)
 (checked : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Checked registry)
 (root : Occurrence roles) (start : State roles)
 (source : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Initial registry root start)
 (inhabited : ∃ owner plan, RegisteredAt registry root start owner plan)
 (owners : List Nat) (state : State roles) (path : Path registry root start state)
 (listed : ∀ plan ∈ state.plans, GeneralRebaseRegisteredOwners263.code plan ∈ owners)
 (assignment : Assignment)
 (representativeHeads : RepresentativeHeads registry root start inhabited owners assignment)
 (observedHeads : GeneralRebaseSourceCenters263.Heads state assignment) :
 ∀ plan ∈ state.plans, GeneralRebaseNormalizedBody263.Compatible
   (representatives registry root start inhabited (GeneralRebaseRegisteredOwners263.code plan)) plan assignment :=
 fun plan member => representative_compatible registry checked root start source inhabited owners state path plan member
   (listed plan member) assignment representativeHeads observedHeads

/-- Existing global support implies this weaker finite representative support.
The converse and automatic head satisfaction are intentionally not asserted. -/
theorem of_sourceHeads (registry : Registry) (root : Occurrence roles) (start : State roles)
 (inhabited : ∃ owner plan, RegisteredAt registry root start owner plan)
 (owners : List Nat) (assignment : Assignment)
 (global : GeneralRebaseSourceRepresentatives263.SourceHeads registry root start assignment) :
 RepresentativeHeads registry root start inhabited owners assignment := by
 intro owner _ occurs
 exact global _ (representativeSnapshot_spec registry root start inhabited owner occurs).1
end Yulang.GeneralRebaseSourceLocalHeads263
