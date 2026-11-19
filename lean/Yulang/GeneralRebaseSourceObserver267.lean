import Yulang.GeneralRebaseStrictSourceCases267

namespace Yulang.GeneralRebaseSourceObserver267
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalCenters (Plan Site)
open GeneralNominalVersionedJournal232 (State)
open GeneralRebaseSourceSurvivor267 (Boundary Encoded declChecked)
open GeneralRebaseHeadProbe267 (atFocus)
open GeneralRebaseExecutableGenerated267 (discover discover_exact)
open GeneralRebaseInstallCandidates267 (scan)
open GeneralRebaseStep258 (Proposal Observer)
open GeneralRebaseCheckedLocal266 (affectedProposal)
open GeneralRebaseMultiSelection263 (proposal ofPlan)

structure Probes (roles : Roles.RoleDecls) where
 head : Occurrence roles → Plan roles → Option Bool
 novelty : Occurrence roles → Plan roles → Bool
 joint : Occurrence roles → Plan roles → Bool
 mergeInputs : Site roles → Site roles → Bool

def installAt (registry : Registry) (state : State roles) (root focus : Occurrence roles)
 (checked : (Boundary roles).Checked registry) (probes : Probes roles) : List (Plan roles) :=
 scan state (probes.head focus) (probes.novelty focus) (probes.joint focus)
   (atFocus (Encoded registry) state root focus (declChecked checked))

def installs (registry : Registry) (state : State roles) (root : Occurrence roles)
 (checked : (Boundary roles).Checked registry) (probes : Probes roles) : List (Plan roles) :=
 (discover state.core.erased.current root).flatMap fun focus => installAt registry state root focus checked probes

theorem installs_exact (registry : Registry) (state : State roles) (root : Occurrence roles)
 (checked : (Boundary roles).Checked registry) (probes : Probes roles) (plan : Plan roles) :
 plan ∈ installs registry state root checked probes ↔
 ∃ focus, GeneralNominalSaturationState.Generated state.core.erased.current root focus ∧
 plan ∈ installAt registry state root focus checked probes := by
 constructor
 · intro found
   obtain ⟨focus,present,member⟩ := List.mem_flatMap.mp found
   exact ⟨focus,(discover_exact ..).mp present,member⟩
 · rintro ⟨focus,generated,member⟩
   exact List.mem_flatMap.mpr ⟨focus,(discover_exact ..).mpr generated,member⟩

def proposals (registry : Registry) (state : State roles) (root : Occurrence roles)
 (checked : (Boundary roles).Checked registry) (probes : Probes roles) : List Proposal :=
 (installs registry state root checked probes).map (fun plan => proposal state.core (ofPlan plan)) ++
 (GeneralRebaseMergeScan267.scan state root probes.mergeInputs).map fun pair =>
   affectedProposal state pair.1 pair.2

theorem proposals_exact (registry : Registry) (state : State roles) (root : Occurrence roles)
 (checked : (Boundary roles).Checked registry) (probes : Probes roles) (result : Proposal) :
 result ∈ proposals registry state root checked probes ↔
 (∃ plan ∈ installs registry state root checked probes, proposal state.core (ofPlan plan) = result) ∨
 ∃ pair ∈ GeneralRebaseMergeScan267.scan state root probes.mergeInputs,
   affectedProposal state pair.1 pair.2 = result := by
 simp [proposals]

end Yulang.GeneralRebaseSourceObserver267
