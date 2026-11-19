import Yulang.GeneralRebaseComputeEffect267

namespace Yulang.GeneralRebaseConcreteEntries267
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalCenters (Plan Site)
open GeneralNominalVersionedInstall232 (install)
open GeneralNominalVersionedAdministrative232 (merge)
open GeneralSourceState (Output)
open GeneralRebaseSourceSurvivor267 (Boundary Encoded)
open GeneralRebaseSourceObserver267 (Probes installs proposals)
open GeneralRebaseObserverSound267 (Sound)
open GeneralRebaseStep258 (Proposal write)
open GeneralRebaseLiveProjection264 (project liveFacts)
open GeneralRebaseMultiSelection263 (proposal ofPlan)
open GeneralRebaseCheckedLocal266 (affectedProposal)
open GeneralRebaseComputeEffect267 (computed computed_valid of_list)

structure Entry (registry : Registry) (root : Occurrence roles) (state : State roles) where
 after : State roles
 facts : Proposal
 step : (Boundary roles).Step registry root state after
 square : ∀ (owners : List Nat) (pool : List Output), write (project owners pool state) facts = project owners pool after
 support : facts ⊆ liveFacts after

def installEntry (registry : Registry) (root : Occurrence roles) (state : State roles)
 (checked : (Boundary roles).Checked registry) (reachable : B4TargetV8.Reachable (Boundary roles) registry root state)
 (probes : Probes roles) (sound : Sound registry state root checked probes)
 (item : {plan : Plan roles // plan ∈ installs registry state root checked probes}) : Entry registry root state :=
 let cert := of_list registry root state checked reachable probes sound item.val item.property
 let e := computed registry root state item.val cert
 let valid := computed_valid registry root state item.val cert
 ⟨install state e,proposal state.core (ofPlan item.val),
   ⟨_,valid.1,.install e valid.2.1 valid.2.2⟩,
   fun owners pool => (GeneralRebaseSourceInstallProjection264.project_install_current
      registry checked root state reachable e valid.2.1 owners pool).symm,
   GeneralRebaseCheckedLocal266.install_proposal_in_live registry checked root state reachable e valid.2.1⟩

def mergeEntry (registry : Registry) (root : Occurrence roles) (state : State roles)
 (checked : (Boundary roles).Checked registry) (probes : Probes roles) (sound : Sound registry state root checked probes)
 (item : {pair : Site roles × Site roles // pair ∈ GeneralRebaseMergeScan267.scan state root probes.mergeInputs}) :
 Entry registry root state :=
 let linked := (GeneralRebaseMergeScan267.linkedPairs_exact ..).mp
   ((GeneralRebaseMergeScan267.scan_exact ..).mp item.property).1
 ⟨merge state item.val.1 item.val.2,affectedProposal state item.val.1 item.val.2,
   GeneralRebaseMergeScan267.source_step (Encoded registry) state root probes.mergeInputs item.val.1 item.val.2
      item.property (sound.mergeFacts _ linked.1 _ linked.2.1),
   fun owners pool => (GeneralRebaseAffectedMerge264.project_merge owners pool state item.val.1 item.val.2).symm,
   GeneralRebaseCheckedLocal266.merge_proposal_in_live state item.val.1 item.val.2⟩

/-- Retain the concrete transition alongside each computed abstract proposal.
Proof fields use the independently checked guards and are erased at runtime. -/
def entries (registry : Registry) (root : Occurrence roles) (state : State roles)
 (checked : (Boundary roles).Checked registry) (reachable : B4TargetV8.Reachable (Boundary roles) registry root state)
 (probes : Probes roles) (sound : Sound registry state root checked probes) :
 List (Entry registry root state) :=
 (installs registry state root checked probes).attach.map (installEntry registry root state checked reachable probes sound) ++
 (GeneralRebaseMergeScan267.scan state root probes.mergeInputs).attach.map (mergeEntry registry root state checked probes sound)

theorem same_order (registry : Registry) (root : Occurrence roles) (state : State roles)
 (checked : (Boundary roles).Checked registry) (reachable : B4TargetV8.Reachable (Boundary roles) registry root state)
 (probes : Probes roles) (sound : Sound registry state root checked probes) :
 (entries registry root state checked reachable probes sound).map Entry.facts = proposals registry state root checked probes := by
 simp only [entries,List.map_append,List.map_map,proposals]
 change (installs registry state root checked probes).attach.map (fun item => (fun plan => proposal state.core (ofPlan plan)) item.val) ++
   (GeneralRebaseMergeScan267.scan state root probes.mergeInputs).attach.map
    (fun item => (fun pair : Site roles × Site roles => affectedProposal state pair.1 pair.2) item.val) = _
 rw [List.attach_map_val (l := installs registry state root checked probes)
      (f := fun plan => proposal state.core (ofPlan plan)),
    List.attach_map_val (l := GeneralRebaseMergeScan267.scan state root probes.mergeInputs)
      (f := fun pair => affectedProposal state pair.1 pair.2)]

end Yulang.GeneralRebaseConcreteEntries267
