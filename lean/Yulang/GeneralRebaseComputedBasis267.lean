import Yulang.GeneralRebaseConcreteCorrect267
import Yulang.GeneralRebaseRegisteredOwners263

namespace Yulang.GeneralRebaseComputedBasis267
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralDeclarationPatterns (Pattern)
open GeneralNominalCandidates (Context)
open GeneralNominalVersionedJournal232 (State initial)
open GeneralRebaseSourceSurvivor267 (Boundary Encoded)
open GeneralRebaseLiveProjection264 (liveFacts)
open GeneralRebaseMultiSelection263 (ofPlan)
open GeneralSourceState (Output)

def keys (registry : Registry) (root : Occurrence roles) (context : Context) (labels : List Pattern) : List (Nat × Nat) :=
 GeneralNominalOwnerCandidates252.owners (Encoded registry) context.state.seed root.identity
    (GeneralNominalPatersonLineage.mass labels)

def owners (registry : Registry) (root : Occurrence roles) (context : Context) (labels : List Pattern) : List Nat :=
 (keys registry root context labels).map fun pair => GeneralNominalIdentities.pair pair.1 pair.2

def pool (registry : Registry) (root : Occurrence roles) (context : Context) (labels : List Pattern) : List Output :=
 GeneralRebaseSourceRequestPool262.pool (Encoded registry) root
   (GeneralNominalPublicPorts253.names (Encoded registry) context.state.seed (keys registry root context labels))

/-- The concrete formulas for owner keys and output addresses cover every
reachable live state, given the source formation certificate and root labels. -/
theorem covered (registry : Registry) (root : Occurrence roles) (context : Context) (labels : List Pattern)
 (formed : GeneralNominalSourceFormation.InitialSource (Encoded registry) context root)
 (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
 (ground : GeneralNominalGroundAccessibility.GroundRoots context root labels)
 (valid : GeneralNominalCenteredHeadWFSource.Coverage (Encoded registry) context.interpretation)
 (state : State roles) (path : B4Target.Steps ((Boundary roles).Step registry root) (initial context root) state) :
 liveFacts state ⊆ GeneralRebaseUniversalBasis263.basis
    (owners registry root context labels) (pool registry root context labels) := by
 apply GeneralRebaseLiveProjection264.covered
 · intro plan member
   obtain ⟨before,effect,prev,generator,enabled,novel,rfl⟩ :=
     GeneralRebaseRegisteredOwners263.registered_origin (Encoded registry) root (initial context root) rfl state path plan member
   have owner := GeneralNominalOwnerCandidates252.installed_owner_enumerated formed point ground valid
     prev generator enabled novel
   exact List.mem_map.mpr ⟨_,owner,rfl⟩
 · unfold pool
   apply GeneralRebaseSourceRequestPool262.trace_covered (Encoded registry) root context _ _ state path
   intro current prior effect generator enabled novel name member
   exact GeneralNominalPublicPorts253.installed_port_enumerated formed point ground valid prior generator enabled novel name member


/-- Run the concrete driver using a basis computed from this source and
its explicit checked root labels. The semantic probes remain parameters. -/
theorem drive_on_computed (registry : Registry) (root : Occurrence roles) (context : Context) (labels : List Pattern)
 (checked : (Boundary roles).Checked registry)
 (source : (Boundary roles).Initial registry root (initial context root))
 (formed : GeneralNominalSourceFormation.InitialSource (Encoded registry) context root)
 (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
 (ground : GeneralNominalGroundAccessibility.GroundRoots context root labels)
 (valid : GeneralNominalCenteredHeadWFSource.Coverage (Encoded registry) context.interpretation)
 (probeFamily : State roles → GeneralRebaseSourceObserver267.Probes roles)
 (sound : GeneralRebaseConcreteDriver267.SoundFrom registry root (initial context root) checked probeFamily)
 (complete : ∀ state, GeneralRebaseConcreteDriver267.PathFrom registry root (initial context root) state →
   GeneralRebaseObserverCoverage267.Covers registry state root checked (probeFamily state)) :
 ∃ last count,
 GeneralRebaseConcreteDriver267.drive registry root (initial context root) checked source probeFamily sound
    (owners registry root context labels) (pool registry root context labels) (initial context root) .refl =
      .ok (count,last) ∧
 GeneralRebaseDynamicTrace267.Trace registry root checked probeFamily
    (owners registry root context labels) (pool registry root context labels) count (initial context root) last ∧
 GeneralRebaseDynamicRun267.StableProjection registry root (owners registry root context labels)
    (pool registry root context labels) last := by
 refine GeneralRebaseConcreteCorrect267.verified registry root (initial context root) checked source probeFamily sound complete
  (owners registry root context labels) (pool registry root context labels) ?_ (initial context root) .refl
 · intro state path projected proposal listed fact inProposal
   have reachable : B4TargetV8.Reachable (Boundary roles) registry root state := ⟨_,source,path⟩
   unfold GeneralRebaseObserverExact267.observe at listed
   split at listed
   · obtain ⟨after,step,_,subset⟩ := GeneralRebaseObserverSound267.witness registry root state checked reachable
       (probeFamily state) (sound state path) (owners registry root context labels)
       (pool registry root context labels) proposal listed
     exact covered registry root context labels formed point ground valid after (.tail path step) (subset inProposal)
   · cases listed

end Yulang.GeneralRebaseComputedBasis267
