import Yulang.GeneralRebasePortTicket280
import Yulang.GeneralRebaseCompactRegression280

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 11000000
namespace Yulang.GeneralRebaseTicketLedger280
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State initial)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralRebasePortTicket280 (Ticket issue readRaw readEdges read_sites read_raw read_edges)
open GeneralRebaseRawGraph280 (source_history registered_generated)
open GeneralNominalVersionedMixedTrace235 (generated_registered)
open GeneralRebaseCompactMachine280 (compact)
open GeneralRebaseCompactEdgeInstall279 (replaceEdges)
open GeneralRebaseInstallNovelty279 (Edge)

def catalog (state : State roles) : List (Ticket roles) :=
  state.plans.reverse.flatMap issue

def replayRaw (root : Occurrence roles) (s : State roles) :
    List (GeneralNominalDemandMerging.Site roles) :=
  GeneralNominalDemandMerging.pointSite root :: (catalog s).map (Site.observed ∘ Ticket.read)

def replayCentres (seed : Nat) (root : Occurrence roles) (s : State roles) : List (Site roles) :=
  rootSite seed root :: (catalog s).map Ticket.read

def replayEdges (s : State roles) : List (Edge roles) :=
  s.plans.reverse.flatMap readEdges

structure Exact (seed : Nat) (root : Occurrence roles) (s : State roles) : Prop where
  raw : replayRaw root s = s.core.erased.current.sites
  centered : replayCentres seed root s = s.core.sites
  edges : replayEdges s = s.core.erased.current.edges

theorem append_install {s : State roles} {effect : GeneralNominalVersionedJournal232.Effect roles}
    (exactOld : Exact seed root s) :
    Exact seed root (GeneralNominalVersionedInstall232.install s effect) := by
  refine ⟨?_,?_,?_⟩
  · change GeneralNominalDemandMerging.pointSite root ::
      ((effect.plan :: s.plans).reverse.flatMap issue).map (Site.observed ∘ Ticket.read) =
        s.core.erased.current.sites ++ GeneralNominalVersionedChildren232.rawSites effect.plan
    rw [List.reverse_cons,List.flatMap_append,List.flatMap_singleton,List.map_append,← List.cons_append]
    change replayRaw root s ++ readRaw effect.plan = _
    rw [exactOld.raw,read_raw]
  · change rootSite seed root :: ((effect.plan :: s.plans).reverse.flatMap issue).map Ticket.read =
      s.core.sites ++ GeneralNominalVersionedChildren232.emitted effect.plan
    rw [List.reverse_cons,List.flatMap_append,List.flatMap_singleton,List.map_append,← List.cons_append]
    change replayCentres seed root s ++ (issue effect.plan).map Ticket.read = _
    rw [exactOld.centered,read_sites]
  · change (effect.plan :: s.plans).reverse.flatMap readEdges =
      s.core.erased.current.edges ++ GeneralNominalVersionedChildren232.edges effect.plan
    rw [List.reverse_cons,List.flatMap_append,List.flatMap_singleton]
    change replayEdges s ++ readEdges effect.plan = _
    rw [exactOld.edges,read_edges]

theorem trace {r : Registry} {root : Occurrence roles} {s : State roles}
    (path : B4Target.Steps (Step r root) (initial context root) s) :
    Exact context.state.seed root s := by
  induction path with
  | refl => exact ⟨rfl,rfl,rfl⟩
  | tail path action ih =>
    obtain ⟨focus,generated,atStep⟩ := action
    cases atStep with
    | administrative admin =>
      cases admin with
      | enqueue _ absent =>
        obtain ⟨raw,recorded,same⟩ := generated_registered
          (GeneralNominalVersionedMixedTrace235.steps (GeneralNominalVersionedMixedTrace235.initial context) path).1 generated
        exact False.elim (absent raw recorded same)
      | refresh | equate | reobserve => exact ⟨ih.raw,ih.centered,ih.edges⟩
    | refresh | merge => exact ⟨ih.raw,ih.centered,ih.edges⟩
    | install _ _ _ => exact append_install ih

theorem source_exact {r : Registry} {root : Occurrence roles} {start s : State roles}
    (init : (boundary roles).Initial r root start)
    (path : B4Target.Steps ((boundary roles).Step r root) start s) :
    Exact start.core.erased.current.context.state.seed root s := by
  obtain ⟨legacy,⟨context,_,_,_,_,_,rfl⟩,rfl⟩ := init
  exact trace path

theorem rebuild_edges {s : State roles} (tracked : Exact seed root s) :
    replaceEdges s (replayEdges s) = s := by
  rw [tracked.edges,GeneralRebaseCompactTrust279.replace_self]

theorem compact_replayed {s : State roles} (tracked : Exact seed root s) :
    (compact s).core.erased.current.edges = GeneralRebaseEdgeLedger279.normalize (replayEdges s) := by
  change GeneralRebaseEdgeLedger279.normalize s.core.erased.current.edges = _
  rw [tracked.edges]

end Yulang.GeneralRebaseTicketLedger280
