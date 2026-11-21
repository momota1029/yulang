import Yulang.GeneralVersionedSemanticPeer312
import Yulang.GeneralDictionaryOrdinaryTransport

set_option backward.isDefEq.respectTransparency false
/-! A refresh may mention an already-known-to-the-pool name in a reflexive
ordinary atom without restricting any assignment. Sparse semantic support is
therefore preferable to requiring an installed equation for every raw name. -/
namespace Yulang.GeneralVersionedHarmlessRefresh312
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalVersionedMixedObservations233 (Refresh)
open GeneralNominalCandidates (Context)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalVersionedModelSupport237 (Support)
open GeneralNominalSemanticRawFrame236 (sources)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (subtype_refl)
open PresenceNormalForm (Atom All)
variable {roles : Roles.RoleDecls} {s : State roles} {id : Nat}

def atom (n : Nat) : Atom Nat := .tyLe (.var n) (.var n)

def add (ctx : Context) (id : Nat) : Context :=
  ⟨GeneralNominalState.extend ctx.state [] [atom id],ctx.interpretation⟩

theorem reflexive (n : Nat) (m : Assignment) : All CommonNominalFullCarrier.model m [atom n] := by
  intro eq listed
  cases List.mem_singleton.mp listed
  exact subtype_refl _

theorem raw_exact (ctx : Context) (id : Nat) (m : Assignment) :
    GeneralNominalState.Models (add ctx id).state m ↔ GeneralNominalState.Models ctx.state m := by
  rw [show (add ctx id).state = GeneralNominalState.extend ctx.state [] [atom id] from rfl,
    GeneralNominalState.extend_models]
  exact and_iff_left (reflexive id m)

theorem name_used (ctx : Context) (id : Nat) : id ∈ sources (add ctx id).state := by
  simp [sources,GeneralNominalSemanticRawFrame236.erased,add,GeneralNominalState.extend,
    GeneralNominalState.sources,atom,GeneralNominalState.atomSources,GeneralNominalState.typeSources]

theorem included {ctx : Context} {id name : Nat}
    (inside : name ∈ GeneralNominalState.sources (add ctx id).state) :
    name ∈ GeneralNominalState.sources ctx.state ∨ name = id := by
  simpa [add,GeneralNominalState.extend,GeneralNominalState.sources,atom,GeneralNominalState.atomSources,
    GeneralNominalState.typeSources,List.flatMap_append,List.mem_append,or_assoc] using inside

/-- Re-use the original refinement and cache. The extra name must already
belong to the previous source domain; no unsupported new ID is introduced. -/
def certificate (old : Refresh s ctx)
    (knownName : id ∈ GeneralNominalState.sources s.core.erased.current.context.state) :
    Refresh s (add ctx id) where
  refines := {
    base := old.refines.base
    heads := old.refines.heads
    nominals := old.refines.nominals
    ordinary := fun eq member => List.mem_append_left _ (old.refines.ordinary eq member)
    known := old.refines.known
    reserved := fun n h => List.mem_append_left _ (old.refines.reserved n h)
    allocated := old.refines.allocated
    seed := old.refines.seed
    constructors := old.refines.constructors }
  interpretation := old.interpretation
  support := fun n member =>
    (included member).elim (old.support n) (fun eq => eq.symm ▸ knownName)
  constraints := by
    intro m valid
    have original := old.constraints m valid
    exact ⟨original.1,(PresenceNormalForm.all_append ..).mpr ⟨original.2,reflexive id m⟩⟩
  cache := by
    intro obs recorded
    apply old.cache obs
    cases recorded with
    | scalar i scalar proof => exact @GeneralCanonicalObservations.Recorded.scalar ctx.state i scalar proof
    | structural i kind children proof => exact @GeneralCanonicalObservations.Recorded.structural ctx.state i kind children proof
    | nominal i desc proof => exact @GeneralCanonicalObservations.Recorded.nominal ctx.state i desc proof

theorem step (old : Refresh s ctx)
    (knownName : id ∈ GeneralNominalState.sources s.core.erased.current.context.state)
    (generated : GeneralNominalSaturationState.Generated s.core.erased.current root focus)
    (witness : source ∈ GeneralNominalState.sources s.core.erased.current.context.state)
    (unknown : ¬ GeneralNominalState.Known s.core.erased.current.context.state source)
    (nowKnown : GeneralNominalState.Known ctx.state source) :
    Step registry root s (refresh s (add ctx id)) :=
  ⟨focus,generated,.refresh focus _ (certificate old knownName) source witness unknown nowKnown⟩

theorem same_full_models (old : Refresh s ctx)
    (knownName : id ∈ GeneralNominalState.sources s.core.erased.current.context.state) (m : Assignment) :
    Models (refresh s (add ctx id)) m ↔ Models (refresh s ctx) m :=
  (GeneralNominalVersionedMixedObservations233.refresh_models (certificate old knownName)).trans
    (GeneralNominalVersionedMixedObservations233.refresh_models old).symm

theorem retains_support (old : Refresh s ctx)
    (knownName : id ∈ GeneralNominalState.sources s.core.erased.current.context.state)
    (support : Support (refresh s ctx) names) : Support (refresh s (add ctx id)) names :=
  GeneralNominalVersionedModelSupport237.transport (same_full_models old knownName) support

/-- A raw-name scan can now demand a missing historical equation. This is
a conditional obstruction to that scan, not failure of semantic choice. -/
theorem raw_scan_blocked {p : GeneralNominalSaturationState.Packet roles}
    (view : p.context = add ctx id)
    (entry : GeneralNominalFiniteEquationRealization236.Entry)
    (member : entry ∈ GeneralNominalVersionedAggregateLedger236.packetEntries p)
    (target : entry.1 = id)
    (noRecord : ∀ past ∈ s.plans, ∀ old ∈ GeneralNominalVersionedAggregateLedger236.packetEntries past.packet,
      old.1 ≠ id) :
    GeneralVersionedProtectedLookup312.verify (GeneralVersionedProtectedPeer312.semanticPool p)
      (refresh s (add ctx id)) p = false := by
  cases found : GeneralVersionedProtectedLookup312.verify (GeneralVersionedProtectedPeer312.semanticPool p)
      (refresh s (add ctx id)) p with
  | false => rfl
  | true =>
    have covered := (GeneralVersionedProtectedLookup312.verify_iff ..).mp found
    have visible : entry.1 ∈ GeneralVersionedProtectedPeer312.semanticPool p := by
      change entry.1 ∈ sources p.context.state
      rw [view,target]
      exact name_used ctx id
    obtain ⟨prior,stored,old,inside,same⟩ := covered entry member visible
    exact False.elim (noRecord prior stored old inside (same.trans target))

end Yulang.GeneralVersionedHarmlessRefresh312
