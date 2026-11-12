import Yulang.GeneralNominalDemandMerging
import Yulang.GeneralNominalRecursiveBoundary

/-! A shared journal over the existing nominal context. Candidate conditions
retain their original source identities and all projection/materialization
constraints. Occurrences remain available for lossless diagnostics after a
demand merge. No executor is stored or consulted. -/
namespace Yulang.GeneralNominalSaturationState

open GeneralDeclarations
open GeneralNominalCommonBridge (Assignment)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalDemandMerging (Site pointSite)

def SiteHolds (site : Site roles) (model : Assignment) : Prop :=
  ∀ (index : Fin (roles site.occurrence.demand.role).arity) origin,
    site.inputs[index.val]? = some (some origin) →
      (∃ actual, GeneralNominalRecursiveInspection.Observes model origin actual) ∧
      ∀ actual, GeneralNominalRecursiveInspection.Observes model origin actual →
        GeneralNominalCaptureMerges.Fits model (site.occurrence.demand.arguments index) actual

theorem point_holds (root : Occurrence roles) (model : Assignment) : SiteHolds (pointSite root) model := by
  simp only [SiteHolds,pointSite]
  intro index origin recorded
  rw [List.getElem?_ofFn] at recorded
  simp only [dite_eq_left index.isLt] at recorded
  by_cases point : (root.demand.arguments index).1 = (root.demand.arguments index).2
  · have same : GeneralNominalRecursiveInspection.Origin.source (root.demand.arguments index).1 = origin := by
      simpa [point] using recorded
    subst origin
    refine ⟨⟨_,.source _⟩,?_⟩
    intro actual seen
    cases seen
    exact ⟨CommonNominalFullCarrier.subtype_refl _,by rw [← point]; exact CommonNominalFullCarrier.subtype_refl _⟩
  · simp [point] at recorded

structure Packet (roles : Roles.RoleDecls) where
  registry : Registry
  context : GeneralNominalCandidates.Context
  site : Site roles
  declaration : Declaration
  checked : DeclarationChecked registry.constructors roles declaration
  bounds : List (GeneralNominalInspection.Bounds context.state)

def Packet.bindings (packet : Packet roles) : GeneralNominalAllocation.Bindings :=
  GeneralNominalRecursiveInspection.bindings packet.context.state
    (GeneralNominalRecursiveCandidates.report packet.context packet.declaration packet.bounds)

def Packet.children (packet : Packet roles) : List (Occurrence roles) :=
  GeneralNominalAllocation.children packet.context.state packet.registry packet.site.occurrence packet.declaration
    packet.checked packet.bindings

def Packet.privateContext (packet : Packet roles) : GeneralNominalCandidates.Context :=
  ⟨GeneralNominalRecursiveCandidates.privateState packet.registry packet.context packet.site.occurrence
    packet.declaration packet.bounds,packet.context.interpretation⟩

def Packet.Holds (packet : Packet roles) (model : Assignment) : Prop :=
  GeneralNominalRecursiveCandidates.BranchModels packet.registry packet.context packet.site.occurrence
    packet.declaration packet.checked packet.bounds model

/-- Canonical point endpoints identify actual values. Non-point arguments retain
unknown provenance here; arbitrary fitting origins are never accepted. -/
structure Emitted (packet : Packet roles) where
  sites : List (Site roles)
  canonical : sites = packet.children.map pointSite

theorem Emitted.exact {packet : Packet roles} (emitted : Emitted packet) : emitted.sites.map Site.occurrence = packet.children := by
  rw [emitted.canonical]
  simp [pointSite,List.map_map,Function.comp_def]

theorem Emitted.sound {packet : Packet roles} (emitted : Emitted packet) (model : Assignment)
    (_valid : packet.Holds model) (site : Site roles) (member : site ∈ emitted.sites) : SiteHolds site model := by
  rw [emitted.canonical] at member
  obtain ⟨child,_,rfl⟩ := List.mem_map.mp member
  exact point_holds child model

def pointEmitted (packet : Packet roles) : Emitted packet where
  sites := packet.children.map pointSite
  canonical := rfl

structure State (roles : Roles.RoleDecls) where
  context : GeneralNominalCandidates.Context
  packets : List (Packet roles) := []
  sites : List (Site roles) := []
  edges : List (Occurrence roles × Occurrence roles) := []
  aliases : List (Nat × Nat) := []

def Models (state : State roles) (model : Assignment) : Prop :=
  GeneralNominalState.Models state.context.state model ∧
    (∀ packet ∈ state.packets, packet.Holds model) ∧ ∀ site ∈ state.sites, SiteHolds site model

def initial (context : GeneralNominalCandidates.Context) (root : Occurrence roles) : State roles :=
  ⟨context,[],[pointSite root],[],[]⟩

theorem initial_models (context : GeneralNominalCandidates.Context) (root : Occurrence roles) (model : Assignment) :
    Models (initial context root) model ↔ GeneralNominalState.Models context.state model := by
  constructor
  · exact fun valid => valid.1
  · intro valid
    exact ⟨valid,(by intro _ impossible; cases impossible),(by
      intro site member
      have same := List.mem_singleton.mp member; subst site
      exact point_holds root model)⟩

inductive Alias (state : State roles) : Nat → Nat → Prop where
  | refl (identity) : Alias state identity identity
  | edge : (first,last) ∈ state.aliases → Alias state first last
  | symm : Alias state first last → Alias state last first
  | trans : Alias state first middle → Alias state middle last → Alias state first last

def Representative (state : State roles) (site : Site roles) : Prop :=
  ∀ other ∈ state.sites, Alias state site.occurrence.identity other.occurrence.identity →
    site.occurrence.identity ≤ other.occurrence.identity

inductive Generated (state : State roles) (root : Occurrence roles) : Occurrence roles → Prop where
  | root : Generated state root root
  | child : Generated state root parent → (parent,child) ∈ state.edges → Generated state root child
  | alias : Generated state root first.occurrence → first ∈ state.sites → last ∈ state.sites →
      Alias state first.occurrence.identity last.occurrence.identity → Generated state root last.occurrence

theorem generated_trans (first : Generated state root middle) (last : Generated state middle child) :
    Generated state root child := by
  induction last with
  | root => exact first
  | child _ member ih => exact .child ih member
  | alias _ one two equal ih => exact .alias ih one two equal

def install (state : State roles) (packet : Packet roles) (emitted : Emitted packet) : State roles :=
  { state with
    context := packet.privateContext
    packets := packet :: state.packets
    sites := state.sites ++ emitted.sites
    edges := state.edges ++ packet.children.map (fun child => (packet.site.occurrence,child)) }

def merge (state : State roles) (first last : Site roles) : State roles :=
  { state with
    context := ⟨GeneralNominalState.extend state.context.state []
      (GeneralNominalDemandMerging.outputAtoms first last),state.context.interpretation⟩
    aliases := (first.occurrence.identity,last.occurrence.identity) :: state.aliases }

def enqueue (state : State roles) (root : Occurrence roles) : State roles :=
  { state with sites := state.sites ++ [pointSite root] }

theorem enqueue_models (state : State roles) (root : Occurrence roles) (model : Assignment) :
    Models (enqueue state root) model ↔ Models state model := by
  constructor
  · intro valid
    exact ⟨valid.1,valid.2.1,fun site member => valid.2.2 site (List.mem_append_left _ member)⟩
  · intro valid
    refine ⟨valid.1,valid.2.1,?_⟩
    intro site member
    rcases List.mem_append.mp member with old | new
    · exact valid.2.2 site old
    · have same := List.mem_singleton.mp new; subst site
      exact point_holds root model

/-- Required feedback contract for the frozen local candidate predicates.
It is not inferred merely from storing packets. -/
def ContextComplete (state : State roles) : Prop :=
  ∀ model, GeneralNominalState.Models state.context.state model → Models state model

theorem context_complete_models (state : State roles) (complete : ContextComplete state) (model : Assignment) :
    Models state model ↔ GeneralNominalState.Models state.context.state model :=
  ⟨fun valid => valid.1,complete model⟩

def regenerate (state : State roles) (context : GeneralNominalCandidates.Context) : State roles :=
  { state with context := context }

theorem install_models (state : State roles) (packet : Packet roles) (emitted : Emitted packet)
    (same : packet.context = state.context) (model : Assignment) :
    Models (install state packet emitted) model ↔ Models state model ∧ packet.Holds model := by
  constructor
  · rintro ⟨_,packets,sites⟩
    have current := packets packet (by simp [install])
    have original := (GeneralNominalRecursiveCandidates.branch_interval_sound _ _ _ _ _ _ _ current).1
    rw [same] at original
    exact ⟨⟨original,fun p hp => packets p (by simp [install,hp]),
      fun site hs => sites site (List.mem_append_left _ hs)⟩,current⟩
  · rintro ⟨old,current⟩
    refine ⟨current.1,?_,?_⟩
    · intro p member
      rcases List.mem_cons.mp member with rfl | member
      · exact current
      · exact old.2.1 p member
    · intro site member
      rcases List.mem_append.mp member with original | generated
      · exact old.2.2 site original
      · exact emitted.sound model current site generated

theorem merge_models (state : State roles) (first last : Site roles) (model : Assignment) :
    Models (merge state first last) model ↔ Models state model ∧
      PresenceNormalForm.All CommonNominalFullCarrier.model model (GeneralNominalDemandMerging.outputAtoms first last) := by
  change (GeneralNominalState.Models (GeneralNominalState.extend state.context.state [] _) model ∧ _) ↔ _
  rw [GeneralNominalState.extend_models]
  constructor
  · rintro ⟨⟨source,outputs⟩,rest⟩; exact ⟨⟨source,rest⟩,outputs⟩
  · rintro ⟨⟨source,rest⟩,outputs⟩; exact ⟨⟨source,outputs⟩,rest⟩

theorem merge_dictionary_models (state : State roles) (first last : Site roles)
    (same : GeneralNominalDemandMerging.SameInputs (Models state) first last)
    (meaning : GeneralNominalDemandMerging.AssociatedMeaning) (model : Assignment) (valid : Models state model)
    (left : GeneralNominalDemandMerging.DictionaryOutputs meaning model first)
    (right : GeneralNominalDemandMerging.DictionaryOutputs meaning model last) : Models (merge state first last) model :=
  (merge_models state first last model).mpr ⟨valid,
    GeneralNominalDemandMerging.dictionary_outputs_preserved _ _ _ same meaning model valid left right⟩

end Yulang.GeneralNominalSaturationState
