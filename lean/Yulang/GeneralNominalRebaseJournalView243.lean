import Yulang.GeneralNominalRebaseClassView243
import Yulang.GeneralNominalRebasePacketView243
import Yulang.GeneralNominalRebaseObservedSite243
import Yulang.GeneralNominalVersionedMixedRegistry234
import Yulang.GeneralNominalPointSourceBoundary240
import Yulang.GeneralNominalPointErasure240
set_option backward.isDefEq.respectTransparency false
/-! Finite expression readback of the actual mixed source journal. Source
reachability supplies the empty legacy-plan/effect invariant; no legacy
constraints are silently discarded. Alias-class request enumeration retains
its original noncomputable definition. This is not an executable solver. -/
namespace Yulang.GeneralNominalRebaseJournalView243
open Core.PresenceGeneration (CompTerm)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRebaseRawView243 (read)
open GeneralNominalVersionedJournal232 (State)

structure Effect where
 raw : GeneralNominalRebaseRawView243.View
 projection : GeneralNominalRebaseProjectionView243.Report
 historical : GeneralNominalRebaseClassView243.View
 live : GeneralNominalRebaseClassView243.View

def Effect.Holds (effect : Effect) (model : Assignment) : Prop :=
 effect.raw.Models model ∧ effect.projection.Models model ∧ effect.historical.Holds model ∧ effect.live.Holds model

noncomputable def effect (state : State roles) (source : GeneralNominalVersionedJournal232.Effect roles)
 (mapping : Nat → CompTerm Nat) : Effect :=
 ⟨GeneralNominalRebaseRawView243.compile (GeneralNominalVersionedPlans231.privateState source.plan.packet) mapping,
 GeneralNominalRebaseProjectionView243.compile source.plan.packet.context.state mapping (GeneralNominalPacketSupport.report source.plan.packet),
 GeneralNominalRebaseClassView243.compile source.snapshot source.plan.packet.site.occurrence source.plan mapping,
 GeneralNominalRebaseClassView243.compile state.core source.plan.packet.site.occurrence source.plan mapping⟩

theorem effect_exact (state : State roles) (source : GeneralNominalVersionedJournal232.Effect roles)
 (mapping : Nat → CompTerm Nat) (model : Assignment) :
 (effect state source mapping).Holds model ↔
 source.Holds (read mapping model) ∧ source.Live state.core (read mapping model) := by
 unfold effect Effect.Holds GeneralNominalVersionedJournal232.Effect.Holds GeneralNominalVersionedJournal232.Effect.Live GeneralNominalVersionedPlans231.HeadModels
 rw [GeneralNominalRebaseRawView243.compile_exact,GeneralNominalRebaseProjectionView243.compile_exact,
   GeneralNominalRebaseClassView243.compile_exact,GeneralNominalRebaseClassView243.compile_exact]
 constructor
 · rintro ⟨a,b,c,d⟩; exact ⟨⟨⟨a,b⟩,c⟩,d⟩
 · rintro ⟨⟨⟨a,b⟩,c⟩,d⟩; exact ⟨a,b,c,d⟩

structure Journal where
 current : GeneralNominalRebaseRawView243.View
 source : GeneralNominalRebaseRawView243.View
 observed : List (List GeneralNominalRebaseObservedSite243.Argument)
 sites : List GeneralNominalRebaseLiveView243.Site
 packets : List GeneralNominalRebasePacketView243.Packet
 effects : List Effect

def Journal.Models (journal : Journal) (model : Assignment) : Prop :=
 journal.current.Models model ∧ journal.source.Models model ∧
 (∀ arguments ∈ journal.observed, GeneralNominalRebaseObservedSite243.Holds arguments model) ∧
 (∀ site ∈ journal.sites, site.Holds model) ∧
 (∀ packet ∈ journal.packets, packet.Holds model) ∧
 ∀ effect ∈ journal.effects, effect.Holds model

noncomputable def compile (state : State roles) (mapping : Nat → CompTerm Nat) : Journal :=
 ⟨GeneralNominalRebaseRawView243.compile state.core.erased.current.context.state mapping,
 GeneralNominalRebaseRawView243.compile state.core.erased.source.state mapping,
 state.core.erased.current.sites.map (GeneralNominalRebaseObservedSite243.compile · mapping),
 GeneralNominalRebaseLiveView243.compileAll state.core.sites mapping,
 state.plans.map (GeneralNominalRebasePacketView243.compile · mapping),state.effects.map (effect state · mapping)⟩

theorem compile_exact (state : State roles)
 (empty : GeneralNominalVersionedMixedRegistry234.LegacyEmpty state)
 (mapping : Nat → CompTerm Nat) (model : Assignment) :
 (compile state mapping).Models model ↔ GeneralNominalVersionedJournal232.Models state (read mapping model) := by
 unfold Journal.Models compile GeneralNominalVersionedJournal232.Models GeneralNominalVersionedJournal232.Legacy.Models GeneralNominalCenteredHeadMatStepJournal.Models
 rw [GeneralNominalRebaseRawView243.compile_exact,GeneralNominalRebaseRawView243.compile_exact,
   GeneralNominalRebaseObservedSite243.all_exact,GeneralNominalRebaseLiveView243.all_holds]
 simp only [List.forall_mem_map,GeneralNominalRebasePacketView243.compile_exact,effect_exact,
   empty.1,empty.2,List.not_mem_nil,false_implies]
 constructor
 · rintro ⟨a,b,c,d,e,f⟩; exact ⟨⟨a,b,c,d,(fun _ => True.intro),(fun _ => True.intro)⟩,e,f⟩
 · rintro ⟨⟨a,b,c,d,_,_⟩,e,f⟩; exact ⟨a,b,c,d,e,f⟩

theorem source_exact
 (reachable : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state)
 (mapping : Nat → CompTerm Nat) (model : Assignment) :
 (compile state mapping).Models model ↔ GeneralNominalVersionedJournal232.Models state (read mapping model) :=
 compile_exact state (GeneralNominalVersionedMixedRegistry234.reachable_legacy_empty reachable) mapping model

theorem point_source_exact
 (reachable : B4TargetV8.Reachable (GeneralNominalPointSourceBoundary240.boundary roles) registry root state)
 (mapping : Nat → CompTerm Nat) (model : Assignment) :
 (compile state mapping).Models model ↔ GeneralNominalVersionedJournal232.Models state (read mapping model) := by
 apply source_exact (registry := registry) (root := root)
 obtain ⟨initial,source,path⟩ := reachable
 exact ⟨initial,source,GeneralNominalPointErasure240.steps_old path⟩
end Yulang.GeneralNominalRebaseJournalView243
