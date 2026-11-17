import Yulang.GeneralNominalRebaseProjectionView243
import Yulang.GeneralNominalSaturationState
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalRebaseObservedSite243
open GeneralNominalRebaseOriginView243 (Origin Observes)
open GeneralNominalRebaseProjectionView243 (Bounds)
open GeneralNominalRebaseRawView243 (read)
open GeneralNominalCommonBridge (Assignment)
open Core.PresenceGeneration (CompTerm)

structure Argument where
 bounds : Bounds
 origin : Option Origin

def Argument.Holds (argument : Argument) (model : Assignment) : Prop :=
 ∀ origin, argument.origin = some origin →
 (∃ actual, Observes model origin actual) ∧ ∀ actual, Observes model origin actual → argument.bounds.Fits model actual

def compileArgument (site : GeneralNominalDemandMerging.Site roles) (mapping : Nat → CompTerm Nat)
 (index : Fin (roles site.occurrence.demand.role).arity) : Argument :=
 ⟨⟨(mapping (site.occurrence.demand.arguments index).1).1,(mapping (site.occurrence.demand.arguments index).2).1⟩,
 (site.inputs[index.val]?.join).map (GeneralNominalRebaseOriginView243.compile mapping)⟩

def compile (site : GeneralNominalDemandMerging.Site roles) (mapping : Nat → CompTerm Nat) : List Argument :=
 List.ofFn (compileArgument site mapping)

def Holds (arguments : List Argument) (model : Assignment) : Prop :=
 ∀ argument ∈ arguments, argument.Holds model

theorem argument_exact (site : GeneralNominalDemandMerging.Site roles) (mapping : Nat → CompTerm Nat)
 (model : Assignment) (index : Fin (roles site.occurrence.demand.role).arity) :
 (compileArgument site mapping index).Holds model ↔
 ∀ origin, site.inputs[index.val]? = some (some origin) →
 (∃ actual, GeneralNominalRecursiveInspection.Observes (read mapping model) origin actual) ∧
 ∀ actual, GeneralNominalRecursiveInspection.Observes (read mapping model) origin actual →
 GeneralNominalCaptureMerges.Fits (read mapping model) (site.occurrence.demand.arguments index) actual := by
 unfold Argument.Holds compileArgument
 rw [GeneralNominalRebaseProjectionView243.origin_forall]
 cases found : site.inputs[index.val]? with
 | none => simp
 | some value =>
   cases value with
   | none => simp
   | some origin =>
     simp only [Option.join_some,Option.some.injEq,forall_eq',GeneralNominalRebaseOriginView243.compile_exact]
     rfl

theorem compile_exact (site : GeneralNominalDemandMerging.Site roles) (mapping : Nat → CompTerm Nat) (model : Assignment) :
 Holds (compile site mapping) model ↔ GeneralNominalSaturationState.SiteHolds site (read mapping model) := by
 constructor
 · intro valid index origin found
   exact (argument_exact site mapping model index).mp (valid _ (List.mem_ofFn.mpr ⟨index,rfl⟩)) origin found
 · intro valid argument member
   obtain ⟨index,rfl⟩ := List.mem_ofFn.mp member
   exact (argument_exact site mapping model index).mpr (valid index)

theorem all_exact (sites : List (GeneralNominalDemandMerging.Site roles)) (mapping : Nat → CompTerm Nat) (model : Assignment) :
 (∀ arguments ∈ sites.map (compile · mapping), Holds arguments model) ↔
 ∀ site ∈ sites, GeneralNominalSaturationState.SiteHolds site (read mapping model) := by
 simp only [List.forall_mem_map,compile_exact]
end Yulang.GeneralNominalRebaseObservedSite243
