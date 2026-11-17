import Yulang.GeneralNominalRebaseViewSubst243
import Yulang.GeneralNominalCenters
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalRebaseLiveView243
open Core.PresenceGeneration (CompTerm TyTerm)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRebaseRawView243 (read)
open CommonNominalFullCarrier

structure Argument where
 lower : TyTerm Nat
 upper : TyTerm Nat
 center : TyTerm Nat

def Argument.Holds (argument : Argument) (model : Assignment) : Prop :=
 Subtype (argument.lower.eval CommonNominalFullCarrier.model model) (argument.center.eval CommonNominalFullCarrier.model model) ∧
 Subtype (argument.center.eval CommonNominalFullCarrier.model model) (argument.upper.eval CommonNominalFullCarrier.model model)

structure Output where
 name : Nat
 target : TyTerm Nat

structure Site where
 identity : Nat
 role : Nat
 arguments : List Argument
 outputs : List Output

def Site.Holds (site : Site) (model : Assignment) : Prop :=
 ∀ argument ∈ site.arguments, argument.Holds model

def compile (site : GeneralNominalCenters.Site roles) (mapping : Nat → CompTerm Nat) : Site where
 identity := site.occurrence.identity
 role := site.occurrence.demand.role
 arguments := List.ofFn fun index => ⟨(mapping (site.occurrence.demand.arguments index).1).1,
   (mapping (site.occurrence.demand.arguments index).2).1,(mapping (site.center index)).1⟩
 outputs := site.occurrence.demand.outputs.map fun output => ⟨output.name,(mapping output.target).1⟩

theorem compile_holds (site : GeneralNominalCenters.Site roles) (mapping : Nat → CompTerm Nat) (model : Assignment) :
 (compile site mapping).Holds model ↔ site.Holds (read mapping model) := by
 unfold Site.Holds compile
 constructor
 · intro valid index
   exact valid _ (List.mem_ofFn.mpr ⟨index,rfl⟩)
 · intro valid argument member
   obtain ⟨index,rfl⟩ := List.mem_ofFn.mp member
   exact valid index

theorem center_read (site : GeneralNominalCenters.Site roles) (mapping : Nat → CompTerm Nat) (model : Assignment) (index) :
 (((compile site mapping).arguments[index.val]'(by simpa only [compile,List.length_ofFn] using index.isLt)).center).eval CommonNominalFullCarrier.model model =
 (read mapping model (site.center index)).1 := by
 simp only [compile,List.getElem_ofFn]
 rfl

theorem output_read (site : GeneralNominalCenters.Site roles) (mapping : Nat → CompTerm Nat) (model : Assignment)
 (output : GeneralSourceState.Output) (member : output ∈ site.occurrence.demand.outputs) :
 ∃ translated ∈ (compile site mapping).outputs, translated.name = output.name ∧
   translated.target.eval CommonNominalFullCarrier.model model = (read mapping model output.target).1 :=
 ⟨⟨output.name,(mapping output.target).1⟩,List.mem_map.mpr ⟨output,member,rfl⟩,rfl,rfl⟩

def Argument.subst (argument : Argument) (mapping : Nat → CompTerm Nat) : Argument :=
 ⟨argument.lower.subst mapping,argument.upper.subst mapping,argument.center.subst mapping⟩

def Site.subst (site : Site) (mapping : Nat → CompTerm Nat) : Site :=
 ⟨site.identity,site.role,site.arguments.map (fun argument => argument.subst mapping),
   site.outputs.map (fun output => ⟨output.name,output.target.subst mapping⟩)⟩

theorem argument_subst (argument : Argument) (mapping : Nat → CompTerm Nat) (model : Assignment) :
 (argument.subst mapping).Holds model ↔ argument.Holds (read mapping model) := by
 simp only [Argument.subst,Argument.Holds,TyTerm.eval_subst]
 rfl

theorem site_subst (site : Site) (mapping : Nat → CompTerm Nat) (model : Assignment) :
 (site.subst mapping).Holds model ↔ site.Holds (read mapping model) := by
 simp only [Site.subst,Site.Holds,List.forall_mem_map,argument_subst]

def compileAll (sites : List (GeneralNominalCenters.Site roles)) (mapping : Nat → CompTerm Nat) : List Site :=
 sites.map (compile · mapping)

theorem all_holds (sites : List (GeneralNominalCenters.Site roles)) (mapping : Nat → CompTerm Nat) (model : Assignment) :
 (∀ site ∈ compileAll sites mapping, site.Holds model) ↔ ∀ site ∈ sites, site.Holds (read mapping model) := by
 simp only [compileAll,List.forall_mem_map,compile_holds]

/-- A center may be an old mutable target: translation retains its old RHS,
not the same Nat subsequently assigned the new aggregate. -/
theorem escaped_center (lo hi center : Nat) :
 (Argument.subst ⟨.var lo,.var hi,.var center⟩
   (GeneralNominalRebaseLookup242.substitution [(center,.var 0)])).center = .var 0 := by
 simp [Argument.subst,TyTerm.subst,GeneralNominalRebaseLookup242.substitution,
   GeneralNominalRebaseLookup242.lookup]
end Yulang.GeneralNominalRebaseLiveView243
