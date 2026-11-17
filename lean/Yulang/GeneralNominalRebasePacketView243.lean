import Yulang.GeneralNominalRebaseSchemaView243
import Yulang.GeneralNominalRebaseEffectView243
set_option backward.isDefEq.respectTransparency false
/-! Materialized syntax for every component of the existing total packet Holds.
This is a readback compiler, not a successor selection or transition kernel. -/
namespace Yulang.GeneralNominalRebasePacketView243
open Core.PresenceGeneration (CompTerm TyTerm)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRebaseRawView243 (read)
open GeneralNominalCenters (Plan)
open GeneralNominalMaterialization (Mode)
open GeneralNominalRebaseEffectView243 (Equation)
open CommonNominalFullCarrier

abbrev OldSchema := GeneralNominalCenteredHeadMatSchemas.Schema

def variables (plan : Plan roles) (mapping : Nat → CompTerm Nat) (mode : Mode) (name : Nat) : TyTerm Nat :=
 if name ∈ plan.packet.declaration.outputNames then (mapping (GeneralNominalVersionedFrame231.binder plan name)).1
 else match mode with
 | .actual => (mapping (GeneralNominalVersionedFrame231.binder plan name)).1
 | .lower => (mapping ((GeneralNominalVersionedFrame231.capture plan.packet).inputs name).1).1
 | .upper => (mapping ((GeneralNominalVersionedFrame231.capture plan.packet).inputs name).2).1

theorem variables_exact (plan : Plan roles) (mapping : Nat → CompTerm Nat) (model : Assignment) :
 (fun mode name => (variables plan mapping mode name).eval CommonNominalFullCarrier.model model) =
 GeneralNominalVersionedPlans231.variables plan (read mapping model) := by
 funext mode name
 unfold variables GeneralNominalVersionedPlans231.variables
 split <;> cases mode <;> rfl

def equation (plan : Plan roles) (mapping : Nat → CompTerm Nat) (source : GeneralNominalCenteredHeadMatSchemas.Equation) : Equation :=
 ⟨(mapping source.target).1,GeneralNominalRebaseEffectView243.compile (variables plan mapping) source.mode source.expression⟩

def equations (plan : Plan roles) (mapping : Nat → CompTerm Nat) (schema : OldSchema) : List Equation :=
 schema.equations.map (equation plan mapping)

def AllEquations (equations : List Equation) (model : Assignment) : Prop :=
 ∀ equation ∈ equations, equation.Holds model

theorem equation_exact (plan : Plan roles) (mapping : Nat → CompTerm Nat) (model : Assignment)
 (source : GeneralNominalCenteredHeadMatSchemas.Equation) :
 (equation plan mapping source).Holds model ↔ source.Holds (GeneralNominalVersionedPlans231.variables plan (read mapping model)) (read mapping model) := by
 unfold equation GeneralNominalRebaseEffectView243.Equation.Holds GeneralNominalCenteredHeadMatSchemas.Equation.Holds
 rw [GeneralNominalRebaseEffectView243.compile_exact,variables_exact]
 rfl

theorem equations_exact (plan : Plan roles) (mapping : Nat → CompTerm Nat) (model : Assignment) (schema : OldSchema) :
 AllEquations (equations plan mapping schema) model ↔ schema.Holds (GeneralNominalVersionedPlans231.variables plan (read mapping model)) (read mapping model) := by
 simp only [AllEquations,equations,List.forall_mem_map,equation_exact,GeneralNominalCenteredHeadMatSchemas.Schema.Holds]

def names (plan : Plan roles) : List Nat :=
 plan.packet.declaration.inputNames ++ plan.packet.declaration.requirements.flatMap
 (fun clause => GeneralDeclarationPatterns.variablesArgs (GeneralDeclarationPatterns.normalizeArgs clause.arguments))

theorem names_exact (plan : Plan roles) (name : Nat) : name ∈ names plan ↔
 name ∈ plan.packet.declaration.inputNames ∨ GeneralNominalSharedCaptures.Needed plan.packet name := by
 simp only [names,List.mem_append,List.mem_flatMap,GeneralNominalSharedCaptures.Needed]

def binder (plan : Plan roles) (mapping : Nat → CompTerm Nat) (name : Nat) : GeneralNominalRebaseLiveView243.Argument :=
 ⟨(mapping ((GeneralNominalVersionedFrame231.capture plan.packet).inputs name).1).1,
  (mapping ((GeneralNominalVersionedFrame231.capture plan.packet).inputs name).2).1,
  (mapping (GeneralNominalVersionedFrame231.binder plan name)).1⟩

theorem binders_exact (plan : Plan roles) (mapping : Nat → CompTerm Nat) (model : Assignment) :
 (∀ argument ∈ (names plan).map (binder plan mapping), argument.Holds model) ↔
 ∀ name, name ∈ plan.packet.declaration.inputNames ∨ GeneralNominalSharedCaptures.Needed plan.packet name →
 GeneralNominalCaptureMerges.Fits (read mapping model) ((GeneralNominalVersionedFrame231.capture plan.packet).inputs name)
 ((read mapping model) (GeneralNominalVersionedFrame231.binder plan name)).1 := by
 simp only [List.forall_mem_map,names_exact]
 rfl

structure Child where
 site : GeneralNominalRebaseLiveView243.Site
 equations : List Equation

def Child.Holds (child : Child) (model : Assignment) : Prop := child.site.Holds model ∧ AllEquations child.equations model

def child (plan : Plan roles) (mapping : Nat → CompTerm Nat) (clause : GeneralDeclarations.Clause) (valid : clause.Signature roles) : Child :=
 ⟨GeneralNominalRebaseLiveView243.compile (GeneralNominalVersionedFrame231.childSite plan clause valid) mapping,
 equations plan mapping (GeneralNominalVersionedPlans231.childSchema plan clause valid)⟩

def children (plan : Plan roles) (mapping : Nat → CompTerm Nat) : List Child :=
 plan.packet.declaration.requirements.attach.map fun clause => child plan mapping clause.val
 (plan.packet.checked.signature.2.2.2 clause.val clause.property)

theorem child_exact (plan : Plan roles) (mapping : Nat → CompTerm Nat) (model : Assignment)
 (clause : GeneralDeclarations.Clause) (valid : clause.Signature roles) :
 (child plan mapping clause valid).Holds model ↔
 (GeneralNominalVersionedFrame231.childSite plan clause valid).Holds (read mapping model) ∧
 (GeneralNominalVersionedPlans231.childSchema plan clause valid).Holds
   (GeneralNominalVersionedPlans231.variables plan (read mapping model)) (read mapping model) :=
 and_congr (GeneralNominalRebaseLiveView243.compile_holds _ _ _) (equations_exact _ _ _ _)

theorem children_exact (plan : Plan roles) (mapping : Nat → CompTerm Nat) (model : Assignment) :
 (∀ next ∈ children plan mapping, next.Holds model) ↔
 ∀ clause ∈ plan.packet.declaration.requirements, ∀ valid : clause.Signature roles,
 (GeneralNominalVersionedFrame231.childSite plan clause valid).Holds (read mapping model) ∧
 (GeneralNominalVersionedPlans231.childSchema plan clause valid).Holds
   (GeneralNominalVersionedPlans231.variables plan (read mapping model)) (read mapping model) := by
 simp only [children,List.forall_mem_map,child_exact]
 constructor
 · intro held clause member valid
   exact held ⟨clause,member⟩ (List.mem_attach _ _)
 · intro held clause _
   exact held clause.val clause.property _

def ordinary (plan : Plan roles) : List (PresenceNormalForm.Atom Nat) :=
 GeneralNominalAllocation.cross plan.packet.bindings ++
 GeneralNominalVersionedAllocation231.merges plan.packet.context.state plan.packet.registry
   plan.packet.site.occurrence.identity plan.packet.declaration plan.packet.bindings ++
 GeneralNominalRecursiveInspection.selfChecks plan.packet.context.state (GeneralNominalPacketSupport.report plan.packet)

theorem ordinary_exact (plan : Plan roles) (model : Assignment) :
 PresenceNormalForm.All CommonNominalFullCarrier.model model (ordinary plan) ↔ GeneralNominalVersionedPlans231.Ordinary plan.packet model := by
 unfold ordinary GeneralNominalVersionedPlans231.Ordinary
 rw [PresenceNormalForm.all_append,PresenceNormalForm.all_append,GeneralNominalAllocation.cross_exact]
 exact and_assoc

structure Packet where
 raw : GeneralNominalRebaseRawView243.View
 ordinary : List (PresenceNormalForm.Atom Nat)
 projection : GeneralNominalRebaseProjectionView243.Report
 input : GeneralNominalRebaseLiveView243.Site
 binders : List GeneralNominalRebaseLiveView243.Argument
 head : GeneralNominalRebaseSchemaView243.Schema
 children : List Child
 outputs : List Equation

def Packet.Holds (packet : Packet) (model : Assignment) : Prop :=
 packet.raw.Models model ∧ PresenceNormalForm.All CommonNominalFullCarrier.model model packet.ordinary ∧
 packet.projection.Models model ∧ packet.input.Holds model ∧
 (∀ argument ∈ packet.binders, argument.Holds model) ∧ packet.head.Holds model ∧
 (∀ child ∈ packet.children, child.Holds model) ∧ AllEquations packet.outputs model

def compile (plan : Plan roles) (mapping : Nat → CompTerm Nat) : Packet :=
 ⟨GeneralNominalRebaseRawView243.compile plan.packet.context.state mapping,
 (ordinary plan).map (GeneralNominalRebaseRawView243.atom mapping),
 GeneralNominalRebaseProjectionView243.compile plan.packet.context.state mapping (GeneralNominalPacketSupport.report plan.packet),
 GeneralNominalRebaseLiveView243.compile plan.input mapping,(names plan).map (binder plan mapping),
 GeneralNominalRebaseSchemaView243.compile plan mapping plan.headSchema,children plan mapping,
 equations plan mapping (GeneralNominalVersionedPlans231.emittedSchema plan)⟩

theorem compile_exact (plan : Plan roles) (mapping : Nat → CompTerm Nat) (model : Assignment) :
 (compile plan mapping).Holds model ↔ GeneralNominalVersionedPlans231.Holds plan (read mapping model) := by
 unfold Packet.Holds compile
 rw [GeneralNominalRebaseRawView243.compile_exact,GeneralNominalRebaseRawView243.all_exact,
   ordinary_exact,GeneralNominalRebaseProjectionView243.compile_exact,
   GeneralNominalRebaseLiveView243.compile_holds,binders_exact,
   GeneralNominalRebaseSchemaView243.compile_exact,children_exact,equations_exact]
 unfold GeneralNominalVersionedPlans231.Holds GeneralNominalVersionedPlans231.Inputs GeneralNominalVersionedPlans231.Outputs
 constructor
 · rintro ⟨raw,ordinary,projection,input,binders,head,children,outputs⟩
   exact ⟨raw,⟨ordinary,projection,input,binders,head,fun equation member _ => outputs equation member,children⟩,outputs⟩
 · rintro ⟨raw,⟨ordinary,projection,input,binders,head,_,children⟩,outputs⟩
   exact ⟨raw,ordinary,projection,input,binders,head,children,outputs⟩
end Yulang.GeneralNominalRebasePacketView243
