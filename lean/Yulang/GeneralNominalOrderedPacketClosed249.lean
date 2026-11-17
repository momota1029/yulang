import Yulang.GeneralNominalOrderedObservationClosed249
import Yulang.GeneralNominalOrderedPacketExpansion249
namespace Yulang.GeneralNominalOrderedPacketClosed249
open Core.PresenceGeneration
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOrderedBlock247
open GeneralPresenceOrderedSubstitution247 GeneralPresenceOrderedDependence247
open GeneralNominalOrderedViewClosed249 GeneralNominalOrderedObservationClosed249
open GeneralPresenceUsedSupport245 (typedReads)
open GeneralNominalCenters (Plan)
variable (old : List (Entry Nat)) (safe : SafeOrder old)
include safe

theorem requirement_closed (declaration : GeneralDeclarations.Declaration)
 (capture : GeneralDeclarationDemands.Capture) (name : Nat) (mode : GeneralNominalMaterialization.Mode) :
 Outside old (GeneralNominalSchemaSupport249.requirementReads
   (GeneralNominalRebaseSchemaView243.requirement declaration capture (mapping old) name mode)) := by
 unfold GeneralNominalRebaseSchemaView243.requirement
 split
 · exact GeneralPresenceOrderedSyntax247.mapping_closed old safe _
 · cases mode with
   | lower => exact GeneralPresenceOrderedSyntax247.mapping_closed old safe _
   | upper => exact GeneralPresenceOrderedSyntax247.mapping_closed old safe _
   | actual =>
     intro n member entry present
     rcases List.mem_append.mp member with member | member
     · exact GeneralPresenceOrderedSyntax247.mapping_closed old safe _ n member entry present
     · exact GeneralPresenceOrderedSyntax247.mapping_closed old safe _ n member entry present

theorem use_closed (plan : Plan roles) (use : GeneralNominalMaterialization.Use) :
 Outside old (GeneralNominalSchemaSupport249.useReads (GeneralNominalRebaseSchemaView243.use plan (mapping old) use)) := by
 unfold GeneralNominalRebaseSchemaView243.use
 split
 · intro n member entry present
   rcases List.mem_append.mp member with member | member
   · exact origin_closed old safe use.origin n member entry present
   · exact GeneralPresenceOrderedSyntax247.mapping_closed old safe _ n member entry present
 · intro n member entry present
   rcases List.mem_append.mp member with member | member
   · exact origin_closed old safe use.origin n member entry present
   · exact requirement_closed old safe _ _ _ _ n member entry present

theorem schema_closed (plan : Plan roles) (schema : GeneralNominalMaterialization.Schema) :
 Outside old (GeneralNominalSchemaSupport249.support (GeneralNominalRebaseSchemaView243.compile plan (mapping old) schema)) := by
 intro n member entry present
 rcases List.mem_append.mp member with tests | uses
 · obtain ⟨test,member,read⟩ := List.mem_flatMap.mp tests
   obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
   exact origin_closed old safe original.1 n read entry present
 · obtain ⟨use,member,read⟩ := List.mem_flatMap.mp uses
   obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
   exact use_closed old safe plan original n read entry present

omit safe in
mutual
 theorem effect_closed (variables : GeneralNominalMaterialization.Mode → Nat → TyTerm Nat)
 (closed : ∀ mode name, Outside old (typedReads (variables mode name)))
 (mode : GeneralNominalMaterialization.Mode) (expression : GeneralNominalRebaseEffectView243.OldExpr) :
 Outside old (GeneralNominalEffectSupport249.support (GeneralNominalRebaseEffectView243.compile variables mode expression)) := by
 cases expression with
 | «variable» name => exact closed mode name
 | primitive constructor arguments => exact effects_closed variables closed mode arguments
 | nominal name arguments => exact effects_closed variables closed .actual arguments
 | record label payload tail =>
   intro n member entry present
   rcases List.mem_append.mp member with member | member
   · exact effect_closed variables closed mode payload n member entry present
   · exact effect_closed variables closed mode tail n member entry present
 | variant tag payload => exact effect_closed variables closed mode payload
 | join payload tail =>
   intro n member entry present
   rcases List.mem_append.mp member with member | member
   · exact effect_closed variables closed mode payload n member entry present
   · exact effect_closed variables closed mode tail n member entry present
 theorem effects_closed (variables : GeneralNominalMaterialization.Mode → Nat → TyTerm Nat)
 (closed : ∀ mode name, Outside old (typedReads (variables mode name)))
 (mode : GeneralNominalMaterialization.Mode) (expressions : List GeneralNominalRebaseEffectView243.OldExpr) :
 Outside old (GeneralNominalEffectSupport249.supports (GeneralNominalRebaseEffectView243.compileMany variables mode expressions)) := by
 cases expressions with
 | nil => intro n member; cases member
 | cons expression rest =>
   intro n member entry present
   rcases List.mem_append.mp member with member | member
   · exact effect_closed variables closed mode expression n member entry present
   · exact effects_closed variables closed mode rest n member entry present
end

theorem variables_closed (plan : Plan roles) (mode : GeneralNominalMaterialization.Mode) (name : Nat) :
 Outside old (typedReads (GeneralNominalRebasePacketView243.variables plan (mapping old) mode name)) := by
 unfold GeneralNominalRebasePacketView243.variables
 split
 · exact GeneralPresenceOrderedSyntax247.mapping_closed old safe _
 · cases mode <;> exact GeneralPresenceOrderedSyntax247.mapping_closed old safe _

theorem equation_closed (plan : Plan roles) (equation : GeneralNominalCenteredHeadMatSchemas.Equation) :
 Outside old (GeneralNominalEffectSupport249.equationReads (GeneralNominalRebasePacketView243.equation plan (mapping old) equation)) := by
 intro n member entry present
 rcases List.mem_append.mp member with target | body
 · exact GeneralPresenceOrderedSyntax247.mapping_closed old safe _ n target entry present
 · exact effect_closed old _ (variables_closed old safe plan) _ _ n body entry present

theorem equations_closed (plan : Plan roles) (schema : GeneralNominalRebasePacketView243.OldSchema) :
 Outside old (GeneralNominalPacketSupport249.equationReads (GeneralNominalRebasePacketView243.equations plan (mapping old) schema)) := by
 intro n member entry present
 obtain ⟨equation,member,read⟩ := List.mem_flatMap.mp member
 obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
 exact equation_closed old safe plan original n read entry present

theorem child_closed (plan : Plan roles) (clause : GeneralDeclarations.Clause) (valid : clause.Signature roles) :
 Outside old (GeneralNominalPacketSupport249.childReads (GeneralNominalRebasePacketView243.child plan (mapping old) clause valid)) := by
 intro n member entry present
 rcases List.mem_append.mp member with site | equations
 · exact live_closed old safe _ n site entry present
 · exact equations_closed old safe plan _ n equations entry present

theorem packet_closed (plan : Plan roles) :
 Outside old (GeneralNominalPacketSupport249.support (GeneralNominalRebasePacketView243.compile plan (mapping old))) := by
 intro n member entry present
 obtain ⟨reads,member,read⟩ := List.mem_flatten.mp member
 simp only [GeneralNominalPacketSupport249.components,GeneralNominalRebasePacketView243.compile,
   List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
 · exact compile_closed old safe _ n read entry present
 · obtain ⟨atom,member,used⟩ := List.mem_flatMap.mp read
   obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
   exact mapped_atom_closed old _ (GeneralPresenceOrderedSyntax247.mapping_closed old safe) original n used entry present
 · exact projection_closed old safe _ _ n read entry present
 · exact live_closed old safe _ n read entry present
 · obtain ⟨argument,member,used⟩ := List.mem_flatMap.mp read
   obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
   exact argument_closed old safe _ _ _ n used entry present
 · exact schema_closed old safe plan _ n read entry present
 · obtain ⟨child,member,used⟩ := List.mem_flatMap.mp read
   obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
   exact child_closed old safe plan _ _ n used entry present
 · exact equations_closed old safe plan _ n read entry present

theorem within_protected (fresh : List (Entry Nat)) (within : TargetsWithin fresh old) (plan : Plan roles) :
 GeneralNominalOrderedPacketExpansion249.Protected plan old fresh := by
 intro n member entry present
 obtain ⟨original,found,equal⟩ := within entry present
 rw [← equal]
 exact packet_closed old safe plan n member original found
end Yulang.GeneralNominalOrderedPacketClosed249
