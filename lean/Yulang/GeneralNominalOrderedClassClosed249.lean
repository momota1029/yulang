import Yulang.GeneralNominalOrderedPacketClosed249
import Yulang.GeneralNominalClassSupport249
import Yulang.GeneralNominalObservedSupport249
namespace Yulang.GeneralNominalOrderedClassClosed249
open Core.PresenceGeneration
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOrderedBlock247
open GeneralPresenceOrderedSubstitution247
open GeneralNominalOrderedViewClosed249 GeneralNominalOrderedPacketClosed249
open GeneralNominalOrderedObservationClosed249
open GeneralPresenceUsedSupport245 (typedReads)
open GeneralNominalCenters (Plan)
variable (old : List (Entry Nat)) (safe : SafeOrder old)
include safe

theorem body_variables_closed (plan : Plan roles) (body : GeneralDictionaryAssociatedProvenance.Body)
 (mode : GeneralNominalMaterialization.Mode) (name : Nat) :
 Outside old (typedReads (GeneralNominalRebaseEffectView243.bodyVariables plan (mapping old) body mode name)) := by
 cases body with
 | explicit expression =>
   simp only [GeneralNominalRebaseEffectView243.bodyVariables]
   unfold GeneralNominalRebaseEffectView243.variables
   split
   · exact GeneralPresenceOrderedSyntax247.mapping_closed old safe _
   · cases mode <;> exact GeneralPresenceOrderedSyntax247.mapping_closed old safe _
 | default owner index source => exact GeneralPresenceOrderedSyntax247.mapping_closed old safe _

theorem body_closed (plan : Plan roles) (target : Nat) (body : GeneralDictionaryAssociatedProvenance.Body)
 (equation : GeneralNominalRebaseEffectView243.Equation)
 (found : GeneralNominalRebaseEffectView243.body plan (mapping old) target body = some equation) :
 Outside old (GeneralNominalEffectSupport249.equationReads equation) := by
 obtain ⟨expression,_,rfl⟩ := Option.map_eq_some_iff.mp found
 intro n member entry present
 rcases List.mem_append.mp member with targetRead | expressionRead
 · exact GeneralPresenceOrderedSyntax247.mapping_closed old safe target n targetRead entry present
 · exact effect_closed old _ (body_variables_closed old safe plan body) _ expression n expressionRead entry present

theorem class_closed (state : GeneralNominalCenteredSteps.State roles)
 (root : GeneralSourceDictionaries.Occurrence roles) (plan : Plan roles) :
 Outside old (GeneralNominalClassSupport249.support (GeneralNominalRebaseClassView243.compile state root plan (mapping old))) := by
 intro n member entry present
 rcases List.mem_append.mp member with equations | equalities
 · obtain ⟨equation,member,read⟩ := List.mem_flatMap.mp equations
   obtain ⟨output,_,member⟩ := List.mem_flatMap.mp member
   obtain ⟨body,_,found⟩ := List.mem_flatMap.mp member
   exact body_closed old safe plan output.target body equation (by simpa using found) n read entry present
 · obtain ⟨atom,member,read⟩ := List.mem_flatMap.mp equalities
   obtain ⟨first,_,member⟩ := List.mem_flatMap.mp member
   obtain ⟨last,_,member⟩ := List.mem_flatMap.mp member
   by_cases equal : first.name = last.name
   · simp only [equal,ite_true,List.mem_cons,List.not_mem_nil,or_false] at member
     rcases member with rfl | rfl
     all_goals
       rcases List.mem_append.mp read with read | read
       · exact GeneralPresenceOrderedSyntax247.mapping_closed old safe _ n read entry present
       · exact GeneralPresenceOrderedSyntax247.mapping_closed old safe _ n read entry present
   · simp [equal] at member

theorem observed_argument_closed (site : GeneralNominalDemandMerging.Site roles)
 (index : Fin (roles site.occurrence.demand.role).arity) :
 Outside old (GeneralNominalObservedSupport249.argumentReads
   (GeneralNominalRebaseObservedSite243.compileArgument site (mapping old) index)) := by
 intro n member entry present
 rcases List.mem_append.mp member with bounds | origin
 · rcases List.mem_append.mp bounds with lower | upper
   · exact GeneralPresenceOrderedSyntax247.mapping_closed old safe _ n lower entry present
   · exact GeneralPresenceOrderedSyntax247.mapping_closed old safe _ n upper entry present
 · obtain ⟨ref,found,read⟩ := List.mem_flatMap.mp origin
   have found' : (site.inputs[index.val]?.join).map
       (GeneralNominalRebaseOriginView243.compile (mapping old)) = some ref := by
     simpa only [Option.mem_toList,GeneralNominalRebaseObservedSite243.compileArgument] using found
   obtain ⟨original,_,rfl⟩ := Option.map_eq_some_iff.mp found'
   exact origin_closed old safe original n read entry present

theorem observed_closed (site : GeneralNominalDemandMerging.Site roles) :
 Outside old (GeneralNominalObservedSupport249.support (GeneralNominalRebaseObservedSite243.compile site (mapping old))) := by
 intro n member entry present
 obtain ⟨argument,member,read⟩ := List.mem_flatMap.mp member
 obtain ⟨index,rfl⟩ := List.mem_ofFn.mp member
 exact observed_argument_closed old safe site index n read entry present
end Yulang.GeneralNominalOrderedClassClosed249
