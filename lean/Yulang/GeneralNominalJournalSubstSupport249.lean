import Yulang.GeneralNominalJournalSubstClosed249
import Yulang.GeneralNominalOrderedViewClosed249
import Yulang.GeneralNominalJournalSupport249

/-! Direct typed-support closure of arbitrary materialized journal substitution.
Unlike compiled-journal closure this covers every later finite subst stage. -/
namespace Yulang.GeneralNominalJournalSubstSupport249
open Core.PresenceGeneration
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOrderedBlock247
open GeneralPresenceOrderedSubstitution247 GeneralPresenceOrderedDependence247
open GeneralNominalOrderedViewClosed249
open GeneralNominalProjectionSchemaSubst249 GeneralNominalPacketSubst249
open GeneralPresenceUsedSupport245 (typedReads)
variable (old : List (Entry Nat)) (safe : SafeOrder old)
include safe

omit safe in
theorem outside_append (a b : List Nat) : Outside old (a ++ b) ↔ Outside old a ∧ Outside old b := by
 simp only [Outside,List.mem_append,or_imp,forall_and]
omit safe in
theorem outside_flatMap (xs : List α) (f : α → List Nat) :
 Outside old (xs.flatMap f) ↔ ∀ x ∈ xs, Outside old (f x) := by
 constructor
 · intro closed x member n read
   exact closed n (List.mem_flatMap.mpr ⟨x,member,read⟩)
 · intro closed n member
   obtain ⟨x,member,read⟩ := List.mem_flatMap.mp member
   exact closed x member n read

theorem type_closed (term : TyTerm Nat) : Outside old (typedReads (term.subst (mapping old))) :=
 GeneralPresenceOrderedExpansion249.type_rewrite_closed old safe term

theorem origin_closed (o : GeneralNominalRebaseOriginView243.Origin) :
 Outside old (GeneralNominalOriginSupport249.support (GeneralNominalRebaseOriginView243.subst (mapping old) o)) := by
 induction o with
 | source term => exact type_closed old safe term
 | nominal p n i ih => exact ih
 | structural p s i ih => exact ih

theorem bounds_closed (b : GeneralNominalRebaseProjectionView243.Bounds) :
 Outside old (GeneralNominalProjectionSupport249.boundsReads (bounds (mapping old) b)) :=
 (outside_append old _ _).mpr ⟨type_closed old safe _,type_closed old safe _⟩

theorem optional_origin_closed (o : Option GeneralNominalRebaseOriginView243.Origin) :
 Outside old (GeneralNominalProjectionSupport249.originReads
   (o.map (GeneralNominalRebaseOriginView243.subst (mapping old)))) := by
 cases o with
 | none => intro n member; cases member
 | some o =>
   intro n member entry present
   simp only [GeneralNominalProjectionSupport249.originReads,Option.map_some,Option.toList_some,List.flatMap_cons,
     List.flatMap_nil,List.append_nil] at member
   exact origin_closed old safe o n member entry present

theorem capture_closed (c : GeneralNominalRebaseProjectionView243.Capture) :
 Outside old (GeneralNominalProjectionSupport249.captureReads (capture (mapping old) c)) :=
 (outside_append old _ _).mpr ⟨bounds_closed old safe _,optional_origin_closed old safe _⟩

theorem report_closed (r : GeneralNominalRebaseProjectionView243.Report) :
 Outside old (GeneralNominalProjectionSupport249.support (report (mapping old) r)) := by
 apply (outside_append old _ _).mpr
 constructor
 · apply (outside_append old _ _).mpr
   constructor
   · apply (outside_flatMap old _ _).mpr
     intro a member
     obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
     exact (outside_append old _ _).mpr ⟨origin_closed old safe _,bounds_closed old safe _⟩
   · apply (outside_flatMap old _ _).mpr
     intro t member
     obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
     exact origin_closed old safe _
 · apply (outside_flatMap old _ _).mpr
   intro c member
   obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
   exact capture_closed old safe _

theorem argument_closed (a : GeneralNominalRebaseLiveView243.Argument) :
 Outside old (GeneralNominalLiveSupport249.argumentReads (a.subst (mapping old))) :=
 (outside_append old _ _).mpr ⟨(outside_append old _ _).mpr
   ⟨type_closed old safe _,type_closed old safe _⟩,type_closed old safe _⟩

theorem site_closed (site : GeneralNominalRebaseLiveView243.Site) :
 Outside old (GeneralNominalLiveSupport249.support (site.subst (mapping old))) := by
 apply (outside_append old _ _).mpr
 constructor
 · apply (outside_flatMap old _ _).mpr
   intro a member
   obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
   exact argument_closed old safe _
 · apply (outside_flatMap old _ _).mpr
   intro output member
   obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
   exact type_closed old safe _

theorem requirement_closed (r : GeneralNominalRebaseSchemaView243.Requirement) :
 Outside old (GeneralNominalSchemaSupport249.requirementReads (requirement (mapping old) r)) := by
 cases r with
 | equal term => exact type_closed old safe _
 | interval lo hi => exact (outside_append old _ _).mpr ⟨type_closed old safe _,type_closed old safe _⟩

theorem use_closed (u : GeneralNominalRebaseSchemaView243.Use) :
 Outside old (GeneralNominalSchemaSupport249.useReads (use (mapping old) u)) := by
 cases u with
 | same a b => exact (outside_append old _ _).mpr ⟨origin_closed old safe _,origin_closed old safe _⟩
 | observed o r => exact (outside_append old _ _).mpr ⟨origin_closed old safe _,requirement_closed old safe _⟩

theorem schema_closed (s : GeneralNominalRebaseSchemaView243.Schema) :
 Outside old (GeneralNominalSchemaSupport249.support (schema (mapping old) s)) := by
 apply (outside_append old _ _).mpr
 constructor
 · apply (outside_flatMap old _ _).mpr
   intro t member
   obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
   exact origin_closed old safe _
 · apply (outside_flatMap old _ _).mpr
   intro u member
   obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
   exact use_closed old safe _

omit safe in
mutual
 theorem effect_closed (safe : SafeOrder old) (e : GeneralNominalRebaseEffectView243.Expr) :
 Outside old (GeneralNominalEffectSupport249.support (GeneralNominalRebaseEffectView243.subst (mapping old) e)) := by
 cases e with
 | source term => exact type_closed old safe _
 | primitive c es => exact effects_closed safe es
 | nominal n es => exact effects_closed safe es
 | record l a b => exact (outside_append old _ _).mpr ⟨effect_closed safe a,effect_closed safe b⟩
 | variant t a => exact effect_closed safe a
 | join a b => exact (outside_append old _ _).mpr ⟨effect_closed safe a,effect_closed safe b⟩
 theorem effects_closed (safe : SafeOrder old) (es : List GeneralNominalRebaseEffectView243.Expr) :
 Outside old (GeneralNominalEffectSupport249.supports (GeneralNominalRebaseEffectView243.substMany (mapping old) es)) := by
 cases es with
 | nil => intro n member; cases member
 | cons e es => exact (outside_append old _ _).mpr ⟨effect_closed safe e,effects_closed safe es⟩
end

theorem equation_closed (e : GeneralNominalRebaseEffectView243.Equation) :
 Outside old (GeneralNominalEffectSupport249.equationReads (equation (mapping old) e)) :=
 (outside_append old _ _).mpr ⟨type_closed old safe _,effect_closed old safe _⟩

theorem equations_closed (es : List GeneralNominalRebaseEffectView243.Equation) :
 Outside old (GeneralNominalPacketSupport249.equationReads (es.map (equation (mapping old)))) := by
 apply (outside_flatMap old _ _).mpr
 intro e member
 obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
 exact equation_closed old safe _

theorem child_closed (c : GeneralNominalRebasePacketView243.Child) :
 Outside old (GeneralNominalPacketSupport249.childReads (child (mapping old) c)) :=
 (outside_append old _ _).mpr ⟨site_closed old safe _,equations_closed old safe _⟩

theorem packet_closed (p : GeneralNominalRebasePacketView243.Packet) :
 Outside old (GeneralNominalPacketSupport249.support (packet (mapping old) p)) := by
 intro n member entry present
 obtain ⟨reads,member,read⟩ := List.mem_flatten.mp member
 simp only [GeneralNominalPacketSupport249.components,packet,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
 · exact view_closed old safe _ n read entry present
 · exact GeneralPresenceOrderedExpansion249.rewrite_closed old safe _ n read entry present
 · exact report_closed old safe _ n read entry present
 · exact site_closed old safe _ n read entry present
 · obtain ⟨a,member,used⟩ := List.mem_flatMap.mp read
   obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
   exact argument_closed old safe _ n used entry present
 · exact schema_closed old safe _ n read entry present
 · obtain ⟨c,member,used⟩ := List.mem_flatMap.mp read
   obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
   exact child_closed old safe _ n used entry present
 · exact equations_closed old safe _ n read entry present

theorem class_closed (v : GeneralNominalRebaseClassView243.View) :
 Outside old (GeneralNominalClassSupport249.support (classView (mapping old) v)) :=
 (outside_append old _ _).mpr ⟨equations_closed old safe _,
   GeneralPresenceOrderedExpansion249.rewrite_closed old safe _⟩

theorem observed_closed (a : GeneralNominalRebaseObservedSite243.Argument) :
 Outside old (GeneralNominalObservedSupport249.argumentReads (observedArgument (mapping old) a)) :=
 (outside_append old _ _).mpr ⟨bounds_closed old safe _,optional_origin_closed old safe _⟩

theorem journal_effect_closed (e : GeneralNominalRebaseJournalView243.Effect) :
 Outside old (GeneralNominalJournalSupport249.effectReads (GeneralNominalJournalSubst249.effect (mapping old) e)) := by
 intro n member entry present
 obtain ⟨reads,member,read⟩ := List.mem_flatten.mp member
 simp only [GeneralNominalJournalSupport249.effectComponents,GeneralNominalJournalSubst249.effect,
   List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl | rfl
 · exact view_closed old safe _ n read entry present
 · exact report_closed old safe _ n read entry present
 · exact class_closed old safe _ n read entry present
 · exact class_closed old safe _ n read entry present

theorem journal_closed (j : GeneralNominalRebaseJournalView243.Journal) :
 Outside old (GeneralNominalJournalSupport249.support (GeneralNominalJournalSubst249.subst (mapping old) j)) := by
 intro n member entry present
 obtain ⟨reads,member,read⟩ := List.mem_flatten.mp member
 simp only [GeneralNominalJournalSupport249.components,GeneralNominalJournalSubst249.subst,
   List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl | rfl | rfl | rfl
 · exact view_closed old safe _ n read entry present
 · exact view_closed old safe _ n read entry present
 · obtain ⟨args,member,used⟩ := List.mem_flatMap.mp read
   obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
   obtain ⟨a,member,used⟩ := List.mem_flatMap.mp used
   obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
   exact observed_closed old safe _ n used entry present
 · obtain ⟨s,member,used⟩ := List.mem_flatMap.mp read
   obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
   exact site_closed old safe _ n used entry present
 · obtain ⟨p,member,used⟩ := List.mem_flatMap.mp read
   obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
   exact packet_closed old safe _ n used entry present
 · obtain ⟨e,member,used⟩ := List.mem_flatMap.mp read
   obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
   exact journal_effect_closed old safe _ n used entry present

theorem within_protected (fresh : List (Entry Nat)) (within : TargetsWithin fresh old)
 (j : GeneralNominalRebaseJournalView243.Journal) :
 ∀ n ∈ GeneralNominalJournalSupport249.support (GeneralNominalJournalSubst249.subst (mapping old) j),
   ∀ entry ∈ fresh, entry.1 ≠ n := by
 intro n member entry present
 obtain ⟨original,found,equal⟩ := within entry present
 rw [← equal]
 exact journal_closed old safe j n member original found
end Yulang.GeneralNominalJournalSubstSupport249
