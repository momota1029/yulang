import Yulang.GeneralNominalJournalSubst249
import Yulang.GeneralNominalOrderedViewSyntax248

/-! Literal absorption on a fixed already-materialized journal. Reapplying a
fresh ordered mapping whose targets are inside the old domain adds no syntax.
This says nothing about newly appended metadata or changing live bodies. -/
namespace Yulang.GeneralNominalJournalSubstClosed249
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOrderedBlock247
open GeneralPresenceOrderedSubstitution247 GeneralPresenceOrderedDependence247
open GeneralPresenceOrderedSyntax247
open GeneralNominalProjectionSchemaSubst249
open GeneralNominalPacketSubst249
variable (old fresh : List (Entry Nat)) (safe : SafeOrder old) (within : TargetsWithin fresh old)
include safe within

theorem origin_absorbs (origin : GeneralNominalRebaseOriginView243.Origin) :
 GeneralNominalRebaseOriginView243.subst (mapping fresh)
   (GeneralNominalRebaseOriginView243.subst (mapping old) origin) =
 GeneralNominalRebaseOriginView243.subst (mapping old) origin := by
 induction origin <;> simp_all only [GeneralNominalRebaseOriginView243.subst,type_absorbs old fresh safe within]

theorem bounds_absorbs (b : GeneralNominalRebaseProjectionView243.Bounds) :
 bounds (mapping fresh) (bounds (mapping old) b) = bounds (mapping old) b := by
 cases b
 simp only [bounds,type_absorbs old fresh safe within]

theorem capture_absorbs (c : GeneralNominalRebaseProjectionView243.Capture) :
 capture (mapping fresh) (capture (mapping old) c) = capture (mapping old) c := by
 cases c
 simp only [capture,bounds_absorbs old fresh safe within,Option.map_map,Function.comp_def,
   origin_absorbs old fresh safe within]

theorem report_absorbs (r : GeneralNominalRebaseProjectionView243.Report) :
 report (mapping fresh) (report (mapping old) r) = report (mapping old) r := by
 cases r
 simp only [report,List.map_map,Function.comp_def,bounds_absorbs old fresh safe within,
   capture_absorbs old fresh safe within,origin_absorbs old fresh safe within]

theorem requirement_absorbs (r : GeneralNominalRebaseSchemaView243.Requirement) :
 requirement (mapping fresh) (requirement (mapping old) r) = requirement (mapping old) r := by
 cases r <;> simp only [requirement,type_absorbs old fresh safe within]

theorem use_absorbs (u : GeneralNominalRebaseSchemaView243.Use) :
 use (mapping fresh) (use (mapping old) u) = use (mapping old) u := by
 cases u <;> simp only [use,origin_absorbs old fresh safe within,requirement_absorbs old fresh safe within]

theorem schema_absorbs (s : GeneralNominalRebaseSchemaView243.Schema) :
 schema (mapping fresh) (schema (mapping old) s) = schema (mapping old) s := by
 cases s
 simp only [schema,List.map_map,Function.comp_def,origin_absorbs old fresh safe within,use_absorbs old fresh safe within]

theorem argument_absorbs (a : GeneralNominalRebaseLiveView243.Argument) :
 (a.subst (mapping old)).subst (mapping fresh) = a.subst (mapping old) := by
 cases a
 simp only [GeneralNominalRebaseLiveView243.Argument.subst,type_absorbs old fresh safe within]

theorem site_absorbs (s : GeneralNominalRebaseLiveView243.Site) :
 (s.subst (mapping old)).subst (mapping fresh) = s.subst (mapping old) := by
 cases s
 simp only [GeneralNominalRebaseLiveView243.Site.subst,List.map_map,Function.comp_def,
   argument_absorbs old fresh safe within,type_absorbs old fresh safe within]

omit safe within in
mutual
 theorem effect_absorbs (safe : SafeOrder old) (within : TargetsWithin fresh old) (e : GeneralNominalRebaseEffectView243.Expr) :
 GeneralNominalRebaseEffectView243.subst (mapping fresh) (GeneralNominalRebaseEffectView243.subst (mapping old) e) =
 GeneralNominalRebaseEffectView243.subst (mapping old) e := by
 cases e with
 | source term => simp only [GeneralNominalRebaseEffectView243.subst,type_absorbs old fresh safe within]
 | primitive c args => simp only [GeneralNominalRebaseEffectView243.subst,effects_absorb safe within args]
 | nominal n args => simp only [GeneralNominalRebaseEffectView243.subst,effects_absorb safe within args]
 | record label payload tail => simp only [GeneralNominalRebaseEffectView243.subst,effect_absorbs safe within payload,effect_absorbs safe within tail]
 | variant tag payload => simp only [GeneralNominalRebaseEffectView243.subst,effect_absorbs safe within payload]
 | join first last => simp only [GeneralNominalRebaseEffectView243.subst,effect_absorbs safe within first,effect_absorbs safe within last]
 theorem effects_absorb (safe : SafeOrder old) (within : TargetsWithin fresh old) (es : List GeneralNominalRebaseEffectView243.Expr) :
 GeneralNominalRebaseEffectView243.substMany (mapping fresh) (GeneralNominalRebaseEffectView243.substMany (mapping old) es) =
 GeneralNominalRebaseEffectView243.substMany (mapping old) es := by
 cases es with
 | nil => rfl
 | cons e es => simp only [GeneralNominalRebaseEffectView243.substMany,effect_absorbs safe within e,effects_absorb safe within es]
end

theorem equation_absorbs (e : GeneralNominalRebaseEffectView243.Equation) :
 equation (mapping fresh) (equation (mapping old) e) = equation (mapping old) e := by
 cases e
 simp only [equation,type_absorbs old fresh safe within,effect_absorbs old fresh safe within]

theorem child_absorbs (c : GeneralNominalRebasePacketView243.Child) :
 child (mapping fresh) (child (mapping old) c) = child (mapping old) c := by
 cases c
 simp only [child,site_absorbs old fresh safe within,List.map_map,Function.comp_def,equation_absorbs old fresh safe within]

theorem packet_absorbs (p : GeneralNominalRebasePacketView243.Packet) :
 packet (mapping fresh) (packet (mapping old) p) = packet (mapping old) p := by
 cases p
 simp only [packet,GeneralNominalOrderedViewSyntax248.view_absorbs old fresh safe within,
   List.map_map,Function.comp_def,GeneralNominalOrderedViewSyntax248.atom_absorbs old fresh safe within,
   report_absorbs old fresh safe within,site_absorbs old fresh safe within,argument_absorbs old fresh safe within,
   schema_absorbs old fresh safe within,child_absorbs old fresh safe within,equation_absorbs old fresh safe within]

theorem class_absorbs (v : GeneralNominalRebaseClassView243.View) :
 classView (mapping fresh) (classView (mapping old) v) = classView (mapping old) v := by
 cases v
 simp only [classView,List.map_map,Function.comp_def,equation_absorbs old fresh safe within,
   GeneralNominalOrderedViewSyntax248.atom_absorbs old fresh safe within]

theorem observed_absorbs (a : GeneralNominalRebaseObservedSite243.Argument) :
 observedArgument (mapping fresh) (observedArgument (mapping old) a) = observedArgument (mapping old) a := by
 cases a
 simp only [observedArgument,bounds_absorbs old fresh safe within,Option.map_map,Function.comp_def,
   origin_absorbs old fresh safe within]

theorem journal_effect_absorbs (e : GeneralNominalRebaseJournalView243.Effect) :
 GeneralNominalJournalSubst249.effect (mapping fresh) (GeneralNominalJournalSubst249.effect (mapping old) e) =
 GeneralNominalJournalSubst249.effect (mapping old) e := by
 cases e
 simp only [GeneralNominalJournalSubst249.effect,GeneralNominalOrderedViewSyntax248.view_absorbs old fresh safe within,
   report_absorbs old fresh safe within,class_absorbs old fresh safe within]

theorem journal_absorbs (j : GeneralNominalRebaseJournalView243.Journal) :
 GeneralNominalJournalSubst249.subst (mapping fresh) (GeneralNominalJournalSubst249.subst (mapping old) j) =
 GeneralNominalJournalSubst249.subst (mapping old) j := by
 cases j
 simp only [GeneralNominalJournalSubst249.subst,GeneralNominalOrderedViewSyntax248.view_absorbs old fresh safe within,
   List.map_map,Function.comp_def,observed_absorbs old fresh safe within,site_absorbs old fresh safe within,
   packet_absorbs old fresh safe within,journal_effect_absorbs old fresh safe within]

omit within in
theorem journal_idempotent (j : GeneralNominalRebaseJournalView243.Journal) :
 GeneralNominalJournalSubst249.subst (mapping old) (GeneralNominalJournalSubst249.subst (mapping old) j) =
 GeneralNominalJournalSubst249.subst (mapping old) j :=
 journal_absorbs old old safe (fun entry member => ⟨entry,member,rfl⟩) j
end Yulang.GeneralNominalJournalSubstClosed249
