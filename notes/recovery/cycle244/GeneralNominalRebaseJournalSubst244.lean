import Yulang.GeneralNominalRebasePacketSubst244
import Yulang.GeneralNominalRebaseJournalView243
set_option backward.isDefEq.respectTransparency false
/-! Physical finite substitution through every materialized journal consumer.
No saved kernel state is recompiled and no structural metadata is reconstructed. -/
namespace Yulang.GeneralNominalRebaseJournalSubst244
open Core.PresenceGeneration (CompTerm)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRebaseRawView243 (read)
open GeneralNominalRebaseJournalView243 (Effect Journal)
def observed (mapping : Nat → CompTerm Nat) (source : GeneralNominalRebaseObservedSite243.Argument) :
 GeneralNominalRebaseObservedSite243.Argument :=
 ⟨GeneralNominalRebaseProjectionSubst244.bounds mapping source.bounds,
 source.origin.map (GeneralNominalRebaseOriginView243.subst mapping)⟩
theorem observed_exact (mapping : Nat → CompTerm Nat) (source : GeneralNominalRebaseObservedSite243.Argument)
 (model : Assignment) : (observed mapping source).Holds model ↔ source.Holds (read mapping model) := by
 unfold observed GeneralNominalRebaseObservedSite243.Argument.Holds
 simp only [GeneralNominalRebaseProjectionSubst244.option_forall,
 GeneralNominalRebaseOriginView243.subst_exact,GeneralNominalRebaseProjectionSubst244.bounds_exact]
def classView (mapping : Nat → CompTerm Nat) (source : GeneralNominalRebaseClassView243.View) :
 GeneralNominalRebaseClassView243.View :=
 ⟨source.equations.map (GeneralNominalRebasePacketSubst244.equation mapping),
 source.equalities.map (GeneralNominalRebaseRawView243.atom mapping)⟩
theorem class_exact (mapping : Nat → CompTerm Nat) (source : GeneralNominalRebaseClassView243.View)
 (model : Assignment) : (classView mapping source).Holds model ↔ source.Holds (read mapping model) := by
 unfold classView GeneralNominalRebaseClassView243.View.Holds
 simp only [List.forall_mem_map,GeneralNominalRebasePacketSubst244.equation_exact,
 GeneralNominalRebaseRawView243.all_exact]
 rfl
def effect (mapping : Nat → CompTerm Nat) (source : Effect) : Effect :=
 ⟨GeneralNominalRebaseViewSubst243.subst source.raw mapping,
 GeneralNominalRebaseProjectionSubst244.subst source.projection mapping,
 classView mapping source.historical,classView mapping source.live⟩
theorem effect_exact (mapping : Nat → CompTerm Nat) (source : Effect) (model : Assignment) :
 (effect mapping source).Holds model ↔ source.Holds (read mapping model) := by
 simp only [effect,Effect.Holds,GeneralNominalRebaseViewSubst243.exact,
 GeneralNominalRebaseProjectionSubst244.exact,class_exact]
def subst (source : Journal) (mapping : Nat → CompTerm Nat) : Journal :=
 ⟨GeneralNominalRebaseViewSubst243.subst source.current mapping,
 GeneralNominalRebaseViewSubst243.subst source.source mapping,
 source.observed.map (List.map (observed mapping)),
 source.sites.map (fun site => site.subst mapping),
 source.packets.map (fun packet => GeneralNominalRebasePacketSubst244.subst packet mapping),
 source.effects.map (effect mapping)⟩
theorem exact (source : Journal) (mapping : Nat → CompTerm Nat) (model : Assignment) :
 (subst source mapping).Models model ↔ source.Models (read mapping model) := by
 simp only [subst,Journal.Models,GeneralNominalRebaseViewSubst243.exact,List.forall_mem_map,
 GeneralNominalRebaseObservedSite243.Holds,observed_exact,GeneralNominalRebaseLiveView243.site_subst,
 GeneralNominalRebasePacketSubst244.exact,effect_exact]
theorem repeated (source : Journal) (first last : Nat → CompTerm Nat) (model : Assignment) :
 (subst (subst source first) last).Models model ↔ source.Models (read first (read last model)) := by
 rw [exact,exact]
theorem compiled_exact (state : GeneralNominalVersionedJournal232.State roles)
 (empty : GeneralNominalVersionedMixedRegistry234.LegacyEmpty state)
 (first last : Nat → CompTerm Nat) (model : Assignment) :
 (subst (GeneralNominalRebaseJournalView243.compile state first) last).Models model ↔
 GeneralNominalVersionedJournal232.Models state (read first (read last model)) := by
 rw [exact,GeneralNominalRebaseJournalView243.compile_exact state empty]
end Yulang.GeneralNominalRebaseJournalSubst244
