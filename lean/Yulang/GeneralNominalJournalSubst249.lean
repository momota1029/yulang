import Yulang.GeneralNominalPacketSubst249
import Yulang.GeneralNominalJournalSupport249
import Yulang.GeneralNominalOrderedRaw248

/-! A finite executable substitution on an already materialized journal.
No alias-class request enumeration is rerun. Exactness uses one readback
assignment throughout all current, source, observed, packet and effect fields.
This is not a source transition or a bound on changing journal bodies. -/
namespace Yulang.GeneralNominalJournalSubst249
open Core.PresenceGeneration (CompTerm)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRebaseRawView243 (read)
open GeneralNominalRebaseJournalView243

def effect (mapping : Nat → CompTerm Nat) (e : Effect) : Effect :=
 ⟨GeneralNominalRebaseViewSubst243.subst e.raw mapping,
 GeneralNominalProjectionSchemaSubst249.report mapping e.projection,
 GeneralNominalPacketSubst249.classView mapping e.historical,
 GeneralNominalPacketSubst249.classView mapping e.live⟩

def subst (mapping : Nat → CompTerm Nat) (journal : Journal) : Journal :=
 ⟨GeneralNominalRebaseViewSubst243.subst journal.current mapping,
 GeneralNominalRebaseViewSubst243.subst journal.source mapping,
 journal.observed.map (fun arguments => arguments.map (GeneralNominalPacketSubst249.observedArgument mapping)),
 journal.sites.map (fun site => site.subst mapping),
 journal.packets.map (GeneralNominalPacketSubst249.packet mapping),
 journal.effects.map (effect mapping)⟩

theorem effect_exact (mapping : Nat → CompTerm Nat) (assignment : Assignment) (e : Effect) :
 (effect mapping e).Holds assignment ↔ e.Holds (read mapping assignment) := by
 simp only [effect,Effect.Holds,GeneralNominalRebaseViewSubst243.exact,
   GeneralNominalProjectionSchemaSubst249.report_exact,GeneralNominalPacketSubst249.class_exact]

theorem models_exact (mapping : Nat → CompTerm Nat) (assignment : Assignment) (journal : Journal) :
 (subst mapping journal).Models assignment ↔ journal.Models (read mapping assignment) := by
 simp only [subst,Journal.Models,GeneralNominalRebaseViewSubst243.exact,List.forall_mem_map,
   GeneralNominalPacketSubst249.observed_exact,GeneralNominalRebaseLiveView243.site_subst,
   GeneralNominalPacketSubst249.packet_exact,effect_exact]

theorem ordered_exact (entries : List (GeneralPresenceDefinitionRewrite244.Entry Nat))
 (assignment : Assignment) (journal : Journal) :
 (subst (GeneralPresenceOrderedSubstitution247.mapping entries) journal).Models assignment ↔
 journal.Models (GeneralPresenceOrderedBlock247.solve CommonNominalFullCarrier.model entries assignment) := by
 rw [models_exact,GeneralNominalOrderedRaw248.read_mapping]

theorem repeated (first last : Nat → CompTerm Nat) (assignment : Assignment) (journal : Journal) :
 (subst last (subst first journal)).Models assignment ↔
 journal.Models (read first (read last assignment)) :=
 (models_exact last assignment (subst first journal)).trans (models_exact first (read last assignment) journal)
end Yulang.GeneralNominalJournalSubst249
