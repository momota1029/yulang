import Yulang.GeneralNominalArbitraryOwnerFrame250
/-! Finite observations, sites, packets and effects can be added before a
rebase. Their constraints use the SAME assignment as the existing journal.
No claim is made that adding constraints preserves unaugmented solutions. -/
namespace Yulang.GeneralNominalJournalAppend250
open Core.PresenceGeneration PresenceNormalForm
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRebaseJournalView243
open GeneralNominalMaterializedOwnerFrame249 (Frame Models)
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOrderedBlock247
open GeneralPresenceOrderedDependence247 GeneralPresenceOrderedSubstitution247
open GeneralPresenceOrderedRebase247
open GeneralNominalMaterializedSequenceModels249 (PublicModels)
open CommonNominalFullCarrier

structure Delta where
 observed : List (List GeneralNominalRebaseObservedSite243.Argument)
 sites : List GeneralNominalRebaseLiveView243.Site
 packets : List GeneralNominalRebasePacketView243.Packet
 effects : List Effect
 ordinary : List (Atom Nat)

def Delta.Holds (delta : Delta) (assignment : Assignment) : Prop :=
 (∀ args ∈ delta.observed, GeneralNominalRebaseObservedSite243.Holds args assignment) ∧
 (∀ site ∈ delta.sites, site.Holds assignment) ∧
 (∀ packet ∈ delta.packets, packet.Holds assignment) ∧
 (∀ effect ∈ delta.effects, effect.Holds assignment) ∧ All model assignment delta.ordinary

def appendJournal (journal : Journal) (delta : Delta) : Journal :=
 ⟨journal.current,journal.source,journal.observed ++ delta.observed,
 journal.sites ++ delta.sites,journal.packets ++ delta.packets,journal.effects ++ delta.effects⟩

def attach (frame : Frame) (delta : Delta) : Frame :=
 ⟨appendJournal frame.metadata delta,frame.consumers ++ delta.ordinary,frame.definitions⟩

theorem attach_models (frame : Frame) (delta : Delta) (assignment : Assignment) :
 Models (attach frame delta) assignment ↔ Models frame assignment ∧ delta.Holds assignment := by
 simp only [Models,attach,appendJournal,Journal.Models,Delta.Holds,List.forall_mem_append,all_append]
 constructor
 · rintro ⟨⟨a,b,⟨c,cc⟩,⟨d,dd⟩,⟨e,ee⟩,⟨f,ff⟩⟩,⟨g,gg⟩,h⟩
   exact ⟨⟨⟨a,b,c,d,e,f⟩,g,h⟩,cc,dd,ee,ff,gg⟩
 · rintro ⟨⟨⟨a,b,c,d,e,f⟩,g,h⟩,cc,dd,ee,ff,gg⟩
   exact ⟨⟨a,b,⟨c,cc⟩,⟨d,dd⟩,⟨e,ee⟩,⟨f,ff⟩⟩,⟨g,gg⟩,h⟩

def subst (mapping : Nat → CompTerm Nat) (delta : Delta) : Delta :=
 ⟨delta.observed.map (fun args => args.map (GeneralNominalPacketSubst249.observedArgument mapping)),
 delta.sites.map (fun site => site.subst mapping),
 delta.packets.map (GeneralNominalPacketSubst249.packet mapping),
 delta.effects.map (GeneralNominalJournalSubst249.effect mapping),
 delta.ordinary.map (atomSubst mapping)⟩

theorem subst_exact (mapping : Nat → CompTerm Nat) (delta : Delta) (assignment : Assignment) :
 (subst mapping delta).Holds assignment ↔ delta.Holds (GeneralNominalRebaseRawView243.read mapping assignment) := by
 simp only [subst,Delta.Holds,List.forall_mem_map,GeneralNominalPacketSubst249.observed_exact,
   GeneralNominalRebaseLiveView243.site_subst,GeneralNominalPacketSubst249.packet_exact,
   GeneralNominalJournalSubst249.effect_exact,All,atom_exact]
 rfl

theorem rebase_attach (frame : Frame) (delta : Delta) (fresh : List (Entry Nat)) :
 GeneralNominalMaterializedOwnerFrame249.rebase (attach frame delta) fresh =
 attach (GeneralNominalMaterializedOwnerFrame249.rebase frame fresh) (subst (mapping frame.definitions) delta) := by
 cases frame; cases delta
 simp only [GeneralNominalMaterializedOwnerFrame249.rebase,attach,appendJournal,
   GeneralNominalJournalSubst249.subst,subst,rewrite,List.map_append]

theorem snapshot_attach (frame : Frame) (delta : Delta) (raw : List (Entry Nat)) :
 GeneralNominalSnapshotOwner250.update (attach frame delta) raw =
 attach (GeneralNominalSnapshotOwner250.update frame raw) (subst (mapping frame.definitions) delta) :=
 rebase_attach frame delta _

theorem augmented_public_models_iff (frame : Frame) (oldSafe : SafeOrder frame.definitions)
 (delta : Delta) (raw : List (Entry Nat)) (within : TargetsWithin raw frame.definitions)
 (shared : Nat → Prop)
 (privateNames : ∀ name, shared name → ∀ entry ∈ frame.definitions, entry.1 ≠ name)
 (boundary : Assignment) :
 (∃ assignment, Models frame assignment ∧ delta.Holds assignment ∧ Agrees model shared assignment boundary) ↔
 PublicModels (attach (GeneralNominalSnapshotOwner250.update frame raw)
   (subst (mapping frame.definitions) delta)) shared boundary := by
 have result := GeneralNominalArbitraryOwnerFrame250.snapshot_public_models_iff
   (attach frame delta) oldSafe raw within shared privateNames boundary
 rw [snapshot_attach] at result
 simpa only [PublicModels,attach_models,and_assoc] using result
end Yulang.GeneralNominalJournalAppend250
