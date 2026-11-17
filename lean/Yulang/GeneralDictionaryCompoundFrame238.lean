import Yulang.GeneralDictionaryCompoundVersionedPacket238
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryCompoundFrame238
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryCompoundSource238
open GeneralDictionaryCompoundPacket238 (plan packet)
open GeneralDictionaryCompoundVersionedModel238
open GeneralNominalVersionedCandidates231
open GeneralNominalCenters

noncomputable abbrev before := GeneralNominalVersionedJournal232.initial context root

theorem source_support : GeneralNominalState.sources snapshot ⊆ pool := by decide +kernel

theorem fresh : GeneralNominalVersionedAllocation231.Fresh snapshot registry root.identity packet.bindings := by
  intro key _ collision
  have high := GeneralNominalIdentities.source_above_seed snapshot.seed key
  have low := source_bound _ collision
  change 4 < GeneralNominalIdentities.source snapshot.seed key at high
  omega

theorem prepared : Prepared registry context root declaration := by
  refine ⟨source.metadata,⟨source.linked.1,by intro output member; cases member⟩,
    [(0,0)],?_,fresh,?_,extended,GeneralDictionaryCompoundVersionedPacket238.head_model⟩
  · decide +kernel
  · rw [GeneralDictionaryCompoundPacket238.report_exact]; exact ⟨rfl,rfl,rfl⟩

theorem frame : GeneralNominalVersionedEvidence231.Frame registry before.core root declaration.id plan :=
  ⟨rfl,rfl,rfl,rfl,List.mem_singleton_self _,List.mem_singleton_self _,List.mem_singleton_self _,rfl,
    by decide +kernel,prepared⟩

theorem survivor : Survivor registry context root declaration.id (GeneralNominalVersionedFrame231.children packet) :=
  ⟨GeneralDictionaryCompoundPacket238.known,declaration,List.mem_singleton_self _,declaration_checked,
    rfl,rfl,[(0,0)],by decide +kernel,prepared,rfl⟩

theorem unique : Unique registry context root declaration.id (GeneralNominalVersionedFrame231.children packet) := by
  refine ⟨survivor,?_⟩
  intro key kids found
  have copy := found
  obtain ⟨_,d,visible,_,identity,_⟩ := found
  cases List.mem_singleton.mp visible
  have same : key = declaration.id := identity.symm
  subst key
  exact ⟨rfl,survivor_children_functional checked copy survivor⟩

noncomputable def effect : GeneralNominalVersionedJournal232.Effect roles where
  registry := registry
  snapshot := before.core
  plan := plan
  frame := frame
  unique := unique
  ready := GeneralDictionaryCompoundPacket238.ready

noncomputable def installed := GeneralNominalVersionedInstall232.install before effect

theorem class_effects : GeneralNominalVersionedEffects231.ClassEffects before.core root plan extended := by
  apply (GeneralNominalVersionedEffects231.class_effects_iff ..).mpr
  constructor
  · intro output member body found
    cases GeneralDictionaryCompoundPacket238.request_exact member
    have same : body = .explicit ⟨0,0,GeneralDictionaryOptionalExpression229.pattern⟩ := Option.some.inj found |>.symm
    subst body
    intro equation present
    cases List.mem_singleton.mp present
    change CommonNominalFullCarrier.Equivalent (extended 4).1 GeneralDictionaryOptionalOutput229.value
    rw [old_value 4 (by simp [pool])]
    unfold baseModel
    rw [GeneralDictionaryCompoundModel238.old_value 4 (by simp [GeneralDictionaryCompoundModel238.pool])]
    exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩
  · intro first one last two _
    cases GeneralDictionaryCompoundPacket238.request_exact one
    cases GeneralDictionaryCompoundPacket238.request_exact two
    exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩


end Yulang.GeneralDictionaryCompoundFrame238
