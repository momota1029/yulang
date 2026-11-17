import Yulang.GeneralDictionaryVersionedInitialPacket233
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryVersionedInitialFrame233
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229
open GeneralDictionaryOptionalInstall229 (plan packet)
open GeneralDictionaryVersionedInitialModel233
open GeneralNominalVersionedCandidates231
open GeneralNominalCenters

noncomputable abbrev before := GeneralNominalVersionedJournal232.initial context root

theorem source_support : GeneralNominalState.sources snapshot ⊆ pool := by decide +kernel

theorem fresh : GeneralNominalVersionedAllocation231.Fresh snapshot registry root.identity packet.bindings := by
  rw [GeneralDictionaryOptionalInstall229.bindings_exact]
  intro key member collision
  change key ∈ [GeneralNominalAggregateVersion231.key root.identity declaration.id 0 0 bindings,
    GeneralNominalAggregateVersion231.key root.identity declaration.id 1 0 bindings,
    GeneralNominalAggregateVersion231.key root.identity declaration.id 0 0 bindings,
    GeneralNominalAggregateVersion231.key root.identity declaration.id 1 0 bindings] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  all_goals exfalso
  all_goals first | exact fresh_outside 0 (source_support collision) | exact fresh_outside 1 (source_support collision)

theorem prepared : Prepared registry context root declaration := by
  refine ⟨source.metadata,⟨source.linked.1,by intro output member; cases member⟩,
    [(0,0)],?_,fresh,?_,extended,GeneralDictionaryVersionedInitialPacket233.head_model⟩
  · decide +kernel
  · rw [GeneralDictionaryOptionalInstall229.report_exact]; exact ⟨rfl,rfl,rfl⟩

theorem frame : GeneralNominalVersionedEvidence231.Frame registry before.core root declaration.id plan :=
  ⟨rfl,rfl,rfl,rfl,List.mem_singleton_self _,List.mem_singleton_self _,List.mem_singleton_self _,rfl,
    by decide +kernel,prepared⟩

theorem children_empty : GeneralNominalVersionedFrame231.children packet = [] := by
  apply List.eq_nil_of_length_eq_zero
  rw [GeneralNominalVersionedFrame231.children_length_eq,GeneralDictionaryOptionalInstall229.children_empty]
  rfl

theorem survivor : Survivor registry context root declaration.id [] :=
  ⟨GeneralDictionaryOptionalInstall229.known,declaration,List.mem_singleton_self _,declaration_checked,
    rfl,rfl,[(0,0)],by decide +kernel,prepared,children_empty.symm⟩

theorem unique : Unique registry context root declaration.id [] := by
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
  unique := children_empty ▸ unique
  ready := GeneralDictionaryOptionalInstall229.ready

noncomputable def installed := GeneralNominalVersionedInstall232.install before effect

theorem class_effects : GeneralNominalVersionedEffects231.ClassEffects before.core root plan extended := by
  apply (GeneralNominalVersionedEffects231.class_effects_iff ..).mpr
  constructor
  · intro output member body found
    cases GeneralDictionaryOptionalInstall229.request_exact member
    have same : body = .explicit ⟨0,0,GeneralDictionaryOptionalExpression229.pattern⟩ := Option.some.inj found |>.symm
    subst body
    intro equation present
    cases List.mem_singleton.mp present
    change CommonNominalFullCarrier.Equivalent (extended 4).1 GeneralDictionaryOptionalOutput229.value
    rw [old_value 4 (by simp [pool])]
    exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩
  · intro first one last two _
    cases GeneralDictionaryOptionalInstall229.request_exact one
    cases GeneralDictionaryOptionalInstall229.request_exact two
    exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩

theorem installation_models : GeneralNominalVersionedInstall232.InstallationModels before effect extended := by
  refine ⟨initial_model,GeneralDictionaryVersionedInitialPacket233.packet_holds,
    ⟨GeneralDictionaryVersionedInitialPacket233.head_model,class_effects⟩,?_,?_,?_⟩
  · exact (GeneralNominalVersionedFrameTransport232.class_effects_iff
      (fun _ => GeneralNominalVersionedTerminal232.requests_iff children_empty)).mpr class_effects
  · intro prior member; cases member
  · intro prior member; cases member

theorem installed_model : GeneralNominalVersionedJournal232.Models installed extended :=
  (GeneralNominalVersionedInstall232.install_models rfl).mpr installation_models

end Yulang.GeneralDictionaryVersionedInitialFrame233
