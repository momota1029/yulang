import Yulang.GeneralDictionaryFootprintCenters227
import Yulang.GeneralDictionaryRequestSeparation227

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryEffectProvenance227
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralDictionarySemanticTrace227 GeneralDictionaryOriginJournal227
open GeneralDictionaryFootprintCenters227 GeneralDictionaryRequestSeparation227
variable {roles : Roles.RoleDecls}

theorem history_prior
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (trace : Footprint registry context root before pool)
    (path : B4Target.Steps (Step registry root) (initial context root) after)
    (retained : before.core.plans ⊆ after.core.plans)
    (two : purpose ≠ 2) (five : purpose ≠ 5)
    (member : fresh context.state.seed invocation declaration purpose owner position ∈ historySources before after.core) :
    fresh context.state.seed invocation declaration purpose owner position ∈ pool := by
  obtain ⟨prior,registered,within⟩ := List.mem_flatMap.mp member
  have old := GeneralDictionaryDefault214ActualEffects.effect_plan_registered trace.path prior registered
  exact registered_input_centers trace prior.plan old
    (delta_reads_center source path prior.plan (retained old) two five within)

theorem install_prior_or_packet
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (trace : Footprint registry context root before pool)
    (generated : GeneralNominalSaturationState.Generated before.core.erased.current root effect.plan.packet.site.occurrence)
    (enabled : Installable registry before effect) (novel : ¬ Committed before effect.plan)
    (two : purpose ≠ 2) (five : purpose ≠ 5)
    (member : fresh context.state.seed invocation declaration purpose owner position ∈ installDelta before effect) :
    fresh context.state.seed invocation declaration purpose owner position ∈ pool ∨
    fresh context.state.seed invocation declaration purpose owner position ∈ GeneralDictionaryReachableRest227.packetSources effect.plan := by
  have path := B4Target.Steps.tail trace.path (Contribution.step (.install effect generated enabled novel))
  rcases List.mem_append.mp member with packetClass | history
  · rcases List.mem_append.mp packetClass with packet | classBody
    · exact Or.inr packet
    · apply Or.inl
      exact frame_input_centers trace (GeneralDictionaryDefaultDepth208.frame enabled)
        (class_reads_center source path effect.plan (List.mem_cons_self ..) two five classBody)
  · exact Or.inl (history_prior source trace path (fun _ h => List.mem_cons_of_mem _ h) two five history)

/-- Raw output equality atoms mention only their two requested targets. -/
theorem output_atoms_separate
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (one : first ∈ state.core.sites) (two : last ∈ state.core.sites)
    (notTwo : purpose ≠ 2) (notFive : purpose ≠ 5) :
    fresh context.state.seed invocation declaration purpose owner position ∉
      (GeneralNominalDemandMerging.outputAtoms first.observed last.observed).flatMap GeneralNominalState.atomSources := by
  intro member
  obtain ⟨atom,present,within⟩ := List.mem_flatMap.mp member
  obtain ⟨a,ha,present⟩ := List.mem_flatMap.mp present
  obtain ⟨b,hb,present⟩ := List.mem_flatMap.mp present
  obtain ⟨rawFirst,recordedFirst,sameFirst⟩ := GeneralDictionaryDefaultTrace208.centered_registered path first one
  obtain ⟨rawLast,recordedLast,sameLast⟩ := GeneralDictionaryDefaultTrace208.centered_registered path last two
  have sepA := raw_target_separate (invocation := invocation) (declaration := declaration) (owner := owner) (position := position) source path notTwo notFive rawFirst recordedFirst a
    (sameFirst.symm ▸ ha)
  have sepB := raw_target_separate (invocation := invocation) (declaration := declaration) (owner := owner) (position := position) source path notTwo notFive rawLast recordedLast b
    (sameLast.symm ▸ hb)
  split at present
  · simp only [GeneralNominalAllocation.equations,List.mem_cons,List.not_mem_nil,or_false] at present
    rcases present with rfl | rfl <;>
      simp [GeneralNominalState.atomSources,GeneralNominalState.typeSources,sepA,sepB] at within
  · cases present

theorem merge_prior
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (trace : Footprint registry context root before pool)
    (generated : GeneralNominalSaturationState.Generated before.core.erased.current root first.occurrence)
    (one : first ∈ before.core.sites) (two : last ∈ before.core.sites)
    (same : SameInputs (Models before) first last)
    (novel : ¬ GeneralNominalSaturationState.Alias before.core.erased.current first.occurrence.identity last.occurrence.identity)
    (notTwo : purpose ≠ 2) (notFive : purpose ≠ 5)
    (member : fresh context.state.seed invocation declaration purpose owner position ∈ mergeDelta before first last) :
    fresh context.state.seed invocation declaration purpose owner position ∈ pool := by
  rcases List.mem_append.mp member with atoms | history
  · exact False.elim (output_atoms_separate source trace.path one two notTwo notFive atoms)
  · exact history_prior source trace
      (.tail trace.path (Contribution.step (.merge first last generated one two same novel)))
      (fun _ h => h) notTwo notFive history

/-- The first protected occurrence of any non-2/5/7 allocated identity is in
an actual installation packet, not a class-body or output-equality contribution.
This deliberately does not assert local packet ownership. -/
theorem first_packet
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (trace : Footprint registry context root state pool)
    (notTwo : purpose ≠ 2) (notFive : purpose ≠ 5) (notSeven : purpose ≠ 7)
    (present : fresh context.state.seed invocation declaration purpose owner position ∈ pool) :
    ∃ before prior, ∃ effect : Effect roles,
      Footprint registry context root before prior ∧
      fresh context.state.seed invocation declaration purpose owner position ∉ prior ∧
      Contribution registry root before (install before effect) (installDelta before effect) ∧
      fresh context.state.seed invocation declaration purpose owner position ∈
        GeneralDictionaryReachableRest227.packetSources effect.plan ∧
      B4Target.Steps (Step registry root) (install before effect) state := by
  obtain ⟨before,after,prior,delta,history,absent,event,member,suffix⟩ := trace.fresh_first source notSeven present
  cases event with
  | administrative | refresh => cases member
  | install effect generated enabled novel =>
      have packet := (install_prior_or_packet source history generated enabled novel notTwo notFive member).resolve_left absent
      exact ⟨before,prior,effect,history,absent,.install effect generated enabled novel,packet,suffix⟩
  | merge first last generated one two same novel =>
      exact False.elim (absent (merge_prior source history generated one two same novel notTwo notFive member))

theorem first_merge_packet
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (trace : Footprint registry context root state pool)
    (mergePurpose : purpose = 0 ∨ purpose = 1)
    (present : fresh context.state.seed invocation declaration purpose owner position ∈ pool) :
    ∃ before prior, ∃ effect : Effect roles,
      Footprint registry context root before prior ∧
      fresh context.state.seed invocation declaration purpose owner position ∉ prior ∧
      Contribution registry root before (install before effect) (installDelta before effect) ∧
      fresh context.state.seed invocation declaration purpose owner position ∈
        GeneralDictionaryReachableRest227.packetSources effect.plan ∧
      B4Target.Steps (Step registry root) (install before effect) state :=
  first_packet source trace (by omega) (by omega) (by omega) present

end Yulang.GeneralDictionaryEffectProvenance227
