import Yulang.GeneralDictionaryHeadFootprint227

/-! The first protected merge identity enters via raw merge equations or
materialization, never current head-schema reads. The actual install certificate
supplies the needed common-model witness, rather than a new satisfiability axiom. -/
namespace Yulang.GeneralDictionaryFirstPacketTail227
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralDictionarySemanticTrace227 GeneralDictionaryOriginJournal227
variable {roles : Roles.RoleDecls}

def tailSources (plan : Plan roles) : List Nat :=
  GeneralDictionaryReachablePacket226.mergeSources plan ++
    GeneralDictionaryDefaultModeSupport213.schemaSources
      (GeneralDictionaryDefaultTotalFrame212.resolve plan)
      (GeneralNominalCenteredHeadMatPlans.emittedSchema plan) ++
    GeneralDictionaryDefaultPacketSupport213.childSources plan

theorem packet_prior_or_tail
    (trace : Footprint registry context root before pool)
    (enabled : Installable registry before effect)
    (notEight : purpose ≠ 8)
    (member : fresh context.state.seed invocation declaration purpose owner position ∈
      GeneralDictionaryReachableRest227.packetSources effect.plan) :
    fresh context.state.seed invocation declaration purpose owner position ∈ pool ∨
    fresh context.state.seed invocation declaration purpose owner position ∈ tailSources effect.plan := by
  obtain ⟨model,valid,branch,_⟩ := enabled.common
  have schema := (GeneralNominalCenteredHeadMatStepPackets.head_equations branch).2.2
  rcases List.mem_append.mp member with merges | rest
  · exact Or.inr (by simp [tailSources,merges])
  · rcases List.mem_append.mp rest with headEmitted | child
    · rcases List.mem_append.mp headEmitted with head | emitted
      · exact Or.inl (GeneralDictionaryHeadFootprint227.head_mem trace effect.plan
          (GeneralDictionaryDefaultDepth208.frame enabled) model valid schema notEight head)
      · exact Or.inr (by simp [tailSources,emitted])
    · exact Or.inr (by simp [tailSources,child])

/-- First p0/p1 protection is witnessed by an actual enabled installation's
raw merges, emitted total schema, or child support. Local ownership is still open. -/
theorem first_merge_tail
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (trace : Footprint registry context root state pool)
    (mergePurpose : purpose = 0 ∨ purpose = 1)
    (present : fresh context.state.seed invocation declaration purpose owner position ∈ pool) :
    ∃ before prior, ∃ effect : Effect roles,
      Footprint registry context root before prior ∧
      fresh context.state.seed invocation declaration purpose owner position ∉ prior ∧
      Installable registry before effect ∧
      Contribution registry root before (install before effect) (installDelta before effect) ∧
      fresh context.state.seed invocation declaration purpose owner position ∈ tailSources effect.plan ∧
      B4Target.Steps (Step registry root) (install before effect) state := by
  obtain ⟨before,after,prior,delta,history,absent,event,member,suffix⟩ :=
    trace.fresh_first source (by omega) present
  cases event with
  | administrative | refresh => cases member
  | install effect generated enabled novel =>
      have packet := (GeneralDictionaryEffectProvenance227.install_prior_or_packet source history
        generated enabled novel (by omega) (by omega) member).resolve_left absent
      have tail := (packet_prior_or_tail history enabled (by omega) packet).resolve_left absent
      exact ⟨before,prior,effect,history,absent,enabled,.install effect generated enabled novel,tail,suffix⟩
  | merge first last generated one two same novel =>
      exact False.elim (absent (GeneralDictionaryEffectProvenance227.merge_prior source history
        generated one two same novel (by omega) (by omega) member))

end Yulang.GeneralDictionaryFirstPacketTail227
