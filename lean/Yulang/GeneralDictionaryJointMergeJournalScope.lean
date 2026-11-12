import Yulang.GeneralDictionaryJointMergeExample
import Yulang.GeneralDictionaryRecursiveObstruction

/-! A manually populated scalar-output journal with no support facts is not
source-formed. This concerns the missing provenance, not merge correctness. -/
namespace Yulang.GeneralDictionaryJointMergeJournalScope
open GeneralDictionaryJointMergeExample
open GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalSupportSteps
open GeneralDeclarationExamples (roles)

abbrev badModel : GeneralNominalCommonBridge.Assignment := fun source =>
  if source = 3 then (.base .str,Common.rowEmpty) else model source

/-- Reserved target 3 is unconstrained by the source snapshot. -/
theorem bad_source_models : GeneralNominalState.Models source badModel := by
  refine ⟨⟨?_,?_,?_⟩,?_,by simp [PresenceNormalForm.All]⟩
  · intro atom member
    change atom ∈ GeneralSourceState.equationAtoms (1 : Fin 2) (.base .int) at member
    simp only [GeneralSourceState.equationAtoms,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> exact CommonNominalFullCarrier.subtype_refl _
  · intro slot term recorded
    by_cases yes : slot = 1
    · subst slot
      have equal : (Core.PresenceGeneration.TyTerm.base .int : Core.PresenceGeneration.TyTerm (Fin 2)) = term := by
        simpa [GeneralNominalExamples.heads,GeneralSourceState.Head.equation] using recorded
      subst term
      exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩
    · simp [GeneralNominalExamples.heads,yes,GeneralSourceState.Head.equation] at recorded
  · intro pair member
    change pair ∈ [(0,0),(1,1)] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> exact CommonNominalFullCarrier.subtype_refl _
  · intro slot descriptor recorded
    by_cases zero : slot = 0
    · subst slot
      have same : GeneralNominalExamples.listDescriptor = descriptor := Option.some.inj recorded
      subst descriptor
      exact ⟨[.inl (.base .int)],.cons ⟨CommonNominalFullCarrier.subtype_refl _,
        CommonNominalFullCarrier.subtype_refl _⟩ .nil,
        ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩⟩
    · simp [source,GeneralNominalExamples.state,zero] at recorded

abbrev lastPacket : Packet roles :=
  ⟨registry,context,last,terminal,terminal_checked,[(1,1)]⟩

theorem bad_packet : ¬ lastPacket.Holds badModel := by
  intro branch
  change GeneralNominalRecursiveCandidates.BranchModels registry context (root 201 3)
    terminal terminal_checked [(1,1)] badModel at branch
  have materialized := branch.2.2
  rw [schema_exact] at materialized
  have equal := (materialized.1 (.source 3,.scalar .int) (by simp)).2 _ (.source 3)
  have old := (CommonNominalFullModelMap.subtype_exact (.base .str) (.base .int)).mp equal.1
  cases (CommonRigidHeadInspection.base_iff .str .int).mp old

/-- Any current journal containing this packet needs semantic support facts:
with this unchanged source and an empty fact list, SourceFormed is impossible. -/
theorem no_empty_facts_formation (current : State roles)
    (present : lastPacket ∈ current.packets) (focus : GeneralSourceDictionaries.Occurrence roles) :
    ¬ SourceFormed registry focus (⟨context,current,[]⟩ : Tracked roles) := by
  intro formed
  have all : AllModels (⟨context,current,[]⟩ : Tracked roles) badModel :=
    ⟨bad_source_models,by intro fact member; cases member⟩
  have valid := (formed_exact formed badModel).mpr all
  exact bad_packet (valid.2.1 lastPacket present)
end Yulang.GeneralDictionaryJointMergeJournalScope
