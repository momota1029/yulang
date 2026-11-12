import Yulang.GeneralDictionaryRecursiveObstruction
import Yulang.GeneralNominalSaturationSteps

/-! A nonvacuous raw journal whose stale choice prevents installing the unique
selected branch. This proves an installation obstruction, not Stable and not
reachability from an initial state. The source and Astra definitions are intact. -/
namespace Yulang.GeneralDictionaryJournalObstruction
open GeneralDeclarations GeneralDeclarationPatterns
open GeneralDeclarationExamples (roles constructors)
open GeneralNominalSaturationState GeneralNominalSaturationSteps
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalUnaryCaptureFacts

abbrev staleDeclaration : Declaration := { GeneralDictionaryRecursiveObstruction.declaration with id := 41 }
abbrev staleRoot : GeneralSourceDictionaries.Occurrence roles :=
  ⟨300,⟨2,fun _ => (0,0),[],by intro output member; cases member⟩⟩

theorem stale_checked : DeclarationChecked constructors roles staleDeclaration := by
  rcases GeneralDictionaryRecursiveObstruction.declaration_checked with ⟨a,b,c,d,e,f,g,h,i,j⟩
  exact ⟨a,b,c,d,e,f,g,h,i,j⟩

abbrev stalePacket : Packet roles :=
  ⟨GeneralDictionaryRecursiveObstruction.registry,GeneralDictionaryRecursiveObstruction.context,GeneralNominalDemandMerging.pointSite staleRoot,
    staleDeclaration,stale_checked,[(0,0)]⟩
abbrev selectedPacket : Packet roles :=
  ⟨GeneralDictionaryRecursiveObstruction.registry,GeneralDictionaryRecursiveObstruction.context,GeneralNominalDemandMerging.pointSite GeneralDictionaryRecursiveObstruction.root,
    GeneralDictionaryRecursiveObstruction.declaration,GeneralDictionaryRecursiveObstruction.declaration_checked,[(0,0)]⟩
abbrev journal : State roles :=
  { context := GeneralDictionaryRecursiveObstruction.context, packets := [stalePacket],
    sites := [GeneralNominalDemandMerging.pointSite GeneralDictionaryRecursiveObstruction.root] }

theorem stale_query : GeneralNominalInspection.queries GeneralDictionaryRecursiveObstruction.context.state
    GeneralDictionaryRecursiveObstruction.context.interpretation staleDeclaration = [.nominal 0 [.variables [0]]] :=
  GeneralDictionaryRecursiveObstruction.query_exact

theorem stale_schema : generated GeneralDictionaryRecursiveObstruction.registry GeneralDictionaryRecursiveObstruction.context staleRoot staleDeclaration
    stale_checked [(0,0)] = {} := by
  unfold generated GeneralNominalMaterialization.requests GeneralCanonicalChildOrder.canonicalEmit
  simp only [GeneralCanonicalChildOrder.canonicalDeclaration,
    GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_nil]
  rfl

theorem stale_holds (model : GeneralNominalCommonBridge.Assignment)
    (models : GeneralNominalState.Models GeneralDictionaryRecursiveObstruction.context.state model) : stalePacket.Holds model := by
  have projection := private_models GeneralDictionaryRecursiveObstruction.context GeneralDictionaryRecursiveObstruction.registry staleRoot staleDeclaration 0
    GeneralNominalExamples.listDescriptor rfl 0 rfl (1,1) rfl stale_query model models
  refine ⟨projection.1,projection.2,?_⟩
  change GeneralNominalMaterialization.Models _ _ _ _
    (generated GeneralDictionaryRecursiveObstruction.registry GeneralDictionaryRecursiveObstruction.context staleRoot staleDeclaration stale_checked [(0,0)]) model
  rw [stale_schema]
  refine ⟨?_,?_,?_,?_⟩ <;> intro entry member <;> cases member

theorem journal_models (model : GeneralNominalCommonBridge.Assignment) :
    Models journal model ↔ GeneralNominalState.Models GeneralDictionaryRecursiveObstruction.context.state model := by
  constructor
  · exact fun valid => valid.1
  · intro valid
    refine ⟨valid,?_,?_⟩
    · intro packet member
      have same := List.mem_singleton.mp member
      subst packet
      exact stale_holds model valid
    · intro site member
      have same := List.mem_singleton.mp member
      subst site
      exact point_holds GeneralDictionaryRecursiveObstruction.root model

theorem context_complete : ContextComplete journal :=
  fun model valid => (journal_models model).mpr valid

theorem bad_journal_model : Models journal GeneralDictionaryRecursiveObstruction.badModel :=
  (journal_models GeneralDictionaryRecursiveObstruction.badModel).mpr GeneralDictionaryRecursiveObstruction.bad_original_model

theorem selected_not_committed : ¬ Committed journal selectedPacket := by
  intro committed
  exact GeneralDictionaryRecursiveObstruction.bad_not_branch (committed.1 GeneralDictionaryRecursiveObstruction.badModel bad_journal_model)

theorem selected_not_choiceCompatible : ¬ ChoiceCompatible journal selectedPacket := by
  intro compatible
  have conflict := compatible stalePacket (by simp) (.refl 300)
  cases conflict

/-- No alternative packet representation avoids the conflict: registry
membership fixes its key, and occurrence equality fixes the alias identity. -/
theorem root_not_installable (packet : Packet roles)
    (root : packet.site.occurrence = GeneralDictionaryRecursiveObstruction.root) : ¬ Installable GeneralDictionaryRecursiveObstruction.registry journal packet := by
  intro enabled
  have visible := enabled.2.2.2.1
  have declaration : packet.declaration = GeneralDictionaryRecursiveObstruction.declaration := List.mem_singleton.mp visible
  have compatible := enabled.2.2.2.2.2.2.2.2.1
  have equal : Alias journal packet.site.occurrence.identity stalePacket.site.occurrence.identity := by
    rw [root]
    exact .refl 300
  have conflict := compatible stalePacket (by simp) equal
  rw [declaration] at conflict
  cases conflict

/-- This obstruction is compatible even with ContextComplete and a nonempty
model class. Full Stable is deliberately not claimed (Refresh is separate). -/
theorem selected_installation_gap :
    Checked GeneralDictionaryRecursiveObstruction.registry ∧ ContextComplete journal ∧
    GeneralNominalLocalBoundary.Local (GeneralNominalLocalBoundary.recursiveFields roles)
      GeneralDictionaryRecursiveObstruction.registry journal.context GeneralDictionaryRecursiveObstruction.root (.selected 40 []) ∧
    Models journal GeneralDictionaryRecursiveObstruction.badModel ∧ ¬ Committed journal selectedPacket ∧
    (∀ packet : Packet roles, packet.site.occurrence = GeneralDictionaryRecursiveObstruction.root →
      ¬ Installable GeneralDictionaryRecursiveObstruction.registry journal packet) :=
  ⟨GeneralDictionaryRecursiveObstruction.registry_checked,context_complete,GeneralDictionaryRecursiveObstruction.selected,bad_journal_model,
    selected_not_committed,root_not_installable⟩

end Yulang.GeneralDictionaryJournalObstruction
