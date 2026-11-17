import Yulang.GeneralDictionaryJournalRefinement229Refresh
namespace Yulang.GeneralDictionaryJournalRefinement229Raw
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryJournalRefinement228Initial
open GeneralDictionaryJournalRefinement228Install
open GeneralDictionaryJournalRefinement228Stage
open GeneralDictionaryJournalRefinement229Snapshot
open GeneralDeclarations
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open CommonNominalFullCarrier

theorem query  :
    GeneralNominalInspection.queries refreshedContext.state interpretation declaration =
      [.nominal 0 [.variables [0],.variables [0]]] := by
  simp [GeneralNominalInspection.queries,Declaration.normalHead,GeneralDeclarationPatterns.normalizeArgs,
    GeneralDeclarationPatterns.normalize,GeneralNominalInspection.translate,interpretation]

theorem report_exact  : report refreshedContext declaration [(0,0)] =
    { inspected := [(0,0)], checked := [(0,0),(0,0),(2,2),(2,2)],
      captures := [⟨0,(2,2),some (.nominal (.source 0) 0 0)⟩,
        ⟨0,(2,2),some (.nominal (.source 0) 0 1)⟩],
      anchors := [(.nominal (.source 0) 0 0,(2,2)),(.nominal (.source 0) 0 1,(2,2))] } := by
  have sub : inspectMany refreshedContext.state [.variables [0],.variables [0]] [(2,2),(2,2)]
      (fun index => some (.nominal (.source 0) 0 index)) 0 =
      { captures := [⟨0,(2,2),some (.nominal (.source 0) 0 0)⟩,
          ⟨0,(2,2),some (.nominal (.source 0) 0 1)⟩],
        checked := [(2,2),(2,2)],
        anchors := [(.nominal (.source 0) 0 0,(2,2)),(.nominal (.source 0) 0 1,(2,2))] } := by
    simp [inspectMany,inspect,Report.append]
  unfold report
  rw [query]
  simp [inspectMany,inspect,typeArguments,Report.append,Report.visit]
  exact ⟨congrArg Report.captures sub,congrArg Report.inspected sub,congrArg Report.checked sub,
    congrArg Report.blocked sub,congrArg Report.conflicts sub,congrArg Report.arity sub,
    congrArg Report.anchors sub,congrArg Report.tests sub⟩

theorem bindings_exact : bindings refreshedContext.state (report refreshedContext declaration [(0,0)]) =
    GeneralDictionaryDefaultMergeRevisionProbe210.twice 0 2 2 := by
  rw [report_exact]
  rfl

theorem raw_lower (m : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models refreshedSnapshot m) : Equivalent (m lo).1 .exactEmpty := by
  have atoms := valid.2.2
  have prior : GeneralNominalState.Models packet.privateContext.state m := by
    refine ⟨?_,?_,atoms⟩
    · exact (GeneralNominalRefinements.models GeneralDictionaryJournalRefinement229Refresh.refines m valid).1
    · have current := GeneralNominalRefinements.models GeneralDictionaryJournalRefinement229Refresh.refines m valid
      exact ((GeneralDictionaryJournalRefinement228Reobserve.extended_models_iff allocated reserved ordinary m).mp current).2.1
  have merged := (GeneralNominalAllocation.propagate_models ..).mp ((GeneralNominalState.extend_models ..).mp prior).1 |>.2.2
  change PresenceNormalForm.All CommonNominalFullCarrier.model m (GeneralNominalAllocation.merges snapshot registry root.identity declaration packet.bindings) at merged
  rw [GeneralDictionaryJournalRefinement228Install.bindings_exact] at merged
  have relation := GeneralDictionaryDefaultMergeRevisionProbe210.repeated_lower_value
    (name := 0) (by simp [GeneralDeclarations.Declaration.inputNames,
      GeneralDeclarationPatterns.variablesArgs,GeneralDeclarationPatterns.normalizeArgs,
      GeneralDeclarationPatterns.normalize,GeneralDeclarationPatterns.Pattern.variables]) merged
  have out : Equivalent (m 4).1 .exactEmpty := valid.1.2.1 (4 : Fin 5) .exactEmpty rfl
  exact ⟨subtype_trans relation.1 out.1,subtype_trans out.2 relation.2⟩

theorem no_head_model (m : GeneralNominalCommonBridge.Assignment) :
    ¬ GeneralNominalCenteredHeadCandidates.HeadModels registry refreshedContext root declaration [(0,0)] m := by
  intro head
  have extended := (GeneralNominalState.extend_models ..).mp head.1
  have parts := (GeneralNominalAllocation.propagate_models ..).mp extended.1
  have lower := raw_lower m parts.1
  have merged := parts.2.2
  change PresenceNormalForm.All CommonNominalFullCarrier.model m
    (GeneralNominalAllocation.merges refreshedContext.state registry root.identity declaration
      (bindings refreshedContext.state (report refreshedContext declaration [(0,0)]))) at merged
  rw [bindings_exact] at merged
  have relation := GeneralDictionaryDefaultMergeRevisionProbe210.repeated_lower_value
    (name := 0) (by simp [Declaration.inputNames,
      GeneralDeclarationPatterns.variablesArgs,GeneralDeclarationPatterns.normalizeArgs,
      GeneralDeclarationPatterns.normalize,GeneralDeclarationPatterns.Pattern.variables]) merged
  have width : Equivalent (m 2).1 .emptyRecord := parts.1.1.2.1 (2 : Fin 5) .emptyRecord rfl
  have toWidth : Equivalent (m lo).1 .emptyRecord :=
    ⟨subtype_trans relation.1 width.1,subtype_trans width.2 relation.2⟩
  exact exactEmpty_not_equivalent_width
    ⟨subtype_trans lower.2 toWidth.1,subtype_trans toWidth.2 lower.1⟩

theorem not_prepared : ¬ GeneralNominalCenteredHeadCandidates.Prepared registry refreshedContext root declaration := by
  rintro ⟨_,_,_,bounds,located,_,m,head⟩
  have same : bounds = [(0,0)] := Option.some.inj located.symm
  subst bounds
  exact no_head_model m head

end Yulang.GeneralDictionaryJournalRefinement229Raw
