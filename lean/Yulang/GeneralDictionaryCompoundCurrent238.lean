import Yulang.GeneralDictionaryCompoundSource238
import Yulang.GeneralDictionaryJournalRefinement228Reobserve
import Yulang.GeneralDictionaryJournalAggregateGuard228

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryCompoundCurrent238
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryCompoundSource238
open GeneralDictionaryJournalRefinement228Reobserve
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)

abbrev currentContext (allocated : List GeneralNominalIdentities.Origin) (reserved : List Nat)
    (ordinary : List (PresenceNormalForm.Atom Nat)) : GeneralNominalCandidates.Context :=
  ⟨pointExtended allocated reserved ordinary,interpretation⟩
abbrev packet (allocated : List GeneralNominalIdentities.Origin) (reserved : List Nat)
    (ordinary : List (PresenceNormalForm.Atom Nat)) : GeneralNominalSaturationState.Packet roles :=
  ⟨registry,currentContext allocated reserved ordinary,GeneralNominalDemandMerging.pointSite root,
    declaration,declaration_checked,[(0,0)]⟩
abbrev plan (allocated : List GeneralNominalIdentities.Origin) (reserved : List Nat)
    (ordinary : List (PresenceNormalForm.Atom Nat)) : Plan roles :=
  ⟨packet allocated reserved ordinary,rootSite snapshot.seed root,rfl⟩

theorem query (allocated : List GeneralNominalIdentities.Origin) (reserved : List Nat)
    (ordinary : List (PresenceNormalForm.Atom Nat)) :
    GeneralNominalInspection.queries (currentContext allocated reserved ordinary).state interpretation declaration =
      [.nominal 0 [.variables [0],.variables [0]]] := by
  simp [GeneralNominalInspection.queries,Declaration.normalHead,GeneralDeclarationPatterns.normalizeArgs,
    GeneralDeclarationPatterns.normalize,GeneralNominalInspection.translate,interpretation]

theorem report_exact (allocated : List GeneralNominalIdentities.Origin) (reserved : List Nat)
    (ordinary : List (PresenceNormalForm.Atom Nat)) : report (currentContext allocated reserved ordinary) declaration [(0,0)] =
    { inspected := [(0,0)], checked := [(0,0),(0,0),(2,2),(2,2)],
      captures := [⟨0,(2,2),some (.nominal (.source 0) 0 0)⟩,
        ⟨0,(2,2),some (.nominal (.source 0) 0 1)⟩],
      anchors := [(.nominal (.source 0) 0 0,(2,2)),(.nominal (.source 0) 0 1,(2,2))] } := by
  have sub : inspectMany (currentContext allocated reserved ordinary).state [.variables [0],.variables [0]] [(2,2),(2,2)]
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

theorem bindings_exact (allocated : List GeneralNominalIdentities.Origin) (reserved : List Nat)
    (ordinary : List (PresenceNormalForm.Atom Nat)) :
    (packet allocated reserved ordinary).bindings = GeneralDictionaryDefaultMergeRevisionProbe210.twice 0 2 2 := by
  change bindings (currentContext allocated reserved ordinary).state
    (report (currentContext allocated reserved ordinary) declaration [(0,0)]) = _
  rw [report_exact]; rfl


end Yulang.GeneralDictionaryCompoundCurrent238
