import Yulang.GeneralDictionaryJournalRefinement228Initial
import Yulang.GeneralDictionaryJournalRefinement228Reobserve
import Yulang.GeneralDictionaryJournalAggregateGuard228

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryJournalRefinement228Current
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryJournalRefinement228Initial
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

/-- A current point-descriptor packet forces p0 to the width-record value.
This local implication does not assert the current state is reachable/selected. -/
theorem packet_forces_width (allocated : List GeneralNominalIdentities.Origin) (reserved : List Nat)
    (ordinary : List (PresenceNormalForm.Atom Nat)) (m : Assignment)
    (holds : GeneralNominalCenteredHeadMatStepPackets.Holds (plan allocated reserved ordinary) m)
    (width : (m 2).1 = .emptyRecord) :
    Equivalent (m (fresh snapshot.seed root.identity declaration.id 0 0 0)).1 .emptyRecord := by
  have merges := holds.2.1.1.2.1
  rw [bindings_exact] at merges
  have bound := GeneralDictionaryDefaultMergeRevisionProbe210.repeated_lower_value
    (name := 0) (by simp [Declaration.inputNames,GeneralDeclarationPatterns.variablesArgs,
      GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
      GeneralDeclarationPatterns.Pattern.variables]) merges
  change Equivalent (m (fresh snapshot.seed root.identity declaration.id 0 0 0)).1 (m 2).1 at bound
  simpa only [width] using bound

theorem packet_excludes_exact_lower (allocated : List GeneralNominalIdentities.Origin) (reserved : List Nat)
    (ordinary : List (PresenceNormalForm.Atom Nat)) (m : Assignment)
    (width : (m 2).1 = .emptyRecord)
    (exactLower : (m (fresh snapshot.seed root.identity declaration.id 0 0 0)).1 = .exactEmpty) :
    ¬ GeneralNominalCenteredHeadMatStepPackets.Holds (plan allocated reserved ordinary) m := by
  intro holds
  have incompatible := packet_forces_width allocated reserved ordinary m holds width
  rw [exactLower] at incompatible
  exact exactEmpty_not_equivalent_width incompatible


theorem frame_plan {s : GeneralNominalCenteredHeadMatStepJournal.State roles}
    (allocated : List GeneralNominalIdentities.Origin) (reserved : List Nat)
    (ordinary : List (PresenceNormalForm.Atom Nat))
    (contextEq : s.core.erased.current.context = currentContext allocated reserved ordinary)
    (rawSites : s.core.erased.current.sites = [GeneralNominalDemandMerging.pointSite root])
    (centers : s.core.sites = [rootSite snapshot.seed root])
    {candidate : Plan roles}
    (framed : GeneralNominalCenteredHeadOutputs.Frame registry s.core root key candidate) :
    candidate = plan allocated reserved ordinary := by
  rcases candidate with ⟨⟨reg,ctx,site,decl,check,bounds⟩,input,inputEq⟩
  have regEq : reg = registry := framed.registry_eq
  have ctxEq : ctx = currentContext allocated reserved ordinary := framed.context_eq.trans contextEq
  have declEq : decl = declaration := List.mem_singleton.mp framed.visible
  have siteEq : site = GeneralNominalDemandMerging.pointSite root :=
    List.mem_singleton.mp (rawSites ▸ framed.raw_recorded)
  have inputSame : input = rootSite snapshot.seed root :=
    List.mem_singleton.mp (centers ▸ framed.center_recorded)
  subst reg; subst ctx; subst decl; subst site; subst input
  have boundsEq : [(0,0)] = bounds := Option.some.inj framed.located
  subst bounds
  rfl

/-- If a concrete state has this current point inspection and a retained
exact-empty aggregate model, no current-frame total certificate can exist.
Reachability, stability and selection are not asserted by this local test. -/
theorem no_instance {s : GeneralNominalCenteredHeadMatStepJournal.State roles}
    (allocated : List GeneralNominalIdentities.Origin) (reserved : List Nat)
    (ordinary : List (PresenceNormalForm.Atom Nat))
    (contextEq : s.core.erased.current.context = currentContext allocated reserved ordinary)
    (rawSites : s.core.erased.current.sites = [GeneralNominalDemandMerging.pointSite root])
    (centers : s.core.sites = [rootSite snapshot.seed root])
    (m : Assignment) (width : (m 2).1 = .emptyRecord)
    (exactLower : (m (fresh snapshot.seed root.identity declaration.id 0 0 0)).1 = .exactEmpty) :
    ¬ GeneralDictionaryTotalEvidence206.Instance registry s.core m root key children := by
  rintro ⟨candidate,certificate⟩
  have same := frame_plan allocated reserved ordinary contextEq rawSites centers certificate.frame
  subst candidate
  exact packet_excludes_exact_lower allocated reserved ordinary m width exactLower certificate.packet

end Yulang.GeneralDictionaryJournalRefinement228Current
