import Yulang.GeneralLiveCompoundLeafEvidence316
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralLiveCompoundCurrentRoot316
open GeneralDictionaryJournalRefinement228Source (snapshot roles root interpretation)
open GeneralLiveCompoundRegistry316 (registry declaration declaration_checked leaf)
open GeneralLiveCompoundUpperSnapshot316 (snap context)
open GeneralLiveCompoundUpperRefresh316 (upperState)
open GeneralLiveCompoundChildSite316 (childSite child raw_sites centers)
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
noncomputable abbrev packet : GeneralNominalSaturationState.Packet roles :=
  ⟨registry,context,GeneralNominalDemandMerging.pointSite root,declaration,declaration_checked,[(0,0)]⟩
noncomputable abbrev plan : Plan roles := ⟨packet,rootSite snapshot.seed root,rfl⟩

theorem query : GeneralNominalInspection.queries snap interpretation declaration =
    [.nominal 0 [.variables [0],.variables [0]]] := GeneralMixedCompoundUpperChild307.query

theorem report_exact : report context declaration [(0,0)] =
    { inspected := [(0,0)], checked := [(0,0),(0,0),(2,2),(2,2)],
      captures := [⟨0,(2,2),some (.nominal (.source 0) 0 0)⟩,⟨0,(2,2),some (.nominal (.source 0) 0 1)⟩],
      anchors := [(.nominal (.source 0) 0 0,(2,2)),(.nominal (.source 0) 0 1,(2,2))] } := by
  have sub : inspectMany snap [.variables [0],.variables [0]] [(2,2),(2,2)]
      (fun index => some (.nominal (.source 0) 0 index)) 0 =
      { captures := [⟨0,(2,2),some (.nominal (.source 0) 0 0)⟩,⟨0,(2,2),some (.nominal (.source 0) 0 1)⟩],
        checked := [(2,2),(2,2)],
        anchors := [(.nominal (.source 0) 0 0,(2,2)),(.nominal (.source 0) 0 1,(2,2))] } := by
    simp [inspectMany,inspect,Report.append]
  unfold report
  rw [query]
  simp [inspectMany,inspect,typeArguments,Report.append,Report.visit]
  exact ⟨congrArg Report.captures sub,congrArg Report.inspected sub,congrArg Report.checked sub,
    congrArg Report.blocked sub,congrArg Report.conflicts sub,congrArg Report.arity sub,
    congrArg Report.anchors sub,congrArg Report.tests sub⟩

theorem bindings_exact : packet.bindings = [(0,2,2),(0,2,2)] := by
  change bindings snap (report context declaration [(0,0)]) = _
  rw [report_exact]
  rfl
theorem located : arguments context (GeneralNominalVersionedCandidates231.inputs root) = some [(0,0)] := by
  decide +kernel

theorem not_root : child ≠ root := by
  intro eq
  have role := congrArg (fun o : Occurrence roles => o.demand.role) eq
  cases role

theorem root_raw {site : GeneralNominalDemandMerging.Site roles}
    (member : site ∈ upperState.core.erased.current.sites) (occurrence : site.occurrence = root) :
    site = GeneralNominalDemandMerging.pointSite root := by
  rw [raw_sites] at member
  rcases List.mem_cons.mp member with same | member
  · exact same
  · cases List.mem_singleton.mp member
    exact False.elim (not_root occurrence)

theorem root_center {site : Site roles}
    (member : site ∈ upperState.core.sites) (occurrence : site.occurrence = root) :
    site = rootSite snapshot.seed root := by
  rw [centers] at member
  rcases List.mem_cons.mp member with same | member
  · exact same
  · cases List.mem_singleton.mp member
    exact False.elim (not_root occurrence)

theorem frame_plan {candidate : Plan roles}
    (framed : GeneralNominalVersionedEvidence231.Frame registry upperState.core root key candidate) :
    candidate = plan := by
  rcases candidate with ⟨⟨reg,ctx,site,decl,check,bounds⟩,input,inputEq⟩
  have regEq : reg = registry := framed.registry_eq
  have ctxEq : ctx = context := framed.context_eq
  have declEq : decl = declaration := by
    rcases List.mem_cons.mp framed.visible with one | last
    · exact one
    · have eq : decl = leaf := List.mem_singleton.mp last
      have role := framed.role_eq
      change decl.role = 0 at role
      rw [eq] at role
      cases role
  have siteEq : site = GeneralNominalDemandMerging.pointSite root := root_raw framed.raw_recorded framed.occurrence_eq
  have inputSame : input = rootSite snapshot.seed root := root_center framed.center_recorded (inputEq.trans framed.occurrence_eq)
  subst reg; subst ctx; subst decl; subst site; subst input
  have boundsEq : [(0,0)] = bounds := Option.some.inj (located.symm.trans framed.located)
  subst bounds
  rfl

end Yulang.GeneralLiveCompoundCurrentRoot316
