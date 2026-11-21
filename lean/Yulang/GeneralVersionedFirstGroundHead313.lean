import Yulang.GeneralVersionedFiniteInspectionTests313

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
/-! The real checked source boundary supplies finite ground roots. Before
the first installation they suffice for every constructor test, including
nested nominal/structural captures and actual repeated-variable rows. -/
namespace Yulang.GeneralVersionedFirstGroundHead313
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralNominalVersionedTraceSupport237 (Reachable)
open GeneralNominalVersionedDiagnostic232 (HeadEquations)
open GeneralVersionedSharingBinderRows313 (Tests)
open GeneralNominalRecursiveInspection (Origin Observes)
open GeneralNominalGroundAccessibility (GroundRoots ClosedTerm Inputs)
open GeneralNominalOriginTerms (Expr)
open GeneralNominalFiniteMeaning (At denote)
open GeneralNominalInspectionPositions (Input InputsAt inputs_at)
open GeneralNominalQueryProvenance183 (headInspection)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Equivalent Subtype subtype_trans)

theorem tests_of_registered_ground {s : State roles} {p : Plan roles}
    (frame : Frame registry s.core focus key p) (m : Assignment) (valid : Models s m)
    (known : Inputs ctx m p.input.observed labels) : Tests p m := by
  have raw : GeneralNominalState.Models p.packet.context.state m := by
    rw [frame.context_eq]
    exact valid.1.1
  have finish := GeneralNominalVersionedCurrentProjection237.frame_finished p frame
  let origins := fun i : Nat => Origin.source ((List.ofFn p.input.center)[i]?.getD 0)
  obtain ⟨labelLength,meanings⟩ := known
  let terms : Fin (roles p.input.occurrence.demand.role).arity → Expr Nat := fun i =>
    Classical.choose (meanings i)
  have termFacts (i) := Classical.choose_spec (meanings i)
  have located := frame.located
  rw [← frame.occurrence_eq,← p.input_exact] at located
  have lens : p.packet.bounds.length = (roles p.input.occurrence.demand.role).arity := by
    simpa only [List.length_ofFn] using GeneralNominalPacketCodes.locate_length p.packet.context.state.base
      (List.ofFn p.input.occurrence.demand.arguments) p.packet.bounds located
  have inputTerms : InputsAt ctx m p.packet.context.state (fun i => some (origins i)) 0 p.packet.bounds (List.ofFn terms) := by
    apply inputs_at _ _ (by rw [List.length_ofFn,lens])
    intro index
    let pos : Fin (roles p.input.occurrence.demand.role).arity := ⟨index.val,by rw [← lens]; exact index.isLt⟩
    have within : index.val < (roles p.input.occurrence.demand.role).arity := pos.isLt
    have facts := termFacts pos
    have rawInterval := congrArg (fun xs => xs[index.val]?)
      (GeneralNominalPacketCaptureReadback.locate_sources p.packet.context.state.base
        (List.ofFn p.input.occurrence.demand.arguments) p.packet.bounds located)
    have same : (p.packet.context.state.base.source p.packet.bounds[index.val].1,
        p.packet.context.state.base.source p.packet.bounds[index.val].2) =
        p.input.occurrence.demand.arguments pos := by
      simpa only [List.getElem?_map,List.getElem?_eq_getElem index.isLt,Option.map_some,List.getElem?_ofFn,
        within,dite_eq_left,Option.some.injEq] using rawInterval
    simp only [Fin.getElem_fin,List.getElem_ofFn,Nat.zero_add]
    refine ⟨⟨_,facts.1⟩,?_,?_⟩
    · change GeneralNominalCaptureMerges.Fits m _ _
      rw [same]
      exact facts.2.1
    · intro actual locatedOrigin
      have eq : origins index.val = actual := Option.some.inj locatedOrigin
      subst actual
      apply facts.2.2
      simp [Site.observed,origins,pos,within]
  exact GeneralVersionedFiniteInspectionTests313.many_tests _ m raw _ _ origins 0 _ finish inputTerms

theorem source_ground {s : State roles} {p : Plan roles}
    (actual : Reachable registry root s) (empty : s.plans = [])
    (frame : Frame compiled s.core focus key p)
    (m : Assignment) (valid : Models s m) :
    ∃ ctx labels, Inputs ctx m p.input.observed labels := by
  obtain ⟨start,⟨legacy,⟨ctx,labels,formation,point,ground,cover,rfl⟩,rfl⟩,steps⟩ := actual
  have path : Reachable registry root s :=
    ⟨_,⟨_,⟨ctx,labels,formation,point,ground,cover,rfl⟩,rfl⟩,steps⟩
  have original : GeneralNominalState.Models ctx.state m := by
    have keep := valid.1.2.1
    rw [GeneralNominalVersionedMixedGrowth234.steps_source steps] at keep
    exact keep
  have origin := (GeneralVersionedSiteOrigins312.trace steps).origin p.input frame.center_recorded
  rcases origin with isRoot|⟨installed,prior,_⟩
  · refine ⟨ctx,labels,?_⟩
    rw [isRoot]
    have erased : (rootSite ctx.state.seed root).observed = GeneralNominalDemandMerging.pointSite root :=
      GeneralNominalCenteredPointSource.point_observed _ point (point_center _ _)
    rw [erased]
    exact GeneralNominalGroundAccessibility.root_inputs ground point m original
  · rw [empty] at prior
    cases prior

theorem tests {s : State roles} {p : Plan roles}
    (actual : Reachable registry root s) (empty : s.plans = [])
    (frame : Frame compiled s.core focus key p) (m : Assignment) (valid : Models s m) :
    Tests p m := by
  obtain ⟨_,_,found⟩ := source_ground actual empty frame m valid
  exact tests_of_registered_ground frame m valid found

theorem head {s : State roles} {p : Plan roles}
    (checked : (boundary roles).Checked registry)
    (actual : Reachable registry root s) (empty : s.plans = [])
    (picked : Local registry s focus (.selected key kids))
    (frame : Frame (Compiled registry) s.core focus key p)
    (nonempty : ∃ m, Models s m) :
    ∃ m, Models s m ∧ HeadEquations p m :=
  GeneralVersionedFirstHead313.initial_head checked actual empty picked frame nonempty
    (fun m valid _ => tests actual empty frame m valid)

end Yulang.GeneralVersionedFirstGroundHead313
