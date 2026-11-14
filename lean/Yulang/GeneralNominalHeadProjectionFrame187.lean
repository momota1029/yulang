import Yulang.GeneralNominalHeadInitialExtension187
import Yulang.GeneralNominalRawOrigin182

/-! Actual centered inspection reads only the existing journal footprint.
Thus finite head extensions preserve its independent projection constraints. -/
namespace Yulang.GeneralNominalHeadProjectionFrame187
open GeneralNominalRecursiveInspection
open GeneralNominalInspection (Query Bounds queries)
open GeneralNominalRawOrigin182 (ReportRoots inspect_roots)
open GeneralNominalCenteredModelExtension (originSource)
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects
open GeneralNominalCenteredHeadOutputs (Frame HeadEquations)
open GeneralNominalHeadLedgerFrame182 (fullSources)
open GeneralNominalQueryProvenance183 (headInspection)
open GeneralNominalHeadEquationExtension186 (uses)
open GeneralNominalHeadConservativeExtension186 (support)
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls} {registry : Registry} {root focus : Occurrence roles}
variable {state : State roles}

 theorem roots_append (first last : Report context)
    (one : ReportRoots first names) (two : ReportRoots last names) :
    ReportRoots (first.append last) names := by
  refine ⟨?_,?_,?_⟩
  · intro anchor member
    rcases List.mem_append.mp member with a | b
    · exact one.1 anchor a
    · exact two.1 anchor b
  · intro test member
    rcases List.mem_append.mp member with a | b
    · exact one.2.1 test a
    · exact two.2.1 test b
  · intro capture member origin recorded
    rcases List.mem_append.mp member with a | b
    · exact one.2.2 capture a origin recorded
    · exact two.2.2 capture b origin recorded

 theorem many_bounded_roots (context : GeneralNominalState.State) (names : List Nat)
    (slots : ∀ slot, context.base.source slot ∈ names)
    (queries : List Query) (bounds : List (Bounds context)) (origins : Nat → Origin) (offset : Nat)
    (known : ∀ index, offset ≤ index → index < offset + queries.length → originSource (origins index) ∈ names) :
    ReportRoots (inspectMany context queries bounds (fun i => some (origins i)) offset) names := by
  induction queries generalizing offset bounds with
  | nil => cases bounds <;> simp [inspectMany,ReportRoots]
  | cons query rest ih => cases bounds with
    | nil => simp [inspectMany,ReportRoots]
    | cons head tail =>
      simp only [inspectMany]
      apply roots_append
      · apply inspect_roots context names slots query head
        intro ref equal
        cases equal
        exact known offset (Nat.le_refl _) (by simp)
      · apply ih tail (offset+1)
        intro index lower upper
        exact known index (by omega) (by simp only [List.length_cons]; omega)

 theorem head_report_roots (candidate : Plan roles)
    (frame : Frame registry state.core focus key candidate) :
    ReportRoots (headInspection candidate) (fullSources state) := by
  apply many_bounded_roots
  · intro slot
    apply GeneralNominalHeadCandidateSupport186.current_source state
    rw [← frame.context_eq]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨slot,rfl⟩)))
  · intro index _ bound
    have aligned := GeneralNominalHeadFrameExtension186.frame_aligned frame
    have length : (queries candidate.packet.context.state candidate.packet.context.interpretation
        candidate.packet.declaration).length = (roles candidate.input.occurrence.demand.role).arity := by
      simp only [queries,List.length_map,Declaration.normalHead,GeneralNominalHeadCandidateSupport186.normalized_length]
      exact candidate.packet.checked.signature.1.trans (congrArg (fun role => (roles role).arity) aligned)
    have within : index < (roles candidate.input.occurrence.demand.role).arity := by omega
    simp only [List.getElem?_ofFn,within,↓reduceDIte,Option.getD_some,originSource]
    exact GeneralNominalHeadCandidateSupport186.registered_center state candidate.input frame.center_recorded
      (List.mem_ofFn.mpr ⟨⟨index,within⟩,rfl⟩)

 theorem report_sources (candidate : Plan roles)
    (frame : Frame registry state.core focus key candidate) :
    GeneralNominalRawFrame179.reportSources candidate.packet.context.state (headInspection candidate) ⊆ fullSources state := by
  intro name member
  have roots := head_report_roots candidate frame
  simp only [GeneralNominalRawFrame179.reportSources,List.mem_append] at member
  rcases member with ((member | member) | member) | member
  · apply GeneralNominalHeadCandidateSupport186.current_source state
    simpa only [frame.context_eq] using member
  · obtain ⟨anchor,present,rfl⟩ := List.mem_map.mp member
    exact roots.1 anchor present
  · obtain ⟨test,present,rfl⟩ := List.mem_map.mp member
    exact roots.2.1 test present
  · obtain ⟨capture,present,member⟩ := List.mem_flatMap.mp member
    obtain ⟨origin,recorded,rfl⟩ := List.mem_map.mp member
    exact roots.2.2 capture present origin (by simpa using recorded)

 theorem projection_iff (candidate : Plan roles)
    (frame : Frame registry state.core focus key candidate) (first last : Assignment)
    (same : ∀ name ∈ fullSources state, first name = last name) :
    ProjectionModels candidate.packet.context.state (headInspection candidate) first ↔
      ProjectionModels candidate.packet.context.state (headInspection candidate) last :=
  GeneralNominalRawFrame179.projection_iff _ _ (fun name member => same name (report_sources candidate frame member))

end Yulang.GeneralNominalHeadProjectionFrame187
