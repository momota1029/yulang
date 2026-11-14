import Yulang.GeneralDictionaryCenteredScalarDiscovery177

/-! Scalar candidate evidence at the reachable ground boundary root.
Point lookup is recovered from the immutable initial root, not supplied. -/
namespace Yulang.GeneralDictionaryCenteredRootScalar177
open GeneralNominalRecursiveInspection GeneralNominalRecursiveCandidates
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralDictionaryCenteredCandidate176 GeneralDictionaryCenteredScalarDiscovery177

private theorem locate_points (state : GeneralSourceState.State)
    (args : List GeneralSourceState.Interval) (bounds)
    (point : ∀ p ∈ args, p.1 = p.2)
    (located : GeneralCandidateBoundaryParts.locate state args = some bounds) :
    ∀ b ∈ bounds, b.1 = b.2 := by
  induction args generalizing bounds with
  | nil => simp [GeneralCandidateBoundaryParts.locate] at located; subst bounds; simp
  | cons a tail ih =>
    have same := point a (by simp)
    cases h : GeneralDictionaryBinderLocations.sourceSlot state a.2 with
    | none => simp [GeneralCandidateBoundaryParts.locate,List.mapM_cons,same,h] at located
    | some slot =>
      simp [GeneralCandidateBoundaryParts.locate,List.mapM_cons,same,h] at located
      change (GeneralCandidateBoundaryParts.locate state tail).bind
        (fun rest => some ((slot,slot) :: rest)) = some bounds at located
      cases ht : GeneralCandidateBoundaryParts.locate state tail with
      | none => simp [ht] at located
      | some rest =>
        simp [ht] at located
        subst bounds
        intro b member
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · rfl
        · exact ih rest (fun p hp => point p (by simp [hp])) ht b member

 theorem root_point {roles : Roles.RoleDecls} {registry : Registry}
    {root : Occurrence roles} {state : State roles}
    (reachable : B4TargetV5.Reachable (GeneralNominalCenteredGroundBoundary.groundBoundary roles)
      registry root state) :
    ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2 := by
  obtain ⟨start,⟨context,labels,source,point,ground,same⟩,path⟩ := reachable
  exact point

 theorem candidate_point {roles : Roles.RoleDecls} {registry : Registry}
    {root : Occurrence roles} {state : State roles} {key : Nat} {children} {plan : Plan roles}
    (reachable : B4TargetV5.Reachable (GeneralNominalCenteredGroundBoundary.groundBoundary roles)
      registry root state)
    (candidate : Candidate registry state root key children plan) (base : Inference.Base)
    (query : GeneralNominalInspection.queries plan.packet.context.state
      plan.packet.context.interpretation plan.packet.declaration = [.scalar base]) :
    ∃ slot, arguments plan.packet.context plan.packet.site.occurrence = some [(slot,slot)] := by
  obtain ⟨metadata,linked,fresh,bounds,located,finished,ready,consistent⟩ := candidate.prepared
  have points : ∀ b ∈ bounds, b.1 = b.2 := by
    apply locate_points plan.packet.context.state.base (List.ofFn root.demand.arguments) bounds
    · intro p member
      obtain ⟨index,rfl⟩ := List.mem_ofFn.mp member
      exact root_point reachable index
    · rw [candidate.occurrence_eq] at located
      exact located
  cases bounds with
  | nil => simp [report,query,inspectMany,Finished] at finished
  | cons b tail =>
    cases tail with
    | cons c rest => simp [report,query,inspectMany,Finished,Report.append] at finished
    | nil =>
      have same := points b (by simp)
      cases b with
      | mk lower upper =>
        change lower = upper at same
        subst upper
        exact ⟨lower,located⟩

variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}
  {state : State roles} {key : Nat} {children : List (Occurrence roles)} {plan : Plan roles}

/-- Terminal scalar root candidates are committed in the current state,
without a recording or installation premise. -/
theorem root_committed
    (reachable : B4TargetV5.Reachable (GeneralNominalCenteredGroundBoundary.groundBoundary roles)
      registry root state)
    (candidate : Candidate registry state root key children plan) (base : Inference.Base)
    (terminal : plan.packet.declaration.requirements = [])
    (outputs : plan.packet.site.occurrence.demand.outputs = [])
    (inputs : plan.packet.declaration.inputNames = [])
    (query : GeneralNominalInspection.queries plan.packet.context.state
      plan.packet.context.interpretation plan.packet.declaration = [.scalar base]) :
    GeneralNominalFeedbackSteps.Committed state.erased.current plan.packet := by
  obtain ⟨slot,point⟩ := candidate_point reachable candidate base query
  exact discovered_committed candidate slot base terminal outputs inputs query point

theorem root_instance
    (reachable : B4TargetV5.Reachable (GeneralNominalCenteredGroundBoundary.groundBoundary roles)
      registry root state)
    (candidate : Candidate registry state root key children plan) (base : Inference.Base)
    (terminal : plan.packet.declaration.requirements = [])
    (outputs : plan.packet.site.occurrence.demand.outputs = [])
    (inputs : plan.packet.declaration.inputNames = [])
    (query : GeneralNominalInspection.queries plan.packet.context.state
      plan.packet.context.interpretation plan.packet.declaration = [.scalar base])
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model) :
    GeneralDictionaryRecursiveEvidence.Instance registry state.erased.current.context model root key children :=
  GeneralDictionaryCenteredScalar177.committed_candidate_instance candidate
    (root_committed reachable candidate base terminal outputs inputs query) model valid

theorem root_evidence
    (reachable : B4TargetV5.Reachable (GeneralNominalCenteredGroundBoundary.groundBoundary roles)
      registry root state)
    (candidate : Candidate registry state root key children plan) (base : Inference.Base)
    (terminal : plan.packet.declaration.requirements = [])
    (outputs : plan.packet.site.occurrence.demand.outputs = [])
    (inputs : plan.packet.declaration.inputNames = [])
    (query : GeneralNominalInspection.queries plan.packet.context.state
      plan.packet.context.interpretation plan.packet.declaration = [.scalar base])
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model) :
    GeneralDictionaryRecursiveEvidence.Evidence registry state.erased.current.context model root (.node key []) := by
  obtain ⟨slot,point⟩ := candidate_point reachable candidate base query
  exact discovered_evidence candidate slot base terminal outputs inputs query point model valid

end Yulang.GeneralDictionaryCenteredRootScalar177
