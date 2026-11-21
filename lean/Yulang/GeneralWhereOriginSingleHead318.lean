import Yulang.GeneralWhereOriginSingleRead318

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27000
set_option maxHeartbeats 23000000
namespace Yulang.GeneralWhereOriginSingleHead318
open GeneralWhereOriginSingleSource318
open GeneralWhereOriginSingleRead318 (firstOrigin secondOrigin old_report new_report old_bindings new_bindings)
open GeneralNominalRecursiveInspection
open GeneralNominalVersionedPlans231 (HeadModels Ordinary private_models_iff)
open GeneralNominalPacketSupport (report)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
open GeneralNominalAllocation (Compatible)

theorem independent_projection {s : GeneralNominalState.State} {a b : GeneralNominalInspection.Bounds s} {r : Report s}
    (anchors : r.anchors = [(firstOrigin,a),(secondOrigin,b)])
    (caps : r.captures = [⟨0,a,some firstOrigin⟩,⟨1,b,some secondOrigin⟩])
    (tests : r.tests = [])
    (m : Assignment)
    (facts : ∀ anchor ∈ r.anchors, (∃ actual, Observes m anchor.1 actual) ∧
      ∀ actual, Observes m anchor.1 actual → Fits s m anchor.2 actual) :
    ProjectionModels s r m := by
  refine ⟨facts,?_,?_,?_⟩
  · intro t stored
    rw [tests] at stored
    cases stored
  · intro x found y stored same ref src v seen
    rw [caps] at found stored
    rcases List.mem_cons.mp found with rfl|tail
    · rcases List.mem_cons.mp stored with rfl|tail'
      · cases Option.some.inj src
        exact (facts _ (anchors.symm ▸ List.mem_cons_self)).2 v seen
      · cases List.mem_singleton.mp tail'
        cases same
    · cases List.mem_singleton.mp tail
      rcases List.mem_cons.mp stored with rfl|tail'
      · cases same
      · cases List.mem_singleton.mp tail'
        cases Option.some.inj src
        exact (facts _ (anchors.symm ▸ List.mem_cons_of_mem _ (List.mem_singleton_self _))).2 v seen
  · intro x found y stored same a' b' lhs rhs u v seenu seenv
    rw [caps] at found stored
    rcases List.mem_cons.mp found with rfl|tail
    · rcases List.mem_cons.mp stored with rfl|tail'
      · cases Option.some.inj lhs
        cases Option.some.inj rhs
        exact nominal_observation_unique m (.argument (.source 0) 0 0) u v seenu seenv
      · cases List.mem_singleton.mp tail'
        cases same
    · cases List.mem_singleton.mp tail
      rcases List.mem_cons.mp stored with rfl|tail'
      · cases same
      · cases List.mem_singleton.mp tail'
        cases Option.some.inj lhs
        cases Option.some.inj rhs
        exact nominal_observation_unique m (.argument (.source 0) 0 1) u v seenu seenv

theorem compatible {lo hi : Nat} (m : Assignment) (bound : Subtype (m lo).1 (m hi).1) :
    Compatible [(0,lo,hi),(1,lo,hi)] m := by
  intro x first y last same
  rcases List.mem_cons.mp first with rfl|rest
  · rcases List.mem_cons.mp last with rfl|last
    · exact bound
    · cases List.mem_singleton.mp last; cases same
  · cases List.mem_singleton.mp rest
    rcases List.mem_cons.mp last with rfl|last
    · cases same
    · cases List.mem_singleton.mp last; exact bound

theorem old_head (m : Assignment) (legacy : HeadModels GeneralLiveCompoundRoot316.packet m) :
    HeadModels older m := by
  have old := (private_models_iff ..).mp legacy.1
  have constraints := old.2
  have lo : Subtype (m 4).1 (m 2).1 := by
    have compatible := constraints.1
    rw [show GeneralLiveCompoundRoot316.packet.bindings = [(0,4,2),(0,4,2)]
      from GeneralDictionaryCompoundPacket238.bindings_exact] at compatible
    exact compatible _ List.mem_cons_self _ List.mem_cons_self rfl
  refine ⟨(private_models_iff ..).mpr ⟨old.1,?_⟩,?_⟩
  · refine ⟨old_bindings.symm ▸ compatible m lo,?_,?_⟩
    · have empty : GeneralNominalVersionedAllocation231.merges older.context.state older.registry
          older.site.occurrence.identity older.declaration older.bindings = [] := by
        rw [old_bindings]
        rfl
      rw [empty]; intro _ bad; cases bad
    · have same : selfChecks older.context.state (report older) =
          selfChecks GeneralLiveCompoundRoot316.packet.context.state (report GeneralLiveCompoundRoot316.packet) := by
        change selfChecks _ (GeneralNominalRecursiveCandidates.report _ declaration [(0,0)]) =
          selfChecks _ (GeneralNominalRecursiveCandidates.report _ GeneralDictionaryCompoundSource238.declaration [(0,0)])
        rw [old_report,GeneralDictionaryCompoundPacket238.report_exact]
        rfl
      rw [same]
      exact constraints.2.2
  · change ProjectionModels _ (GeneralNominalRecursiveCandidates.report _ declaration [(0,0)]) m
    rw [old_report]
    apply independent_projection rfl rfl rfl
    intro anchor member
    apply legacy.2.1 anchor
    change anchor ∈ (GeneralNominalRecursiveCandidates.report
      GeneralDictionaryJournalRefinement228Source.context GeneralDictionaryCompoundSource238.declaration [(0,0)]).anchors
    rw [GeneralDictionaryCompoundPacket238.report_exact]
    exact member

theorem new_head (m : Assignment) (legacy : HeadModels GeneralLiveCompoundCurrentRoot316.packet m) :
    HeadModels newer m := by
  have old := (private_models_iff ..).mp legacy.1
  refine ⟨(private_models_iff ..).mpr ⟨old.1,?_⟩,?_⟩
  · refine ⟨new_bindings.symm ▸ compatible m (subtype_refl _),?_,?_⟩
    · have empty : GeneralNominalVersionedAllocation231.merges newer.context.state newer.registry
          newer.site.occurrence.identity newer.declaration newer.bindings = [] := by
        rw [new_bindings]
        rfl
      rw [empty]; intro _ bad; cases bad
    · have same : selfChecks newer.context.state (report newer) =
          selfChecks GeneralLiveCompoundCurrentRoot316.packet.context.state (report GeneralLiveCompoundCurrentRoot316.packet) := by
        change selfChecks _ (GeneralNominalRecursiveCandidates.report _ declaration [(0,0)]) =
          selfChecks _ (GeneralNominalRecursiveCandidates.report _ GeneralLiveCompoundRegistry316.declaration [(0,0)])
        rw [new_report,GeneralLiveCompoundCurrentRoot316.report_exact]
        rfl
      rw [same]
      exact old.2.2.2
  · change ProjectionModels _ (GeneralNominalRecursiveCandidates.report _ declaration [(0,0)]) m
    rw [new_report]
    apply independent_projection rfl rfl rfl
    intro anchor member
    apply legacy.2.1 anchor
    change anchor ∈ (GeneralNominalRecursiveCandidates.report
      GeneralLiveCompoundUpperSnapshot316.context GeneralLiveCompoundRegistry316.declaration [(0,0)]).anchors
    rw [GeneralLiveCompoundCurrentRoot316.report_exact]
    exact member

end Yulang.GeneralWhereOriginSingleHead318
