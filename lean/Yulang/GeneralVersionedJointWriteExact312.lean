import Yulang.GeneralVersionedJointWrites312

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralVersionedJointWriteExact312
open GeneralNominalCenteredFrame179 (Agree)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (State Models Effect)
open GeneralNominalVersionedPlans231 (HeadModels SchemaHolds)
open GeneralNominalVersionedMixedMaterialization237 (Residual)
open GeneralNominalVersionedModelSupport237 (Support)
open GeneralFiniteTypedWrites312 (Coherent Protected)
open GeneralVersionedJointWrites312 (equations inputNames rhs rows protect)

theorem requirements {s : State roles} {e : Effect roles} {first last : Assignment}
    {semantic : List Nat}
    (agree : Agree (protect s e semantic) first last) (held : Residual s e last) :
    Coherent (rows e.plan first) ∧ Protected (rows e.plan first) (protect s e semantic) first := by
  apply (GeneralFiniteTypedWrites312.exact _ _ _).mp
  refine ⟨last,agree,?_⟩
  intro row present
  obtain ⟨eq,located,rfl⟩ := List.mem_map.mp present
  have valueEq := GeneralVersionedJointWrites312.rhs_preserved e.plan first last eq
    (fun k h => by
      have read : k ∈ (equations e.plan).flatMap (inputNames e.plan) :=
        List.mem_flatMap.mpr ⟨eq,located,h⟩
      exact agree k (by simp [protect,read]))
  change CommonNominalFullCarrier.Equivalent (last eq.target).1 (rhs e.plan first eq)
  rw [valueEq]
  rcases List.mem_append.mp located with emitted|child
  · exact held.2.2.2.1 eq emitted
  · obtain ⟨clause,_,inChild⟩ := List.mem_flatMap.mp child
    exact held.2.2.2.2.1 clause.val clause.property _ eq inChild

/-- An exact criterion relative to the chosen protected starting assignment.
It is not a claim that all candidates pass the criterion or that different
starting assignments agree on prospective write terms. -/
theorem exact {s : State roles} {e : Effect roles} {first : Assignment} {semantic : List Nat}
    (aligned : e.plan.packet.context = s.core.erased.current.context)
    (support : Support s semantic)
    (valid : Models s first) (head : HeadModels e.plan.packet first)
    (schema : SchemaHolds e.plan e.plan.headSchema first) (live : e.Live s.core first) :
    (∃ last, Agree (protect s e semantic) first last ∧ Residual s e last) ↔
    Coherent (rows e.plan first) ∧ Protected (rows e.plan first) (protect s e semantic) first := by
  constructor
  · rintro ⟨last,same,held⟩
    exact requirements same held
  · rintro ⟨coherent,fixed⟩
    refine ⟨GeneralFiniteTypedWrites312.applyWrites (rows e.plan first) (protect s e semantic) first,?_,?_⟩
    · exact GeneralFiniteTypedWrites312.preserved (rows e.plan first) (protect s e semantic) first
    · exact GeneralVersionedJointWrites312.complete aligned support valid head schema live coherent fixed

end Yulang.GeneralVersionedJointWriteExact312
