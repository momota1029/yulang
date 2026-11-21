import Yulang.GeneralVersionedComputedRows313

set_option backward.isDefEq.respectTransparency false
/-! First-install output collision checking is exact. Apart from agreement
on genuinely shared purpose-5 addresses, all compound where and child rows
are complete on the same chosen head/class model. -/
namespace Yulang.GeneralVersionedFirstComputed313
open GeneralNominalCenters GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedTraceSupport237 (Reachable)
open GeneralVersionedFirstHead313 (names)
open GeneralVersionedFirstInternal313 (taut_protected cell_free sites_covered)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralVersionedComputedRows313 (OutputCell KeyCoherent classifies addresses_disjoint row_present)
open GeneralVersionedCompoundRows313 (Cell coherent_address address)
open GeneralVersionedRootWrites312 (inner internalRows)
open GeneralVersionedJointWrites312 (protect rhs)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open GeneralNominalVersionedMixedMaterialization237 (Residual)
open GeneralNominalVersionedPlans231 (HeadModels SchemaHolds)
open GeneralNominalCommonBridge (Assignment)
open GeneralFiniteTypedWrites312 (reflexive symmetric transitive)
open CommonNominalFullCarrier (Equivalent)

def Compatible (p : Plan roles) (m : Assignment) : Prop :=
  ∀ a b, OutputCell p a → OutputCell p b →
    a.target = b.target → Equivalent (rhs p m a) (rhs p m b)

theorem proper_keys (p : Plan roles) (keys : KeyCoherent p.packet.declaration) (m : Assignment) :
    Compatible p m := by
  intro a b left right same
  rw [GeneralVersionedComputedRows313.output_coherent keys left right same]
  exact reflexive _

theorem output_free {s : State roles} {e : Effect roles}
    (actual : Reachable registry root s) (empty : s.plans = [])
    (frame : Frame (Compiled registry) s.core focus key e.plan)
    {q : GeneralNominalCenteredHeadMatSchemas.Equation} (cell : OutputCell e.plan q) :
    q.target ∉ protect s e (names s) := by
  obtain ⟨_,_,rule,_,_,_,target,_⟩ := cell
  intro present
  have protectedName := GeneralVersionedFirstFootprint313.protected_names actual empty frame _ present
  rw [target] at protectedName
  exact GeneralVersionedPrivateWriteNames313.excludes _ _ _ 5 (by decide) protectedName

theorem table {s : State roles} {e : Effect roles}
    (actual : Reachable registry root s) (empty : s.plans = [])
    (frame : Frame (Compiled registry) s.core focus key e.plan) (m : Assignment)
    (outputs : Compatible e.plan m) :
    GeneralVersionedRootWrites312.FreeCoherent (internalRows e.plan m) (protect s e (names s)) ∧
    GeneralFiniteTypedWrites312.Protected (internalRows e.plan m) (protect s e (names s)) m := by
  constructor
  · intro a aMem b bMem same free
    obtain ⟨one,ho,rfl⟩ := List.mem_map.mp aMem
    obtain ⟨two,ht,rfl⟩ := List.mem_map.mp bMem
    have fromOne := (classifies e.plan _ ho).resolve_left (fun taut => free (taut_protected ho taut))
    have fromTwo := (classifies e.plan _ ht).resolve_left (fun taut => free (same.symm ▸ taut_protected ht taut))
    rcases fromOne with first|first <;> rcases fromTwo with last|last
    · rw [coherent_address first last same]
      exact reflexive _
    · exact False.elim (addresses_disjoint first last same)
    · exact False.elim (addresses_disjoint last first same.symm)
    · exact outputs _ _ first last same
  · intro row present protectedName
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp present
    rcases classifies e.plan q hq with taut|cell|cell
    · exact taut m
    · exact False.elim (cell_free actual empty frame cell protectedName)
    · exact False.elim (output_free actual empty frame cell protectedName)

theorem residual_compatible {s : State roles} {e : Effect roles} {m : Assignment}
    (residual : Residual s e m) : Compatible e.plan m := by
  intro a b one two same
  have left := residual.2.2.2.1 a (row_present one)
  have right := residual.2.2.2.1 b (row_present two)
  unfold GeneralNominalCenteredHeadMatSchemas.Equation.Holds at left right
  rw [same] at left
  exact transitive (symmetric left) right

theorem exact {s : State roles} {e : Effect roles}
    (actual : Reachable registry root s) (empty : s.plans = [])
    (registryEq : e.registry = Compiled registry) (snapshot : e.snapshot = s.core) :
    (∃ m, Residual s e m) ↔
    ∃ m, Models s m ∧ HeadModels e.plan.packet m ∧ SchemaHolds e.plan e.plan.headSchema m ∧
      e.Live s.core m ∧ Compatible e.plan m := by
  constructor
  · rintro ⟨m,residual⟩
    exact ⟨m,residual.1,residual.2.1,residual.2.2.1,residual.2.2.2.2.2,residual_compatible residual⟩
  · rintro ⟨m,valid,head,schema,live,outputs⟩
    have frame : Frame (Compiled registry) s.core e.plan.packet.site.occurrence e.plan.packet.declaration.id e.plan :=
      registryEq ▸ snapshot ▸ e.frame
    obtain ⟨free,fixed⟩ := table actual empty frame m outputs
    obtain ⟨coherent,preserved⟩ := GeneralVersionedRootWrites312.lift_table snapshot live free fixed
    exact ⟨_,GeneralVersionedJointWrites312.complete frame.context_eq
      (GeneralVersionedBeforeFirstInstall313.support_initial actual empty) valid head schema live coherent preserved⟩

theorem joint {s : State roles} {e : Effect roles}
    (checked : (boundary roles).Checked registry) (actual : Reachable registry root s)
    (empty : s.plans = [])
    (pick : Local registry s e.plan.packet.site.occurrence (.selected e.plan.packet.declaration.id children))
    (registryEq : e.registry = Compiled registry) (snapshot : e.snapshot = s.core)
    (inhabited : ∃ m, Models s m)
    (keys : KeyCoherent e.plan.packet.declaration) : ∃ m, Residual s e m := by
  have frame : Frame (Compiled registry) s.core e.plan.packet.site.occurrence e.plan.packet.declaration.id e.plan :=
    registryEq ▸ snapshot ▸ e.frame
  apply GeneralVersionedSelectedJointWrites312.joint_from_internal checked actual pick registryEq snapshot
    (GeneralVersionedBeforeFirstInstall313.support_initial actual empty) (sites_covered actual empty)
    (GeneralVersionedFirstFootprint313.class_aggregate_free actual empty frame)
    (GeneralVersionedFirstGroundHead313.head checked actual empty pick frame inhabited)
  intro m _ _ _ _
  exact table actual empty frame m (proper_keys e.plan keys m)

theorem installable {s : State roles} {e : Effect roles}
    (checked : (boundary roles).Checked registry) (actual : Reachable registry root s)
    (empty : s.plans = [])
    (pick : Local registry s e.plan.packet.site.occurrence (.selected e.plan.packet.declaration.id children))
    (registryEq : e.registry = Compiled registry) (snapshot : e.snapshot = s.core)
    (inhabited : ∃ m, Models s m)
    (keys : KeyCoherent e.plan.packet.declaration) :
    GeneralNominalVersionedMixedKernel234.Installable (Compiled registry) s e := by
  refine (GeneralNominalVersionedMixedMaterialization237.source_installable_iff checked actual pick registryEq snapshot).mpr
    ⟨?_,joint checked actual empty pick registryEq snapshot inhabited keys⟩
  intro prior recorded _
  rw [(GeneralNominalVersionedMixedChoiceHistory236.reachable actual).2,empty] at recorded
  cases recorded

end Yulang.GeneralVersionedFirstComputed313
