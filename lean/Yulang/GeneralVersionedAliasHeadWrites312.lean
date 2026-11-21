import Yulang.GeneralVersionedAliasReadback312
import Yulang.GeneralVersionedSelectedJointHead312
import Yulang.GeneralFiniteTypedWrites312
import Yulang.GeneralNominalVersionedResidualFrame237

set_option backward.isDefEq.respectTransparency false
/-! Build current actual-binder assignments from one aliased historical
head. Preserve model/head constraints and actual origin reads. Even a newly
allocated current binder is compared to a real old binder in the same base
assignment; no current HeadEquations witness is assumed here. -/
namespace Yulang.GeneralVersionedAliasHeadWrites312
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedPlans231 (HeadModels SchemaHolds)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralNominalVersionedDiagnostic232 (HeadEquations)
open GeneralNominalVersionedFrame231 (binder)
open GeneralNominalVersionedModelSupport237 (Support)
open GeneralNominalCenteredModelExtension (originSource)
open GeneralNominalCenteredFrame179 (Agree)
open GeneralNominalOriginTerms (Same)
open GeneralNominalRecursiveInspection (Observes)
open GeneralNominalCommonBridge (Assignment)
open GeneralFiniteTypedWrites312 (Write Coherent Protected applyWrites symmetric transitive)
variable {roles : Roles.RoleDecls}

def rows (now past : Plan roles) (m : Assignment) : List Write :=
  now.headSchema.variables.map fun use => (binder now use.name,(m (past.binder use.name)).1)

def pool (p : Plan roles) (names : List Nat) : List Nat :=
  names ++ GeneralNominalVersionedResidualFrame237.headSources p.packet ++
    p.headSchema.tests.map (fun test => originSource test.1) ++
    p.headSchema.variables.map (fun use => originSource use.origin)

theorem source_retarget {m n : Assignment} {origin target previous}
    (current : m (originSource origin) = n (originSource origin))
    (was : Same m origin (.source previous))
    (targetType : CommonNominalFullCarrier.Equivalent (n target).1 (m previous).1) :
    Same n origin (.source target) := by
  constructor
  · obtain ⟨value,seen⟩ := was.1
    exact ⟨value,(GeneralNominalCenteredFrame179.observes_iff origin current value).mp seen⟩
  refine ⟨⟨_,.source _⟩,?_⟩
  intro x y hx hy
  cases hy
  have old := (GeneralNominalCenteredFrame179.observes_iff origin current x).mpr hx
  exact transitive (was.2.2 x _ old (.source previous)) (symmetric targetType)

theorem complete {registry : Registry} {root : Occurrence roles} {s : State roles} {now past : Plan roles}
    (checked : (boundary roles).Checked registry)
    (path : B4TargetV8.Reachable (boundary roles) registry root s)
    (frame : Frame (Compiled registry) s.core focus key now)
    (history : past ∈ s.plans)
    (alias : GeneralNominalSaturationState.Alias s.core.erased.current
      now.packet.site.occurrence.identity past.packet.site.occurrence.identity)
    (sameRule : now.packet.declaration = past.packet.declaration)
    (supported : Support s names) (m : Assignment) (valid : Models s m) (head : HeadModels now.packet m)
    (coherence : Coherent (rows now past m))
    (fixed : Protected (rows now past m) (pool now names) m) :
    let next := applyWrites (rows now past m) (pool now names) m
    Models s next ∧ HeadModels now.packet next ∧ HeadEquations now next := by
  let next := applyWrites (rows now past m) (pool now names) m
  have agrees := GeneralFiniteTypedWrites312.preserved (rows now past m) (pool now names) m
  have modelNext := (supported m next (fun k h => agrees k (by simp [pool,h]))).mp valid
  have rawOld : GeneralNominalState.Models now.packet.context.state m := by
    rw [frame.context_eq]
    exact valid.1.1
  have rawNew : GeneralNominalState.Models now.packet.context.state next := by
    rw [frame.context_eq]
    exact modelNext.1.1
  have headNext := (GeneralNominalVersionedResidualFrame237.head_models_iff now.packet rawOld rawNew
    (fun k h => agrees k (by simp [pool,h]))).mp head
  obtain ⟨tests,binders⟩ := GeneralVersionedAliasReadback312.readback checked path history frame.center_recorded
    frame.context_eq alias sameRule valid
  have writes := GeneralFiniteTypedWrites312.solves (rows now past m) (pool now names) m coherence fixed
  have schema : SchemaHolds now now.headSchema next := by
    constructor
    · intro test present
      have read : originSource test.1 ∈ now.headSchema.tests.map (fun test => originSource test.1) :=
        List.mem_map.mpr ⟨test,present,rfl⟩
      exact (GeneralNominalCenteredFrame179.head_iff test.1 test.2 (agrees _ (by simp [pool,read]))).mp (tests test present)
    · intro use present
      have actual := GeneralNominalHeadSchemaNames186.head_actual now use present
      simp only [actual,ite_true]
      have read : originSource use.origin ∈ now.headSchema.variables.map (fun use => originSource use.origin) :=
        List.mem_map.mpr ⟨use,present,rfl⟩
      have entry : (binder now use.name,(m (past.binder use.name)).1) ∈ rows now past m :=
        List.mem_map.mpr ⟨use,present,rfl⟩
      exact source_retarget (agrees _ (by simp [pool,read])) (binders use present) (writes _ entry)
  exact ⟨modelNext,headNext,GeneralVersionedSelectedJointHead312.head_of_schema frame modelNext headNext schema⟩

end Yulang.GeneralVersionedAliasHeadWrites312
