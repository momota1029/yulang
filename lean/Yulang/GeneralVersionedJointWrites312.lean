import Yulang.GeneralFiniteTypedWrites312
import Yulang.GeneralNominalVersionedMixedMaterialization237
import Yulang.GeneralNominalVersionedResidualFrame237

set_option backward.isDefEq.respectTransparency false
/-! One finite table covers both emitted and ordered child equations. Its
right-hand-side reads are frozen before any write. Thus an existential full
materialization is constructed from one known head/class assignment, rather
than assumed by means of another witness. -/
namespace Yulang.GeneralVersionedJointWrites312
open GeneralNominalCenters
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredFrame179 (Agree)
open GeneralNominalCenteredHeadMatSchemas (Equation Schema)
open GeneralNominalCenteredHeadMatExpressions (value)
open GeneralNominalVersionedJournal232 (State Models Effect)
open GeneralNominalVersionedPlans231 (HeadModels SchemaHolds childSchema emittedSchema variables)
open GeneralNominalVersionedExpressionFrame236 (variableSource reads variable_value value_eq)
open GeneralNominalVersionedMixedMaterialization237 (Residual)
open GeneralFiniteTypedWrites312 (Write Coherent Protected applyWrites)
open GeneralDictionaryDefault214ActualBodyFrame (classSources)
open GeneralNominalVersionedModelSupport237 (Support)

def equations (p : Plan roles) : List Equation :=
  (emittedSchema p).equations ++
    p.packet.declaration.requirements.attach.flatMap fun clause =>
      (childSchema p clause.val (p.packet.checked.signature.2.2.2 clause.val clause.property)).equations

def inputNames (p : Plan roles) (e : Equation) : List Nat :=
  (reads e.mode e.expression).map fun input => variableSource p input.1 input.2

def rhs (p : Plan roles) (m : Assignment) (e : Equation) :=
  value (variables p m) e.mode e.expression

def rows (p : Plan roles) (m : Assignment) : List Write :=
  (equations p).map fun e => (e.target,rhs p m e)

noncomputable def protect (s : State roles) (e : Effect roles) (semantic : List Nat) : List Nat :=
  semantic ++ GeneralNominalVersionedResidualFrame237.headSources e.plan.packet ++
  GeneralNominalVersionedHeadFrame236.schemaSources e.plan e.plan.headSchema ++
  classSources s.core e.plan.packet.site.occurrence e.plan ++
  (equations e.plan).flatMap (inputNames e.plan)

theorem rhs_preserved (p : Plan roles) (m n : Assignment) (e : Equation)
    (same : Agree (inputNames p e) m n) : rhs p m e = rhs p n e := by
  apply value_eq
  intro input member
  simp only [variable_value]
  exact congrArg Prod.fst (same _ (List.mem_map.mpr ⟨input,member,rfl⟩))

theorem emitted_in (p : Plan roles) {e : Equation} (member : e ∈ (emittedSchema p).equations) :
    e ∈ equations p := List.mem_append_left _ member

theorem child_in (p : Plan roles) (clause : GeneralDeclarations.Clause)
    (member : clause ∈ p.packet.declaration.requirements) (signature : clause.Signature roles)
    {e : Equation} (inside : e ∈ (childSchema p clause signature).equations) :
    e ∈ equations p := by
  apply List.mem_append_right
  exact List.mem_flatMap.mpr ⟨⟨clause,member⟩,List.mem_attach _ _,inside⟩

theorem full_write (p : Plan roles) (m n : Assignment)
    (same : Agree ((equations p).flatMap (inputNames p)) m n)
    (realized : ∀ row ∈ rows p m, GeneralFiniteTypedWrites312.Holds n row) :
    ∀ e ∈ equations p, e.Holds (variables p n) n := by
  intro e present
  have held := realized (e.target,rhs p m e) (List.mem_map.mpr ⟨e,present,rfl⟩)
  change CommonNominalFullCarrier.Equivalent (n e.target).1 (rhs p m e) at held
  rw [rhs_preserved p m n e (fun k h => same k (List.mem_flatMap.mpr ⟨e,present,h⟩))] at held
  exact held

/-- Protects the journal, head, live class and every actual RHS read. An
existing target must already agree; only targets outside that set are written.
This theorem does not assume that further outputs or child equations hold. -/
theorem complete {s : State roles} {e : Effect roles} {m : Assignment}
    (aligned : e.plan.packet.context = s.core.erased.current.context)
    (support : Support s semantic)
    (valid : Models s m) (head : HeadModels e.plan.packet m)
    (schema : SchemaHolds e.plan e.plan.headSchema m) (live : e.Live s.core m)
    (coherent : Coherent (rows e.plan m))
    (fixed : Protected (rows e.plan m) (protect s e semantic) m) :
    Residual s e (applyWrites (rows e.plan m) (protect s e semantic) m) := by
  let patch := applyWrites (rows e.plan m) (protect s e semantic) m
  have same := GeneralFiniteTypedWrites312.preserved (rows e.plan m) (protect s e semantic) m
  have unchanged : Models s patch := (support m patch (fun k h => same k (by simp [protect,h]))).mp valid
  have baseOriginal : GeneralNominalState.Models e.plan.packet.context.state m := by
    rw [aligned]
    exact valid.1.1
  have baseNew : GeneralNominalState.Models e.plan.packet.context.state patch := by
    rw [aligned]
    exact unchanged.1.1
  have sameHead := (GeneralNominalVersionedResidualFrame237.head_models_iff e.plan.packet baseOriginal baseNew
    (fun k h => same k (by simp [protect,h]))).mp head
  have sameSchema := (GeneralNominalVersionedHeadFrame236.schema_iff e.plan e.plan.headSchema
    (first := m) (last := patch) (fun k h => same k (by simp [protect,h]))).mp schema
  have sameLive : e.Live s.core patch :=
    (GeneralNominalVersionedJournalFrame236.class_iff s.core e.plan.packet.site.occurrence e.plan
      (first := m) (last := patch) (fun k h => same k (by simp [protect,h]))).mp live
  have realized := full_write e.plan m patch (fun k h => same k (by simp [protect,h]))
    (GeneralFiniteTypedWrites312.solves (rows e.plan m) (protect s e semantic) m coherent fixed)
  exact ⟨unchanged,sameHead,sameSchema,
    (fun eq present => realized eq (emitted_in e.plan present)),
    (fun clause member signature eq present => realized eq (child_in e.plan clause member signature present)),sameLive⟩

end Yulang.GeneralVersionedJointWrites312
