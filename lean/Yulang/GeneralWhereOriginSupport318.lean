import Yulang.GeneralWhereOriginConfig318

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 26000
set_option maxHeartbeats 22000000
namespace Yulang.GeneralWhereOriginSupport318
open GeneralNominalCenters (Plan)
open GeneralNominalVersionedPlans231 (HeadModels SchemaHolds childSchema variables)
open GeneralNominalVersionedFrame231 (capture binder)
open GeneralWhereVersionCompiler317 (child schema)
open GeneralWhereVersionSemantics317 (Holds)
open GeneralNominalVersionedPacketFrame236 (headSources head_models_iff captureSources captures_iff)
open GeneralNominalCenteredFrame179 (Agree siteSources site_iff)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryDefault214ActualBodyFrame (classSources)
open GeneralWhereVersionInstall317 (Journal Models)
open GeneralNominalVersionedEffects231 (ClassEffects)
open GeneralNominalVersionedExpressionFrame236 (schemaSources)
open GeneralNominalVersionedJournalFrame236 (class_iff)

variable {first last : Assignment}

def childrenSupport (p : Plan rs) : List Nat :=
  p.packet.declaration.requirements.attach.flatMap fun x =>
    let sig := p.packet.checked.signature.2.2.2 x.val x.property
    siteSources (child p x.val sig) ++ schemaSources p (childSchema p x.val sig)

def planSources (p : Plan rs) : List Nat :=
  headSources p.packet ++ siteSources p.input ++ captureSources p ++
  GeneralNominalVersionedHeadFrame236.schemaSources p p.headSchema ++
  schemaSources p (schema p) ++ childrenSupport p

theorem child_transport (p : Plan rs) (same : Agree (childrenSupport p) first last) (clause)
    (found : clause ∈ p.packet.declaration.requirements) (sig : clause.Signature rs) :
    ((child p clause sig).Holds first ∧ (childSchema p clause sig).Holds (variables p first) first) ↔
    ((child p clause sig).Holds last ∧ (childSchema p clause sig).Holds (variables p last) last) := by
  have inner : Agree (siteSources (child p clause sig) ++ schemaSources p (childSchema p clause sig)) first last := by
    intro n present
    exact same n (List.mem_flatMap.mpr ⟨⟨clause,found⟩,by simp,present⟩)
  exact and_congr (site_iff _ (fun n member => inner n (List.mem_append_left _ member)))
    (GeneralNominalVersionedExpressionFrame236.schema_iff _ _ (fun n member => inner n (List.mem_append_right _ member)))

theorem plan_holds (p : Plan rs) (same : Agree (planSources p) first last) :
    Holds p first ↔ Holds p last := by
  have head := head_models_iff p.packet (first := first) (last := last) (fun n h => same n (by simp [planSources,h]))
  have input := site_iff p.input (first := first) (last := last) (fun n h => same n (by simp [planSources,h]))
  have fits (n) (h) := captures_iff p (first := first) (last := last)
    (fun s uses => same s (by simp [planSources,uses])) n h
  have tests := GeneralNominalVersionedHeadFrame236.schema_iff p p.headSchema (first := first) (last := last)
    (fun n h => same n (by simp [planSources,h]))
  have rows := GeneralNominalVersionedExpressionFrame236.schema_iff p (schema p) (first := first) (last := last)
    (fun n h => same n (by simp [planSources,h]))
  have children (clause) (found) (sig) := child_transport p
    (first := first) (last := last) (fun n h => same n (by simp [planSources,h])) clause found sig
  constructor
  · intro h
    exact ⟨head.mp h.head,input.mp h.input,fun n uses => (fits n uses).mp (h.captures n uses),
      tests.mp h.headSchema,h.materialized,rows.mp h.rows,fun c atC sig => (children c atC sig).mp (h.childSemantics c atC sig)⟩
  · intro h
    exact ⟨head.mpr h.head,input.mpr h.input,fun n uses => (fits n uses).mpr (h.captures n uses),
      tests.mpr h.headSchema,h.materialized,rows.mpr h.rows,fun c atC sig => (children c atC sig).mpr (h.childSemantics c atC sig)⟩

noncomputable def journalSources (j : Journal rs) : List Nat :=
  GeneralNominalVersionedJournalFrame236.sources j.mixed ++
    j.versionedWhere.flatMap fun p =>
      planSources p ++ classSources j.mixed.core p.packet.site.occurrence p

theorem journal_models (j : Journal rs) (same : Agree (journalSources j) first last) :
    Models j first ↔ Models j last := by
  apply and_congr (GeneralNominalVersionedJournalFrame236.models_iff j.mixed
    (fun n h => same n (List.mem_append_left _ h)))
  apply forall_congr'; intro p
  apply forall_congr'; intro present
  have inner : Agree (planSources p ++ classSources j.mixed.core p.packet.site.occurrence p) first last := by
    intro n h
    exact same n (List.mem_append_right _ (List.mem_flatMap.mpr ⟨p,present,h⟩))
  exact and_congr (plan_holds p (fun n h => inner n (List.mem_append_left _ h)))
    (class_iff _ _ _ (fun n h => inner n (List.mem_append_right _ h)))

end Yulang.GeneralWhereOriginSupport318
