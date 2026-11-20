import Yulang.GeneralDeferredLadderOutcomes302
import Yulang.GeneralNominalCenteredHeadMatPlanData
import Yulang.GeneralNominalVersionedPacketFrame236

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeferredLadderTransport302
open GeneralNominalCenters
open GeneralNominalCenteredHeadMatPlanData (Same)
open GeneralNominalReportErasure (Data checks_exact)
open GeneralNominalVersionedFrame231 (frame capture binder childSite children)
open GeneralNominalVersionedPlans231
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarations (Clause Registry)
open GeneralNominalAllocation (Bindings)
open GeneralNominalSaturationState (Packet)

theorem capture_seed (raw next : GeneralNominalState.State) (same : raw.seed = next.seed)
    (registry : Registry) (owner key : Nat) (data : Bindings) :
    GeneralNominalVersionedAllocation231.capture raw registry owner key data =
      GeneralNominalVersionedAllocation231.capture next registry owner key data := by
  simp only [GeneralNominalVersionedAllocation231.capture,GeneralNominalAllocation.source,same]

theorem frame_eq {p q : Plan roles} (same : Same p q) : frame p.packet = frame q.packet := by
  unfold frame
  have occur := GeneralNominalCenteredHeadMatPlanData.occurrence same
  have bindings := GeneralNominalCenteredHeadMatPlanData.bindings same
  simp only [same.registry,occur,bindings,capture_seed _ _ same.seed,
    GeneralNominalPacketCodes.allocation_seed _ _ same.seed,GeneralNominalAllocation.source,same.seed]

theorem capture_eq {p q : Plan roles} (same : Same p q) : capture p.packet = capture q.packet := by
  unfold capture
  rw [frame_eq same,same.declaration]

theorem binder_eq {p q : Plan roles} (same : Same p q) (name : Nat) : binder p name = binder q name := by
  rw [GeneralNominalVersionedFrame231.binder_eq,GeneralNominalVersionedFrame231.binder_eq,
    GeneralNominalCenteredHeadMatPlanData.binder same]

theorem variables_eq {p q : Plan roles} (same : Same p q) (m : Assignment) :
    variables p m = variables q m := by
  funext mode name
  unfold variables
  rw [same.declaration,binder_eq same,capture_eq same]

theorem children_eq {p q : Plan roles} (same : Same p q) :
    children p.packet = children q.packet := by
  rcases p with ⟨⟨regP,ctxP,siteP,declP,proofP,boundsP⟩,inputP,exactP⟩
  rcases q with ⟨⟨regQ,ctxQ,siteQ,declQ,proofQ,boundsQ⟩,inputQ,exactQ⟩
  have regEq : regP = regQ := same.registry
  have declEq : declP = declQ := same.declaration
  subst regQ
  subst declQ
  unfold children
  rw [frame_eq same,GeneralNominalCenteredHeadMatPlanData.occurrence same]

theorem child_eq {p q : Plan roles} (same : Same p q) (clause : Clause) (cert : clause.Signature roles) :
    childSite p clause cert = childSite q clause cert := by
  have child : GeneralNominalVersionedFrame231.clauseChild p.packet clause cert =
      GeneralNominalVersionedFrame231.clauseChild q.packet clause cert := by
    unfold GeneralNominalVersionedFrame231.clauseChild
    rw [frame_eq same,GeneralNominalCenteredHeadMatPlanData.occurrence same,same.declaration,capture_eq same]
  let mk (o : GeneralSourceDictionaries.Occurrence roles) (r : o.demand.role = clause.role) : Site roles :=
    ⟨o,fun i => q.emittedCenter clause.id i.val (getElem clause.arguments i.val (by
      rw [cert.1,← r]
      exact i.isLt))⟩
  have build {a b : GeneralSourceDictionaries.Occurrence roles} (r : a.demand.role = clause.role)
      (s : b.demand.role = clause.role) (e : a = b) : mk a r = mk b s := by
    cases e
    rfl
  unfold childSite
  simp only [GeneralNominalVersionedFrame231.emittedCenter_eq,
    GeneralNominalCenteredHeadMatPlanData.emitted_center same]
  exact build rfl rfl child

theorem emitted_eq {p q : Plan roles} (same : Same p q) : emittedSchema p = emittedSchema q := by
  rcases p with ⟨⟨regP,ctxP,siteP,declP,proofP,boundsP⟩,inputP,exactP⟩
  rcases q with ⟨⟨regQ,ctxQ,siteQ,declQ,proofQ,boundsQ⟩,inputQ,exactQ⟩
  have regEq : regP = regQ := same.registry
  have declEq : declP = declQ := same.declaration
  subst regQ
  subst declQ
  unfold emittedSchema emittedRequests
  rw [same.interpretation,capture_eq same,frame_eq same,GeneralNominalCenteredHeadMatPlanData.occurrence same]

theorem ordinary_iff {p q : Plan roles} (same : Same p q) (m : Assignment) :
    Ordinary p.packet m ↔ Ordinary q.packet m := by
  have checks := congrArg Data.selfChecks same.report
  simp only [checks_exact] at checks
  unfold Ordinary GeneralNominalVersionedAllocation231.merges
  rw [GeneralNominalCenteredHeadMatPlanData.bindings same,same.registry,
    GeneralNominalCenteredHeadMatPlanData.occurrence same,same.declaration,checks,
    capture_seed _ _ same.seed]

theorem inputs_iff {p q : Plan roles} (same : Same p q) (m : Assignment) :
    Inputs p m ↔ Inputs q m := by
  unfold Inputs
  have needed := GeneralNominalCenteredHeadMatPlanData.needed same
  have childSchema : ∀ c (cert : c.Signature roles), childSchema p c cert = childSchema q c cert := by
    intro c cert
    rw [GeneralNominalVersionedPlans231.childSchema_eq,GeneralNominalVersionedPlans231.childSchema_eq,
      GeneralNominalCenteredHeadMatPlanData.child_schema same]
  have schema (body) : SchemaHolds p body m ↔ SchemaHolds q body m := by
    unfold SchemaHolds
    simp only [binder_eq same,capture_eq same,same.declaration]
  simp only [ordinary_iff same,GeneralNominalCenteredHeadMatPlanData.projections same,
    same.input,needed,same.declaration,binder_eq same,capture_eq same,
    GeneralNominalCenteredHeadMatPlanData.head_schema same,schema,emitted_eq same,
    variables_eq same,child_eq same,childSchema]

theorem held_of_reindex {p q : Plan roles} (same : Same p q) (m : Assignment) (past : Holds p m)
    (newContext : GeneralNominalState.Models q.packet.context.state m) : Holds q m := by
  refine ⟨newContext,(inputs_iff same m).mp past.2.1,?_⟩
  have result := past.2.2
  unfold Outputs at result ⊢
  rwa [emitted_eq same,variables_eq same] at result

end Yulang.GeneralDeferredLadderTransport302
