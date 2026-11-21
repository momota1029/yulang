import Yulang.GeneralVersionedChildEndpointCut315
import Yulang.GeneralDictionaryDefaultBodyTransport209

set_option backward.isDefEq.respectTransparency false
/-! Same-owner revisits do not need a separate class-output model.
The old effect already covers today's alias requests in every live
assignment; only scoped actual binders/default centers are transported. -/
namespace Yulang.GeneralVersionedHistoricalClasses315
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedTraceSupport237 (Reachable)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralNominalVersionedPlans231 (HeadModels SchemaHolds)
open GeneralNominalVersionedEffects231 (ClassEffects BodyHolds body_holds_iff)
open GeneralDictionaryAssociatedProvenance (Body lookup lookup_exact)
open GeneralNominalCenteredHeadMatEffects (compileBody body_equation)
open GeneralNominalCenteredHeadOutputs (requests mem_requests_iff)
open GeneralNominalCommonBridge (Assignment)
open GeneralFiniteTypedWrites312 (transitive)
open CommonNominalFullCarrier (Equivalent)
open GeneralVersionedEndpointEquationCut315 (EndpointEquations)
open GeneralNominalVersionedMixedMaterialization237 (Residual)

theorem same_requests {state : GeneralNominalCenteredSteps.State roles}
    {p q : Occurrence roles} (eq : p.identity = q.identity) (out : GeneralSourceState.Output) :
    out ∈ requests state p ↔ out ∈ requests state q := by
  simp only [mem_requests_iff,eq]

theorem body {s : State roles} {p q : Plan roles}
    (checked : (boundary roles).Checked registry) (actual : Reachable registry root s)
    (frame : Frame (Compiled registry) s.core focus key p)
    (stored : q ∈ s.plans)
    (owner : q.packet.site.occurrence.identity = p.packet.site.occurrence.identity)
    (rule : q.packet.declaration = p.packet.declaration)
    (m : Assignment) (valid : Models s m) (schema : SchemaHolds p p.headSchema m)
    (target name : Nat) (b : Body) (found : lookup roles p.packet.declaration name = some b)
    (past : BodyHolds q target m b) : BodyHolds p target m b := by
  have config := GeneralVersionedSiteOrigins312.stored_current_config actual stored
  have oldCatalogue : q.packet.registry.constructors = p.packet.registry.constructors :=
    congrArg Registry.constructors (((GeneralNominalVersionedMixedRegistry234.reachable actual).2.1 q stored).trans frame.registry_eq.symm)
  have oldInterp := config.2.2.trans (congrArg GeneralNominalCandidates.Context.interpretation frame.context_eq).symm
  have compiled := GeneralDictionaryDefaultBodyTransport209.compile_equal oldCatalogue oldInterp b
  apply (body_holds_iff p target m b).mpr
  have earlier := (body_holds_iff q target m b).mp past
  cases trans : compileBody p b with
  | none =>
    simp [GeneralNominalCenteredHeadMatEffects.BodyHolds,GeneralNominalCenteredHeadMatEffects.bodySchema,
      trans,GeneralNominalCenteredHeadMatSchemas.Schema.Holds]
  | some code =>
    have oldCode : compileBody q b = some code := compiled.trans trans
    cases b with
    | explicit eq =>
      have declaration := (lookup_exact roles p.packet.declaration p.packet.checked.identified.2.2.1 name
        (.explicit eq)).mp found
      cases declaration with
      | explicit _ inDecl _ =>
        have values := GeneralVersionedRevisitActual314.same_value checked actual frame stored owner rule
          m valid schema eq.rhs trans (fun n member => p.packet.checked.scope.2.1 eq inDecl n member)
        have oldCorrect := (body_equation oldCode).mp earlier
        apply (body_equation trans).mpr
        change Equivalent (m target).1
          (GeneralNominalCenteredHeadMatExpressions.value (GeneralNominalCenteredHeadMatEffects.variables p m) .actual code)
        change Equivalent (m target).1
          (GeneralNominalCenteredHeadMatExpressions.value (GeneralNominalCenteredHeadMatEffects.variables q m) .actual code)
          at oldCorrect
        rw [← GeneralNominalVersionedEffects231.actual_expression] at oldCorrect ⊢
        exact transitive oldCorrect values
    | default role key rhs =>
      obtain ⟨ctx,origins⟩ := GeneralVersionedSiteOrigins312.reached actual
      have centers := GeneralVersionedIdentityCenters312.same_identity checked actual valid q.input p.input
        (origins.input q stored) frame.center_recorded
        ((congrArg (fun o : Occurrence roles => o.identity) q.input_exact).trans
          (owner.trans (congrArg (fun o : Occurrence roles => o.identity) p.input_exact).symm))
      apply (GeneralDictionaryDefaultBodyTransport209.body_holds_iff oldCode trans ?_).mp earlier
      intro index used
      exact (centers index).2.2 _ _ (.source _) (.source _)

theorem live {s : State roles} {p q : Plan roles}
    (checked : (boundary roles).Checked registry) (actual : Reachable registry root s)
    (selected : Local registry s focus (.selected key kids))
    (frame : Frame (Compiled registry) s.core focus key p)
    (stored : q ∈ s.plans)
    (owner : q.packet.site.occurrence.identity = p.packet.site.occurrence.identity)
    (m : Assignment) (valid : Models s m) (schema : SchemaHolds p p.headSchema m) :
    ClassEffects s.core p.packet.site.occurrence p m := by
  have same := GeneralVersionedHistoricalHead314.declaration checked actual selected frame valid stored owner
  obtain ⟨e,history,planEq⟩ := GeneralVersionedSiteOrigins312.stored_effect actual stored
  have old : ClassEffects s.core q.packet.site.occurrence q m := by
    have t := (valid.2.2 e history).2
    unfold Effect.Live at t
    rw [planEq] at t
    exact t
  refine ⟨?_,?_⟩
  · intro out requested b lookupNew
    have earlier := old.1 out ((same_requests owner out).mpr requested) b (same ▸ lookupNew)
    exact body checked actual frame stored owner same m valid schema out.target out.name b lookupNew earlier
  · intro first firstIn last lastIn named
    exact old.2 first ((same_requests owner first).mpr firstIn)
      last ((same_requests owner last).mpr lastIn) named

theorem residual_iff {s : State roles} {e : Effect roles}
    (checked : (boundary roles).Checked registry) (actual : Reachable registry root s)
    (selected : Local registry s e.plan.packet.site.occurrence (.selected e.plan.packet.declaration.id kids))
    (rg : e.registry = Compiled registry) (snapshot : e.snapshot = s.core)
    (inhabited : ∃ m, Models s m) :
    (∃ m, Residual s e m) ↔
      (∀ prior ∈ s.plans, prior.packet.site.occurrence.identity ≠ e.plan.packet.site.occurrence.identity) ∨
      ∃ m, Models s m ∧ HeadModels e.plan.packet m ∧ SchemaHolds e.plan e.plan.headSchema m ∧ EndpointEquations s e m := by
  constructor
  · rintro ⟨m,found⟩
    have ready := GeneralVersionedEndpointEquationCut315.ready_of_residual found
    exact .inr ⟨m,ready.1,ready.2.1,ready.2.2.1,ready.2.2.2.2⟩
  · rintro (unseen|⟨m,valid,head,schema,endpoints⟩)
    · exact GeneralVersionedNewOwnerInstall314.joint checked actual unseen selected rg snapshot inhabited
    · classical
      by_cases history : ∃ q ∈ s.plans, q.packet.site.occurrence.identity = e.plan.packet.site.occurrence.identity
      · obtain ⟨q,stored,owner⟩ := history
        have frame : Frame (Compiled registry) s.core e.plan.packet.site.occurrence e.plan.packet.declaration.id e.plan :=
          rg ▸ snapshot ▸ e.frame
        exact GeneralVersionedEndpointEquationCut315.from_ready checked actual selected rg snapshot
          ⟨valid,head,schema,live checked actual selected frame stored owner m valid schema,endpoints⟩
      · exact GeneralVersionedNewOwnerInstall314.joint checked actual
          (fun q stored own => history ⟨q,stored,own⟩) selected rg snapshot inhabited

end Yulang.GeneralVersionedHistoricalClasses315
