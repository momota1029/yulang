import Yulang.GeneralSharedNamedInstall310
import Yulang.GeneralRebaseCompiledChildFresh277

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 25500
set_option maxHeartbeats 14000000
namespace Yulang.GeneralSharedNamedLeaf310
open GeneralSharedNamedSource310 (compiled leaf leaf_checked leafBody)
open GeneralSharedNamedPlan310 (loSite hiSite args_low args_high center_low center_high shared_receivers z)
open GeneralSharedNamedInstall310 (after installed_equality)
open GeneralDeclarationExamples (roles constructors)
open GeneralNominalExamples (state interpretation)
open GeneralDeclarations
open GeneralNominalCenters
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedPlans231
open GeneralNominalRecursiveInspection
open CommonNominalFullCarrier

inductive Side where | low | high deriving DecidableEq
abbrev site : Side → Site roles | .low => loSite | .high => hiSite
abbrev decl (_ : Side) := leaf
theorem sideChecked (side : Side) : DeclarationChecked constructors roles (decl side) :=
  leaf_checked

abbrev ctx := after.core.erased.current.context

abbrev one : Fin ctx.state.base.slots := (1 : Fin 2)

abbrev packet (side : Side) : GeneralNominalSaturationState.Packet roles :=
 ⟨compiled,ctx,(site side).observed,decl side,sideChecked side,[(one,one)]⟩
abbrev plan (side : Side) : Plan roles := ⟨packet side,site side,rfl⟩

theorem args (side : Side) (i : Fin (roles (site side).occurrence.demand.role).arity) :
    (site side).occurrence.demand.arguments i = (1,1) := by
  cases side
  · exact args_low i
  · exact args_high i

theorem center (side : Side) (i : Fin (roles (site side).occurrence.demand.role).arity) :
    (site side).center i = 1 := by
  cases side
  · exact center_low i
  · exact center_high i

theorem query (side : Side) : GeneralNominalInspection.queries ctx.state ctx.interpretation (decl side) = [.scalar .int] := by
  change GeneralNominalInspection.queries (state true) interpretation (decl side) = _
  cases side <;>
    simp [GeneralNominalInspection.queries,GeneralDeclarations.Declaration.normalHead,
      GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
      GeneralNominalInspection.translate,GeneralNominalExamples.interpretation]

theorem report (side : Side) : GeneralNominalPacketSupport.report (packet side) =
    { inspected := [(one,one)], checked := [(one,one),(one,one)] } := by
  unfold GeneralNominalPacketSupport.report GeneralNominalRecursiveCandidates.report
  have q : GeneralNominalInspection.queries (packet side).context.state (packet side).context.interpretation
      (packet side).declaration = _ := query side
  rw [q]
  have no : ctx.state.nominals (1 : Fin 2) = none := rfl
  have scalar : ctx.state.view.heads (1 : Fin 2) = .scalar .int := rfl
  change { inspectMany ctx.state [.scalar .int] [(one,one)] (fun _ => none) 0 with
    checked := [(one,one)] ++ (inspectMany ctx.state [.scalar .int] [(one,one)] (fun _ => none) 0).checked } = _
  simp [inspectMany,inspect,Report.visit,Report.append,no,scalar]

theorem bindings_empty (side : Side) : (packet side).bindings = [] := by
  change bindings ctx.state (GeneralNominalPacketSupport.report (packet side)) = []
  rw [report]
  rfl

theorem no_children (side : Side) : GeneralNominalVersionedFrame231.children (packet side) = [] := by
  unfold GeneralNominalVersionedFrame231.children GeneralDictionaryEmissionPlans.children
  rw [GeneralRebaseRetarget275.no_emission _ _ _ _ _ (show (decl side).requirements = [] from by cases side <;> rfl)]
  rfl

theorem named_requests (side : Side) : (site side).occurrence.demand.outputs = [⟨1,z⟩] := by
  cases side
  · exact shared_receivers.1
  · exact shared_receivers.2

theorem emitted_exact (side : Side) :
    emittedSchema (plan side) = ⟨[⟨z,.actual,.primitive (.scalar .int) []⟩],false⟩ := by
  unfold emittedSchema emittedRequests
  rw [GeneralRebaseRetarget275.no_emission _ _ _ _ _ rfl]
  cases side <;> rfl

theorem sharing_scalar (m : Assignment) (valid : Models after m) : Equivalent (m z).1 (.base .int) := by
  have eq := installed_equality m valid
  have int := valid.1.1.1.2.1 (1 : Fin 2) (.base .int) rfl
  exact ⟨subtype_trans eq.2 int.1,subtype_trans int.2 eq.1⟩

theorem head_schema (side : Side) : (plan side).headSchema = ⟨[],[(.source 1,.scalar .int)],false⟩ := by
  unfold Plan.headSchema
  rw [show GeneralNominalInspection.queries ctx.state ctx.interpretation (decl side) = _ from query side]
  cases side <;>
    simp [GeneralNominalMaterialization.schemas,GeneralNominalMaterialization.schema,
      GeneralNominalMaterialization.Schema.append,List.ofFn_succ,center_low,center_high]

theorem ordinary (side : Side) (m : Assignment) : Ordinary (packet side) m := by
  refine ⟨?_,?_,?_⟩
  · rw [bindings_empty]
    exact fun _ member => False.elim (List.not_mem_nil member)
  · cases side <;> intro a hit <;> cases hit
  · rw [report]
    simp [selfChecks,PresenceNormalForm.All]
    exact subtype_refl _

theorem holds (side : Side) (m : Assignment) (valid : Models after m) : Holds (plan side) m := by
  refine ⟨valid.1.1,⟨ordinary side m,?_,?_,?_,?_,?_,?_⟩,?_⟩
  · change ProjectionModels ctx.state (GeneralNominalPacketSupport.report (packet side)) m
    rw [report]; simp [ProjectionModels]
  · intro i
    change Subtype (m ((site side).occurrence.demand.arguments i).1).1 (m ((site side).center i)).1 ∧
      Subtype (m ((site side).center i)).1 (m ((site side).occurrence.demand.arguments i).2).1
    rw [args,center]
    exact ⟨subtype_refl _,subtype_refl _⟩
  · intro _ hit
    rcases hit with named|⟨c,contained,_⟩
    · cases side <;> cases named
    · cases side <;> cases contained
  · rw [head_schema]
    refine ⟨?_,by intro _ h; cases h⟩
    intro entry seen
    cases List.mem_singleton.mp seen
    refine ⟨⟨_,.source 1⟩,?_⟩
    intro actual observed
    cases observed
    exact valid.1.1.1.2.1 (1 : Fin 2) (.base .int) rfl
  · rw [emitted_exact]
    intro e found wrong; cases List.mem_singleton.mp found; exact False.elim (wrong rfl)
  · cases side <;> intro _ found <;> cases found
  · unfold Outputs
    rw [emitted_exact]
    intro _ found; cases List.mem_singleton.mp found
    exact sharing_scalar m valid

end Yulang.GeneralSharedNamedLeaf310
