import Yulang.GeneralDeclarativeEndpointChildren336
import Yulang.GeneralDeclarativeEndpointChildModels336

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 22000
set_option maxHeartbeats 14000000
namespace Yulang.GeneralDeclarativeEndpointClash336
open GeneralDeclarativeEndpointChildren336 (initial support payload lo hi scalar initial_lo initial_hi)
open GeneralDeclarativeEndpointChildModels336 (sourceModel source_valid)
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeWitnessCutDecl334 (arg body)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeEndpointProgram336 (Projection Jobs ready template)
open GeneralDeclarativeEndpointOverlay336 (Entry ModelsWith footprintKeep spans receipts)
open GeneralDeclarativeEndpointBatch336 (prepare)
open GeneralDeclarativeEndpointSelected336 (Rule Clash clash_exact)
open GeneralDeclarativeEndpointInput336 (Inputs)
open GeneralDeclarativeEndpointRecord336 (interp field_interval)
open GeneralDeclarativeEndpointResidual336 (exact_residuals)
open GeneralDeclarativeGrowth327 (Extends)
open GeneralDeclarativeStableAttempt329 (Elected)
open GeneralDeclarativeInlineEndpoint331 (candidates)
open GeneralDeclarativeLowerKnown321 (Ready knows_row alias_refl Alias)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeRank321 (graph_no_cycle)
open GeneralDeclarativeGraphRows321 (observed shapeOf)
open GeneralDeclarativeWitnessCutRank334 (height edgeOK atomOK rowOK decreases)
open GeneralDeclarativeObserverGrowth330 (preserve sources_grow)
open GeneralDeclarativeOpaqueNominal328 (point)
open GeneralDeclarativeExampleSource320 (int)
open GeneralDeclarationExamples (constructors roles)
open GeneralDeclarativeNestedExample332 (interpretation)
open GeneralDeclarations (Declaration Registry)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans eqv_symm)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Equivalent Subtype mask exactEmpty emptyRecord subtype_trans observeTy)
open CommonNominalFullDemand (ProbeAt ProbeStep MaskedProbeStep)
open CommonNominalSyntax (Layer)

abbrev endL := GeneralDeclarativeEndpointChildren336.endL
abbrev endU := GeneralDeclarativeEndpointChildren336.endU

abbrev approved := GeneralDeclarativeEndpointChildren336.read
abbrev code : Expr := .record 7 (.variable 0) (.variable 0)
abbrev pat := template [(7,0)] 0
abbrev impl : Declaration := ⟨92,1,[pat],[],[body],[]⟩
abbrev registry : Registry := ⟨constructors,roles,[impl]⟩
abbrev root : Demand := ⟨1,[arg],[⟨0,5⟩]⟩
abbrev jobs : Jobs := [(0,.field arg 7 (.variable 3) (.variable 3)),(0,.rest arg [7] endL endU)]
abbrev protect : List Nat := [5]
abbrev keep := footprintKeep protect jobs
abbrev named := prepare initial keep jobs.length
abbrev used := spans initial keep jobs
abbrev sidecar : List Entry := receipts initial keep jobs
def fallback (_ : Nat) : Capture := point 3
def wait (_ : Demand) (_ : Declaration) : Prop := False

theorem program : ready arg [(7,0)] 0 payload payload payload payload endL endU = some jobs := rfl

theorem input : Inputs support constructors interpretation protect initial root.arguments impl.head named used sidecar :=
  .cons (used := used) (later := []) (reads := sidecar) (history := [])
    (.record (pat := pat) (shape := [(7,0)]) (tail := 0) rfl approved program) .nil

theorem before_model : ∃ m, ModelsWith named sidecar m := by
  obtain ⟨m,fit,_⟩ := GeneralDeclarativeEndpointOverlay336.approved approved program sourceModel source_valid protect
  exact ⟨m,fit⟩

theorem used_exact : used = [(0,⟨6,7,8⟩),(0,⟨9,10,11⟩)] := rfl

theorem field_agrees (m : Assignment) (fit : ModelsWith named sidecar m) :
    Equivalent (m 7).1 int := by
  have initialFit := GeneralDeclarativeGrowth327.restrict (GeneralDeclarativeEndpointBatch336.grows _ _ _) m fit.1
  have actualField := initialFit.2 scalar (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  obtain ⟨mid,project,ranges⟩ := field_interval approved List.mem_cons_self List.mem_cons_self m initialFit
  let e : Entry := ⟨.field arg 7 (.variable 3) (.variable 3),⟨6,7,8⟩⟩
  obtain ⟨ideal,wrote,agrees⟩ := fit.2 e List.mem_cons_self
  change (GeneralDeclarativeRecordChannel330.project 7 false [] (m 1).1).map
      (fun x => ((m 3).1,x,(m 3).1)) = some ideal at wrote
  have h : ((m 3).1,mid,(m 3).1) = ideal := Option.some.inj (by
    rw [project] at wrote; exact wrote)
  rw [← h] at agrees
  exact eqv_trans agrees.2.1 (eqv_trans ⟨ranges.2,ranges.1⟩ actualField)

theorem rest_above (m : Assignment) (fit : ModelsWith named sidecar m) :
    Subtype (mask [7] exactEmpty) (m 10).1 := by
  have initialFit := GeneralDeclarativeGrowth327.restrict (GeneralDeclarativeEndpointBatch336.grows _ _ _) m fit.1
  have residual := exact_residuals approved m initialFit
  let e : Entry := ⟨.rest arg [7] endL endU,⟨9,10,11⟩⟩
  obtain ⟨ideal,wrote,agrees⟩ := fit.2 e (List.mem_cons_of_mem _ List.mem_cons_self)
  have h : (mask [7] exactEmpty,mask [7] (m 1).1,mask [7] emptyRecord) = ideal := Option.some.inj wrote
  rw [← h] at agrees
  exact subtype_trans residual.1 agrees.2.1.2

theorem disjoint : ¬ Subtype (mask [7] exactEmpty) int := by
  intro below
  let env : CommonNominalFullDemand.Environment CommonNominalFullCarrier.Row :=
    ⟨fun _ => .bottom,fun _ => []⟩
  have yes : ProbeAt Common.rowLe 0 env (observeTy 0 int) (.base .int) := rfl
  have no := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (below 0) 0 env _ yes
  change ProbeAt Common.rowLe 0 env (.mask [7] .exactEmpty) (.base .int) at no
  simp [ProbeAt,ProbeStep,MaskedProbeStep] at no

theorem clash : Clash named sidecar used fallback := by
  apply (clash_exact _ _ _ _).mpr
  refine ⟨before_model,?_⟩
  intro m fits tied
  have eq := tied 0 ⟨6,7,8⟩ ⟨9,10,11⟩ (by rw [used_exact]; exact List.mem_cons_self)
    (by rw [used_exact]; exact List.mem_cons_of_mem _ List.mem_cons_self)
  exact disjoint (subtype_trans (rest_above m fits) (subtype_trans eq.2 (field_agrees m fits).1))

theorem grown : Extends initial named := GeneralDeclarativeEndpointBatch336.grows _ _ _
def current : Supported named (fun _ => False) := preserve support grown

theorem safe : ∀ k, ¬AliasCycle named (observed named) k := by
  have intervals : named.normal.intervals.all edgeOK = true := by decide +kernel
  have atoms : named.normal.ordinary.all atomOK = true := by decide +kernel
  have saved : named.equations.all rowOK = true := by decide +kernel
  have heads : named.equations.all decreases = true := by decide +kernel
  have forward {a b} (proof : GeneralDeclarativeBounds319.Bound named.normal a b) : height a ≤ height b := by
    induction proof with
    | interval seen => exact of_decide_eq_true (List.all_eq_true.mp intervals _ seen)
    | constraint seen => exact of_decide_eq_true (List.all_eq_true.mp atoms _ seen)
    | refl _ => exact Nat.le_refl _
    | trans _ _ f g => exact Nat.le_trans f g
  have level {a b} (h : Alias named a b) : height a = height b := by
    induction h with
    | bounds first last => exact Nat.le_antisymm (forward first) (forward last)
    | forward seen => exact of_decide_eq_true (List.all_eq_true.mp saved _ seen)
    | backward seen => exact (of_decide_eq_true (List.all_eq_true.mp saved _ seen)).symm
    | trans _ _ a b => exact a.trans b
  apply graph_no_cycle height (fun _ _ => level)
  rintro n tag child ⟨rhs,seen,code⟩ present
  have yes := List.all_eq_true.mp heads ⟨n,rhs⟩ seen
  change decreases ⟨n,rhs⟩ = true at yes
  unfold decreases at yes
  rw [code] at yes
  exact of_decide_eq_true (List.all_eq_true.mp yes child present)


theorem elected : Elected named registry interpretation current
    (candidates current registry interpretation wait) root impl := by
  have supportedLo := (sources_grow support grown).equations initial_lo
  have supportedHi := (sources_grow support grown).equations initial_hi
  have rdy : Ready current root := by
    intro a h; cases List.mem_singleton.mp h
    exact ⟨_,knows_row supportedLo rfl⟩
  have lowerRead (mode : GeneralNominalMaterialization.Mode) :
      GeneralDeclarativeInlineTrace331.Read (restriction current) mode (.variable 0) code
        [⟨0,mode,.variable 3⟩,⟨0,mode,endL⟩] := by
    exact .record (.name (.inline (alias_refl _) .exactEnd supportedLo))
      (raw := payload) (keys := [7]) (selected := payload) (by decide) (by decide) rfl
      (.cons .capture .nil) .binder .capture
  have upperRead (mode : GeneralNominalMaterialization.Mode) :
      GeneralDeclarativeInlineTrace331.Read (restriction current) mode (.variable 2) code
        [⟨0,mode,.variable 3⟩,⟨0,mode,endU⟩] := by
    exact .record (.name (.inline (alias_refl _) .width supportedHi))
      (raw := payload) (keys := [7]) (selected := payload) (by decide) (by decide) rfl
      (.cons .capture .nil) .binder .capture
  have bounded : GeneralDeclarativeDemand320.Bounds named arg :=
    GeneralDeclarativeGrowth327.fits grown approved.valid
  have seen : GeneralDeclarativeInlineEndpoint331.Heads (restriction current) constructors interpretation root impl :=
    .cons ⟨bounded,code,_,_,rfl,lowerRead .lower,upperRead .upper⟩ .nil
  have noCycle : ¬GeneralDeclarativePriority321.Recurs named registry interpretation
      (candidates current registry interpretation wait) root := by
    rintro (⟨a,_,cy⟩|⟨_,_,_,_,_,_,_,_,_,site,_,cy⟩)
    · exact safe a.lower cy
    · exact safe site cy
  refine ⟨rdy,noCycle,fun ⟨_,_,bad⟩ => bad,⟨⟨List.mem_cons_self,rfl⟩,.inr seen⟩,?_⟩
  intro other found
  cases List.mem_singleton.mp found.1.1
  rfl

theorem rejected : Rule current sidecar registry interpretation wait root .rejected :=
  .tieClash (slice := ⟨initial,support,grown,sources_grow support grown⟩) elected input clash

end Yulang.GeneralDeclarativeEndpointClash336
