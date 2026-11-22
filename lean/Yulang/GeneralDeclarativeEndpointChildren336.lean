import Yulang.GeneralDeclarativeEndpointSupport336
import Yulang.GeneralDeclarativeEndpointDictionary336
import Yulang.GeneralDeclarativeEndpointLink336
import Yulang.GeneralDeclarativeEndpointMixedTail336
import Yulang.GeneralDeclarativeRecordReplay330
import Yulang.GeneralDeclarativeWitnessCutRank334

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 24000
set_option maxHeartbeats 16000000
namespace Yulang.GeneralDeclarativeEndpointChildren336
open GeneralDeclarativeRecordDecl326 (decl registry checked pat normalizedExpr normal)
open GeneralDeclarativeRecordReplay330 (covered)
open GeneralDeclarativeExampleSource320 (leaf int)
open GeneralDeclarativeHiddenDecl324 (catalogue interpretation)
open GeneralDeclarativeWitnessCutDecl334 (arg)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeOrigins321 (Supported restriction from_source)
open GeneralDeclarativeEndpointInput336 (Inputs)
open GeneralDeclarativeEndpointProgram336 (Jobs ready)
open GeneralDeclarativeEndpointRecord336 (Read)
open GeneralDeclarativeEndpointBatch336 (prepare)
open GeneralDeclarativeEndpointOverlay336 (Entry ModelsWith footprintKeep receipts spans)
open GeneralDeclarativeEndpointSupport336 (Certified authorize projected_row singleton_bounds rows)
open GeneralDeclarativeEndpointSelected336 (Rule Selected)
open GeneralDeclarativeEndpointDictionary336 (Evidence dictionary_sound)
open GeneralDeclarativeCurrentReceipt330 (literal)
open GeneralDeclarativeEntailment320 (appendFacts model_append)
open GeneralDeclarativeGrowth327 (Extends trans)
open GeneralDeclarativeObserverGrowth330 (preserve sources_grow)
open GeneralDeclarativeNestedBody332 (compileBody)
open GeneralDeclarativeStableAttempt329 (Elected)
open GeneralDeclarativeInlineEndpoint331 (candidates)
open GeneralDeclarativeDemand320 (Demand Bounds)
open GeneralDeclarativeLowerKnown321 (Ready Alias alias_refl alias_mono knows_row knows_alias)
open GeneralDeclarativeGraphRows321 (observed shapeOf)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeRank321 (graph_no_cycle)
open GeneralDeclarativePriority321 (Candidates Recurs)
open GeneralDeclarativeWitnessCutRank334 (height edgeOK atomOK rowOK decreases)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeOpaqueNominal328 (point)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (record exactEmpty emptyRecord mask subtype_refl)
open CommonRoleOutermostResolver (Classify)
open GeneralDeclarations (Clause Declaration)

abbrev endL : Expr := .primitive .exactEmpty []
abbrev endU : Expr := .primitive .emptyRecord []
abbrev payload : List (Nat × Expr) := [(7,.variable 3)]
abbrev lo : Equation := ⟨0,.record 7 (.variable 3) endL⟩
abbrev hi : Equation := ⟨2,.record 7 (.variable 3) endU⟩
abbrev scalar : Equation := ⟨3,.primitive (.scalar .int) []⟩
abbrev initial : State := ⟨⟨[],[(0,1),(1,2)]⟩,[lo,hi,scalar]⟩
def support : Supported initial (fun _ => False) :=
  ⟨fun e o => e ∈ initial.equations ∧ o = .source,And.left⟩
theorem initial_lo : lo ∈ (restriction support).equations := from_source _ ⟨List.mem_cons_self,rfl⟩
theorem initial_hi : hi ∈ (restriction support).equations := from_source _ ⟨List.mem_cons_of_mem _ List.mem_cons_self,rfl⟩
theorem initial_scalar : scalar ∈ (restriction support).equations := from_source _
  ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),rfl⟩

theorem read : Read support arg [7] payload payload payload payload endL endU :=
  ⟨⟨.interval List.mem_cons_self,.interval (List.mem_cons_of_mem _ List.mem_cons_self)⟩,
    by decide,.inline (alias_refl _) .exactEnd initial_lo,.inline (alias_refl _) .width initial_hi,rfl,rfl⟩

def wait (_ : Demand) (_ : Declaration) : Prop := False
abbrev root : Demand := ⟨1,[arg],[⟨0,6⟩]⟩
abbrev jobs : Jobs := [(0,.field arg 7 (.variable 3) (.variable 3)),(1,.rest arg [7] endL endU)]
abbrev protect : List Nat := [5,6]
abbrev keep := footprintKeep protect jobs
abbrev named := prepare initial keep jobs.length
abbrev uses := spans initial keep jobs
abbrev sidecar : List Entry := receipts initial keep jobs
def fallback (_ : Nat) : Capture := point 3
def targets (_ : Clause) (_ : Nat) := 5
abbrev rootBuilt := (GeneralDeclarativeStableAssemble329.merged named protect uses fallback).state
abbrev rootWrite : Equation := ⟨6,.variable 11⟩
abbrev rootFinal := appendFacts rootBuilt [rootWrite]
abbrev childArg : Capture := ⟨13,8,14⟩
abbrev child : Demand := ⟨2,[childArg],[⟨1,5⟩]⟩
abbrev childUses : List (Nat × Capture) := [(0,childArg)]
abbrev childBuilt := (GeneralDeclarativeStableAssemble329.merged rootFinal protect childUses fallback).state
abbrev childWrite : Equation := ⟨5,.variable 8⟩
abbrev childFinal := appendFacts childBuilt [childWrite]
abbrev final := appendFacts childFinal (rows sidecar)

theorem program : ready arg [(7,0)] 1 payload payload payload payload endL endU = some jobs := rfl
theorem root_compiles : compileBody registry interpretation root decl named uses protect fallback targets =
    some (rootFinal,[child]) := rfl
theorem child_compiles : compileBody registry interpretation child leaf rootFinal childUses protect fallback targets =
    some (childFinal,[]) := rfl
theorem uses_eq : uses = [(0,⟨7,8,9⟩),(1,⟨10,11,12⟩)] := rfl

theorem root_source : Inputs support catalogue interpretation protect initial root.arguments decl.head named uses sidecar :=
  .cons (used := uses) (later := []) (reads := sidecar) (history := [])
    (.record (pat := pat) (shape := [(7,0)]) (tail := 1) rfl read program) .nil

open GeneralDeclarativeStableAssemble329 (assemble)

theorem root_grows : Extends named rootFinal :=
  trans (GeneralDeclarativeGrowth327.facts _ _) (trans
    (assemble protect uses fallback (fun _ found => GeneralDeclarativeEndpointOverlay336.spans_ready found)).preserve.grows
    (GeneralDeclarativeGrowth327.facts _ _))

theorem child_bounds : Bounds rootFinal childArg := by
  refine ⟨.constraint ?_,.constraint ?_⟩
  all_goals decide +kernel

theorem child_grows : Extends rootFinal childFinal :=
  trans (GeneralDeclarativeGrowth327.facts _ _) (trans
    (assemble protect childUses fallback (fun a found => by cases List.mem_singleton.mp found; exact child_bounds)).preserve.grows
    (GeneralDeclarativeGrowth327.facts _ _))

theorem early : Extends initial childFinal :=
  trans (GeneralDeclarativeEndpointBatch336.grows _ _ _) (trans root_grows child_grows)

def beforeAuth : Supported childFinal (fun _ => False) := preserve support early

theorem legit : ∀ e ∈ sidecar, Certified beforeAuth e := by
  intro e present
  have record : Read beforeAuth arg [7] payload payload payload payload endL endU :=
    ⟨GeneralDeclarativeGrowth327.fits early read.valid,by decide,
      .inline (alias_refl _) .exactEnd ((sources_grow support early).equations initial_lo),
      .inline (alias_refl _) .width ((sources_grow support early).equations initial_hi),rfl,rfl⟩
  exact ⟨arg,[(7,0)],1,payload,payload,payload,payload,endL,endU,jobs,initial,protect,record,program,present⟩

def authorized : Supported final (fun _ => False) := authorize beforeAuth sidecar legit

theorem root_final : Extends rootFinal final := trans child_grows (GeneralDeclarativeGrowth327.facts _ _)
theorem initial_final : Extends initial final := trans early (GeneralDeclarativeGrowth327.facts _ _)

theorem supported {row} (old : row ∈ (restriction support).equations) :
    row ∈ (restriction authorized).equations :=
  GeneralDeclarativeEndpointSupport336.old_kept ((sources_grow support early).equations old)

theorem child_lower : GeneralDeclarativeLowerKnown321.Knows (restriction authorized) childArg.lower (.primitive (.scalar .int) 0) := by
  have name7 : GeneralDeclarativeLowerKnown321.Knows (restriction authorized) 7 (.primitive (.scalar .int) 0) := by
    have stored : (⟨7,.variable 3⟩ : Equation) ∈ (restriction authorized).equations := by
      apply projected_row (e := (GeneralDeclarativeEndpointProgram336.Projection.field arg 7 (.variable 3) (.variable 3),
        (⟨7,8,9⟩ : Capture))) (legit := legit)
      · exact List.mem_cons_self
      · exact List.mem_cons_self
    exact knows_alias (.forward stored) (knows_row (supported initial_scalar) rfl)
  have bridge : Alias (restriction authorized) 13 7 := by
    refine .bounds (.constraint ?_) (.constraint ?_)
    all_goals decide +kernel
  exact knows_alias bridge name7

theorem safe : ∀ k, ¬AliasCycle final (observed final) k := by
  have intervals : final.normal.intervals.all edgeOK = true := by decide +kernel
  have atoms : final.normal.ordinary.all atomOK = true := by decide +kernel
  have saved : final.equations.all rowOK = true := by decide +kernel
  have heads : final.equations.all decreases = true := by decide +kernel
  have forward {a b} (proof : GeneralDeclarativeBounds319.Bound final.normal a b) : height a ≤ height b := by
    induction proof with
    | interval seen => exact of_decide_eq_true (List.all_eq_true.mp intervals _ seen)
    | constraint seen => exact of_decide_eq_true (List.all_eq_true.mp atoms _ seen)
    | refl _ => exact Nat.le_refl _
    | trans _ _ f g => exact Nat.le_trans f g
  have level {a b} (h : Alias final a b) : height a = height b := by
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

theorem no_cycle (d : Demand) : ¬Recurs final registry interpretation (candidates authorized registry interpretation wait) d := by
  rintro (⟨a,_,cy⟩|⟨_,_,_,_,_,_,_,_,_,site,_,cy⟩)
  · exact safe a.lower cy
  · exact safe site cy

theorem root_picks : Elected final registry interpretation authorized (candidates authorized registry interpretation wait)
    root decl := by
  have rdy : Ready authorized root := by
    intro a h; cases List.mem_singleton.mp h
    exact ⟨_,knows_row (supported initial_lo) rfl⟩
  have range := GeneralDeclarativeGrowth327.fits initial_final read.valid
  have lowerRead (mode : GeneralNominalMaterialization.Mode) :
      GeneralDeclarativeInlineTrace331.Read (restriction authorized) mode (.variable 0) normalizedExpr
        [⟨0,mode,.variable 3⟩,⟨1,mode,endL⟩] := by
    exact .record (.name (.inline (alias_refl _) .exactEnd (supported initial_lo)))
      (raw := payload) (keys := [7]) (selected := payload) (by decide) (by decide) rfl
      (.cons .capture .nil) .binder .capture
  have upperRead (mode : GeneralNominalMaterialization.Mode) :
      GeneralDeclarativeInlineTrace331.Read (restriction authorized) mode (.variable 2) normalizedExpr
        [⟨0,mode,.variable 3⟩,⟨1,mode,endU⟩] := by
    exact .record (.name (.inline (alias_refl _) .width (supported initial_hi)))
      (raw := payload) (keys := [7]) (selected := payload) (by decide) (by decide) rfl
      (.cons .capture .nil) .binder .capture
  have recorded : GeneralDeclarativeInlineEndpoint331.Heads (restriction authorized) catalogue interpretation root decl :=
    .cons ⟨range,normalizedExpr,_,_,normal,lowerRead .lower,upperRead .upper⟩ .nil
  refine ⟨rdy,no_cycle root,fun ⟨_,_,bad⟩ => bad,⟨⟨List.mem_cons_self,rfl⟩,.inr recorded⟩,?_⟩
  intro other allowed
  rcases List.mem_cons.mp allowed.1.1 with rfl|second
  · rfl
  · have equal := List.mem_singleton.mp second
    subst other
    cases allowed.1.2

theorem child_picks : Elected final registry interpretation authorized (candidates authorized registry interpretation wait)
    child leaf := by
  have rdy : Ready authorized child := by
    intro a h; cases List.mem_singleton.mp h
    exact ⟨_,child_lower⟩
  have range := GeneralDeclarativeGrowth327.fits root_final child_bounds
  have selected : GeneralDeclarativeEndpointProbe321.HeadMatches (restriction authorized) catalogue interpretation child leaf :=
    .cons ⟨range,.variable 0,[⟨0,.lower,13⟩],[⟨0,.upper,14⟩],rfl,.capture,.capture⟩ .nil
  refine ⟨rdy,no_cycle child,fun ⟨_,_,bad⟩ => bad,
    ⟨⟨List.mem_cons_of_mem _ List.mem_cons_self,rfl⟩,.inl selected⟩,?_⟩
  intro other allowed
  rcases List.mem_cons.mp allowed.1.1 with rfl|second
  · cases allowed.1.2
  · cases List.mem_singleton.mp second
    rfl

def choiceRoot : Selected authorized sidecar registry interpretation wait root decl [child] where
  slice := ⟨initial,support,initial_final,⟨initial_final.constraints,initial_final.intervals,fun _ h => supported h⟩⟩
  protect := protect
  fallback := fallback
  targets := targets
  named := named
  spans := uses
  source := root_source
  reads := sidecar
  ordinary := rootFinal
  compiler := root_compiles
  receipt := literal root_final
  readback := fun _ h => h
  chosen := root_picks

def rootOnly : Supported rootFinal (fun _ => False) :=
  preserve support (trans (GeneralDeclarativeEndpointBatch336.grows _ _ _) root_grows)

def choiceChild : Selected authorized sidecar registry interpretation wait child leaf [] where
  slice := ⟨rootFinal,rootOnly,root_final,⟨root_final.constraints,root_final.intervals,by
    intro row h
    apply supported
    obtain ⟨origin,reason,ready⟩ := (GeneralDeclarativeOrigins321.backed_iff _ _).mp h
    exact (GeneralDeclarativeOrigins321.backed_iff _ _).mpr ⟨origin,reason,ready⟩⟩⟩
  protect := protect
  fallback := fallback
  targets := targets
  named := rootFinal
  spans := childUses
  source := .cons (used := childUses) (later := []) (reads := []) (history := [])
    (.old (.named ⟨child_bounds,.variable 0,[⟨0,.actual,8⟩],rfl,.capture,
      .cons ⟨rfl,rfl,child_bounds⟩ .nil⟩)) .nil
  reads := []
  ordinary := childFinal
  compiler := child_compiles
  receipt := literal (GeneralDeclarativeGrowth327.facts _ _)
  readback := fun _ h => False.elim (List.not_mem_nil h)
  chosen := child_picks

abbrev dictionary : CommonRoleOutermostResolver.Dictionary := .node decl.id [.node leaf.id []]

theorem selected : Classify (Rule authorized sidecar registry interpretation wait) root (.selected dictionary) :=
  ⟨.selected decl.id [.selected leaf.id []],
    .selected (.selected choiceRoot) (.cons (.selected (.selected choiceChild) .nil) .nil),
    .selected (.cons (.selected .nil (.selected rfl)) .nil) (.selected rfl)⟩

theorem declared : GeneralDeclarativeOutputSource323.Declared registry root := by
  intro output h
  cases List.mem_singleton.mp h
  exact ⟨none,rfl⟩

theorem every_model (m) (fit : ModelsWith final sidecar m) :
    Evidence registry interpretation m root dictionary :=
  dictionary_sound checked covered declared selected m fit

end Yulang.GeneralDeclarativeEndpointChildren336
