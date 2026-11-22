import Yulang.GeneralDeclarativeEndpointDictionary336
import Yulang.GeneralDeclarativeEndpointCase336
import Yulang.GeneralDeclarativeWitnessCutRank334

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000
namespace Yulang.GeneralDeclarativeEndpointRegression336
open GeneralDeclarativeEndpointCase336
open GeneralDeclarativeWitnessCutDecl334 (arg pat root impl registry checked declared covered normal wanted)
open GeneralDeclarativeNestedExample332 (interpretation)
open GeneralDeclarationExamples (constructors)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeOrigins321 (Supported restriction from_source)
open GeneralDeclarativeEndpointInput336 (Input Inputs)
open GeneralDeclarativeEndpointProgram336 (Jobs Projection ready)
open GeneralDeclarativeEndpointBatch336 (prepare slots patch)
open GeneralDeclarativeEndpointOverlay336 (Entry ModelsWith footprintKeep receipts spans values)
open GeneralDeclarativeEndpointSelected336 (Rule Selected)
open GeneralDeclarativeEndpointDictionary336 (Evidence dictionary_sound)
open GeneralDeclarativeCurrentReceipt330 (literal)
open GeneralDeclarativeEntailment320 (appendFacts model_append)
open GeneralDeclarativeGrowth327 (Extends trans)
open GeneralDeclarativeObserverGrowth330 (preserve sources_grow)
open GeneralDeclarativeNestedBody332 (compileBody)
open GeneralDeclarativeStableAttempt329 (Elected)
open GeneralDeclarativeEndpointProbe321 (HeadMatches)
open GeneralDeclarativeInlineEndpoint331 (candidates)
open GeneralDeclarativeDemand320 (Demand Bounds)
open GeneralDeclarativeLowerKnown321 (Ready alias_refl alias_mono knows_row)
open GeneralDeclarativeGraphRows321 (observed shapeOf)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeRank321 (graph_no_cycle)
open GeneralDeclarativePriority321 (Candidates Recurs)
open GeneralDeclarativeWitnessCutRank334 (height edgeOK atomOK rowOK decreases)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeOpaqueNominal328 (point)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (Classify)
open GeneralDeclarations (Clause Declaration)

def wait (_ : Demand) (_ : Declaration) : Prop := False
abbrev shape : List (Nat × Nat) := [(7,0)]
abbrev jobs : Jobs := [(0,.field arg 7 (.variable 3) (.variable 4)),(1,.rest arg [7] endCode endCode)]
abbrev protect : List Nat := [5]
abbrev keep := footprintKeep protect jobs
abbrev named : State := prepare before keep jobs.length
abbrev uses := spans before keep jobs
abbrev sidecar : List Entry := receipts before keep jobs
def fallback (_ : Nat) : Capture := point 3
def targets (_ : Clause) (_ : Nat) : Nat := 5

theorem ready_eq : ready arg shape 1 loFields hiFields loFields hiFields endCode endCode = some jobs := rfl

theorem source : Inputs support constructors interpretation protect before root.arguments impl.head named uses sidecar :=
  .cons (used := uses) (later := []) (reads := sidecar) (history := [])
    (.record (pat := pat) (shape := shape) (tail := 1) rfl actual_read ready_eq) .nil

theorem points : uses = [(0,⟨6,7,8⟩),(1,⟨9,10,11⟩)] := rfl

abbrev output : Equation := ⟨5,.variable 7⟩
abbrev assembled := (GeneralDeclarativeStableAssemble329.merged named protect uses fallback).state
abbrev final : State := appendFacts assembled [output]

theorem build :
    compileBody registry interpretation root impl named uses protect fallback targets = some (final,[]) := rfl

theorem grown : Extends before final :=
  trans (GeneralDeclarativeEndpointBatch336.grows _ _ _) (trans (GeneralDeclarativeGrowth327.facts _ _)
    (trans ((GeneralDeclarativeStableAssemble329.assemble protect uses fallback
      (fun _ found => GeneralDeclarativeEndpointOverlay336.spans_ready found)).preserve.grows)
      (GeneralDeclarativeGrowth327.facts _ _)))

def authorized : Supported final (fun _ => False) := preserve support grown

theorem safe : ∀ k, ¬AliasCycle final (observed final) k := by
  have intervals : final.normal.intervals.all edgeOK = true := by decide +kernel
  have atoms : final.normal.ordinary.all atomOK = true := by decide +kernel
  have rows : final.equations.all rowOK = true := by decide +kernel
  have heads : final.equations.all decreases = true := by decide +kernel
  have forward {a b} (proof : GeneralDeclarativeBounds319.Bound final.normal a b) : height a ≤ height b := by
    induction proof with
    | interval seen => exact of_decide_eq_true (List.all_eq_true.mp intervals _ seen)
    | constraint seen => exact of_decide_eq_true (List.all_eq_true.mp atoms _ seen)
    | refl _ => exact Nat.le_refl _
    | trans _ _ f g => exact Nat.le_trans f g
  have level {a b} (h : GeneralDeclarativeLowerKnown321.Alias final a b) : height a = height b := by
    induction h with
    | bounds first last => exact Nat.le_antisymm (forward first) (forward last)
    | forward seen => exact of_decide_eq_true (List.all_eq_true.mp rows _ seen)
    | backward seen => exact (of_decide_eq_true (List.all_eq_true.mp rows _ seen)).symm
    | trans _ _ a b => exact a.trans b
  apply graph_no_cycle height (fun _ _ => level)
  rintro n tag child ⟨rhs,seen,code⟩ member
  have yes := List.all_eq_true.mp heads ⟨n,rhs⟩ seen
  change decreases ⟨n,rhs⟩ = true at yes
  unfold decreases at yes
  rw [code] at yes
  exact of_decide_eq_true (List.all_eq_true.mp yes child member)

theorem elected :
    Elected final registry interpretation authorized (candidates authorized registry interpretation wait) root impl := by
  have lo := (sources_grow support grown).equations low
  have hi := (sources_grow support grown).equations high
  have rb : Bounds final arg := GeneralDeclarativeGrowth327.fits grown actual_read.valid
  have rdy : Ready authorized root := by
    intro a part; cases List.mem_singleton.mp part
    exact ⟨_,knows_row lo rfl⟩
  have liveRead (mode : GeneralNominalMaterialization.Mode) :
      GeneralDeclarativeInlineTrace331.Read (restriction authorized) mode (.variable 0) wanted
        [⟨0,mode,.variable 3⟩,⟨1,mode,endCode⟩] := by
    refine .record (.name (.inline (alias_refl _) .exactEnd lo)) (raw := loFields) (keys := [7]) (selected := loFields)
      (by decide) (by decide) rfl (.cons .capture .nil) .binder .capture
  have upperRead (mode : GeneralNominalMaterialization.Mode) :
      GeneralDeclarativeInlineTrace331.Read (restriction authorized) mode (.variable 2) wanted
        [⟨0,mode,.variable 4⟩,⟨1,mode,endCode⟩] := by
    refine .record (.name (.inline (alias_refl _) .exactEnd hi)) (raw := hiFields) (keys := [7]) (selected := hiFields)
      (by decide) (by decide) rfl (.cons .capture .nil) .binder .capture
  have matched : GeneralDeclarativeInlineEndpoint331.Heads (restriction authorized) constructors interpretation root impl :=
    .cons ⟨rb,wanted,_,_,normal,liveRead .lower,upperRead .upper⟩ .nil
  have noRec : ¬Recurs final registry interpretation (candidates authorized registry interpretation wait) root := by
    rintro (⟨a,_,cy⟩|⟨_,_,_,_,_,_,_,_,_,site,_,cy⟩)
    · exact safe a.lower cy
    · exact safe site cy
  refine ⟨rdy,noRec,fun ⟨_,_,w⟩ => w,⟨⟨List.mem_cons_self,rfl⟩,.inr matched⟩,?_⟩
  intro other allowed
  cases List.mem_singleton.mp allowed.1.1
  rfl

def witness : Selected authorized sidecar registry interpretation wait root impl [] where
  slice := ⟨before,support,grown,sources_grow support grown⟩
  protect := protect
  fallback := fallback
  targets := targets
  named := named
  spans := uses
  reads := sidecar
  source := source
  ordinary := final
  compiler := build
  receipt := literal (GeneralDeclarativeClauseBatch327.reflexive _)
  readback := fun _ h => h
  chosen := elected

theorem accepted : Classify (Rule authorized sidecar registry interpretation wait) root (.selected (.node impl.id [])) :=
  ⟨.selected impl.id [],.selected (.selected witness) .nil,.selected .nil (.selected rfl)⟩

def seed : Assignment := patch before keep (values model jobs) model

theorem seed_valid : ModelsWith named sidecar seed :=
  GeneralDeclarativeEndpointOverlay336.patch_checked model model_ok
    ((GeneralDeclarativeEndpointProgram336.list_sound actual_read ready_eq).2 model model_ok) protect

theorem no_repeat : GeneralDeclarativeStableCanonical329.EqualUses seed uses := by
  intro key a b one two
  rw [points] at one two
  simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at one two
  rcases one with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;>
    rcases two with ⟨same,rfl⟩|⟨same,rfl⟩
  all_goals first | exact eqv_refl _ | contradiction

theorem populated : ∃ m, ModelsWith final sidecar m := by
  have merged := GeneralDeclarativeStableAssemble329.assemble protect uses fallback
    (fun _ found => GeneralDeclarativeEndpointOverlay336.spans_ready found)
  obtain ⟨m,valid,old⟩ := (GeneralDeclarativeStableAssemble329.witness_projection merged seed).mp
    ⟨seed_valid.1,no_repeat⟩
  have unchanged (n : Nat) (bounded : n ≤ 11) : m n = seed n := by
    apply old
    have listed : (List.range 12) ⊆
        GeneralDeclarativeFootprint321.stateNames (GeneralDeclarativeStableAssemble329.tieState named uses fallback) ++ protect := by
      intro x h
      have xlt := List.mem_range.mp h
      have options : x=0 ∨ x=1 ∨ x=2 ∨ x=3 ∨ x=4 ∨ x=5 ∨ x=6 ∨ x=7 ∨ x=8 ∨ x=9 ∨ x=10 ∨ x=11 := by omega
      rcases options with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel
    exact listed (List.mem_range.mpr (by omega))
  have both : ∀ x ∈ sidecar, GeneralDeclarativeEndpointOverlay336.Holds m x := by
    intro x used
    have previous := seed_valid.2 x used
    let fld : Entry := ⟨.field arg 7 (.variable 3) (.variable 4),⟨6,7,8⟩⟩
    let rem : Entry := ⟨.rest arg [7] endCode endCode,⟨9,10,11⟩⟩
    change x ∈ [fld,rem] at used
    rcases List.mem_cons.mp used with rfl|later
    · simpa [fld,rem,GeneralDeclarativeEndpointOverlay336.Holds,Projection.eval,
        GeneralDeclarativeEndpointRecord336.interp,GeneralNominalCenteredHeadMatExpressions.value,
        GeneralNominalCenteredHeadMatExpressions.values,GeneralDeclarativeHead320.environment,GeneralDeclarativeEndpointBatch336.atSlots,
        unchanged 1 (by decide),unchanged 3 (by decide),unchanged 4 (by decide),
        unchanged 6 (by decide),unchanged 7 (by decide),unchanged 8 (by decide)] using previous
    · have equal := List.mem_singleton.mp later
      subst x
      simpa [fld,rem,GeneralDeclarativeEndpointOverlay336.Holds,Projection.eval,
        GeneralDeclarativeEndpointRecord336.interp,GeneralNominalCenteredHeadMatExpressions.value,
        GeneralNominalCenteredHeadMatExpressions.values,GeneralDeclarativeHead320.environment,GeneralDeclarativeEndpointBatch336.atSlots,
        unchanged 1 (by decide),unchanged 9 (by decide),unchanged 10 (by decide),
        unchanged 11 (by decide)] using previous
  refine ⟨m,(model_append _).mpr ⟨valid,?_⟩,both⟩
  intro row shown
  cases List.mem_singleton.mp shown
  change CommonNominalFullCarrier.Equivalent (m 5).1 (m 7).1
  rw [unchanged 5 (by decide),unchanged 7 (by decide)]
  exact eqv_refl _

theorem accepted_model : ∃ m, ModelsWith final sidecar m ∧ Evidence registry interpretation m root (.node impl.id []) :=
  let ⟨m,fit⟩ := populated
  ⟨m,fit,dictionary_sound checked covered declared accepted m fit⟩

end Yulang.GeneralDeclarativeEndpointRegression336
