import Yulang.GeneralDeclarativeEndpointOverlay336
import Yulang.GeneralDeclarativeWitnessHead334

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeEndpointInput336
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeDemand320 (Bounds bounds_sound)
open GeneralDeclarativeWhere319 (Capture InInterval)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativeEndpointRecord336 (Read)
open GeneralDeclarativeEndpointProgram336 (Jobs Projection ready template list_sound)
open GeneralDeclarativeEndpointOverlay336 (Entry footprintKeep receipts spans spans_ready span_order)
open GeneralDeclarativeEndpointBatch336 (prepare grows)
open GeneralDeclarativeWitnessHead334 (Argument argument_sound)
open GeneralDeclarativeOpaqueConserve328 (Retains)
open GeneralDeclarativeGrowth327 (Extends trans fits derives)
open GeneralDeclarativeStableReads329 (One names_one)
open GeneralDeclarativeEqualities322 (Derives semantic)
open GeneralDeclarativeOpaqueNested328 (occurrences)
open GeneralDeclarativeTermWalk322 (Walk)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalInspection (Interpretation)
open GeneralDeclarationPatterns (Constructors Pattern normalize variablesArgs normalizeArgs)
open CommonNominalFullCarrier (Equivalent)
open CommonRoleOutermostResolver (All₂)

/-- Newly approved I-61 route is independent of the older actual
center RHS routes. The candidate's normalized syntax determines
whether this direct binder record procedure is applicable. The record
read is the genuine endpoint source certificate, not model existence. -/
inductive Input {s : State} (p : Supported s done) (c : Constructors) (i : Interpretation)
    (keep : List Nat) : State → Capture → Pattern → State → List (Nat × Capture) → List Entry → Prop where
  | old : Argument p c i keep before a pat after used →
    Input p c i keep before a pat after used []
  | record : normalize pat = template shape tail →
    Read p a (shape.map Prod.fst) ls us first last le ue →
    ready a shape tail ls us first last le ue = some jobs →
    Input p c i keep before a pat (prepare before (footprintKeep keep jobs) jobs.length)
      (spans before (footprintKeep keep jobs) jobs) (receipts before (footprintKeep keep jobs) jobs)

inductive Inputs {s : State} (p : Supported s done) (c : Constructors) (i : Interpretation)
    (keep : List Nat) : State → List Capture → List Pattern → State → List (Nat × Capture) → List Entry → Prop where
  | nil : Inputs p c i keep before [] [] before [] []
  | cons : Input p c i keep before a pat mid used reads →
    Inputs p c i keep mid as ps after later history →
    Inputs p c i keep before (a::as) (pat::ps) after (used++later) (reads++history)

def RecordRecipe (a : Capture) (pat : Pattern) (used : List (Nat × Capture)) (reads : List Entry) : Prop :=
  ∃ (source : State) (done : Nat → Prop) (p : Supported source done)
    (shape : List (Nat × Nat)) (tail : Nat) (ls us first last : CommonRoleCanonicalRows.Row Expr)
    (le ue : Expr) (jobs : Jobs) (before : State) (keep : List Nat),
    normalize pat = template shape tail ∧
    Read p a (shape.map Prod.fst) ls us first last le ue ∧
    ready a shape tail ls us first last le ue = some jobs ∧
    used = spans before (footprintKeep keep jobs) jobs ∧
    reads = receipts before (footprintKeep keep jobs) jobs

structure LocalShape {s : State} (c : Constructors) (i : Interpretation)
    (a : Capture) (pat : Pattern) (used : List (Nat × Capture)) (reads : List Entry) : Prop where
  range : Bounds s a
  form : (∃ target code, translate c i (normalize pat) = some code ∧ Derives s (.variable a.center) target ∧
      Walk .actual target code (occurrences used) ∧ reads = []) ∨ RecordRecipe a pat used reads

theorem shape_grows {s t : State} (step : Extends s t) (before : LocalShape (s := s) c i a pat us rs) :
    LocalShape (s := t) c i a pat us rs := by
  refine ⟨fits step before.range,?_⟩
  rcases before.form with ⟨target,code,found,h,walk,none⟩|right
  · exact .inl ⟨target,code,found,derives step h,walk,none⟩
  · exact .inr right

theorem input {s before : State} {p : Supported s done}
    (seen : Input p c i keep before a pat after used reads) (old : Extends s before) :
    Extends before after ∧ LocalShape (s := after) c i a pat used reads ∧
      (∀ slot ∈ used, Bounds after slot.2) ∧ used.map Prod.fst = (normalize pat).variables := by
  cases seen with
  | old former =>
    obtain ⟨retains,head,bounded⟩ := argument_sound former old
    obtain ⟨code,form,printed,actual,walk⟩ := head.actual
    exact ⟨retains.grows,⟨head.fits,.inl ⟨form,code,printed,actual,walk,rfl⟩⟩,bounded,names_one head⟩
  | @record pat shape tail a ls us first last le ue jobs before exactPat read calculated =>
    let update := grows before (footprintKeep keep jobs) jobs.length
    have names := (list_sound read calculated).1
    refine ⟨update,⟨fits (trans old update) read.valid,.inr ?_⟩,fun _ known => spans_ready known,?_⟩
    · exact ⟨s,done,p,shape,tail,ls,us,first,last,le,ue,jobs,before,keep,exactPat,read,calculated,rfl,rfl⟩
    · rw [span_order,exactPat]; exact names

theorem sources {s before : State} {p : Supported s done}
    (seen : Inputs p c i keep before args pats after used reads) (old : Extends s before) :
    Extends before after ∧ (∀ slot ∈ used, Bounds after slot.2) ∧
      used.map Prod.fst = variablesArgs (normalizeArgs pats) := by
  induction seen with
  | nil => exact ⟨GeneralDeclarativeClauseBatch327.reflexive _,fun _ h => False.elim (List.not_mem_nil h),rfl⟩
  | cons one more ih =>
    obtain ⟨step,shape,here,first⟩ := input one old
    obtain ⟨next,later,last⟩ := ih (trans old step)
    exact ⟨trans step next,fun _ h => (List.mem_append.mp h).elim (fun u => fits next (here _ u)) (later _),
      by simp only [List.map_append,first,last,GeneralDeclarationPatterns.normalizeArgs,variablesArgs]⟩

open GeneralDeclarativeEndpointOverlay336 (Holds Agreement)
open GeneralDeclarativeEndpointBatch336 (atSlots)

inductive Observed (c : Constructors) (i : Interpretation) (m : Assignment) : Capture → Pattern → Prop where
  | literal : InInterval (m a.lower).1 (m a.upper).1 (m a.center).1 →
    translate c i (normalize pat) = some code →
    Equivalent (m a.center).1 (GeneralDeclarativeEndpointRecord336.interp m target) →
    Walk .actual target code (occurrences used) →
    Observed c i m a pat
  | record : InInterval (m a.lower).1 (m a.upper).1 (m a.center).1 →
    RecordRecipe a pat used exactReads →
    (∀ e ∈ exactReads, Holds m e) →
    Observed c i m a pat

theorem observed {s before : State} {p : Supported s done}
    (seen : Inputs p c i keep before args pats after used reads)
    (old : Extends s before) (current : Extends after t) (m) (fit : Models t m)
    (projections : ∀ e ∈ reads, Holds m e) :
    All₂ (Observed c i m) args pats := by
  induction seen with
  | nil => exact .nil
  | cons one more ih =>
    obtain ⟨step,shape,_,_⟩ := input one old
    have remain := (sources more (trans old step)).1
    have upto := trans remain current
    have currentShape := shape_grows upto shape
    refine .cons ?_ (ih (trans old step) current (fun e had => projections e (List.mem_append_right _ had)))
    rcases currentShape.form with ⟨target,code,someCode,actual,walk,none⟩|recipe
    · exact .literal (bounds_sound currentShape.range m fit) someCode (semantic actual m fit) walk
    · exact .record (bounds_sound currentShape.range m fit) recipe
        (fun e had => projections e (List.mem_append_left _ had))

end Yulang.GeneralDeclarativeEndpointInput336
