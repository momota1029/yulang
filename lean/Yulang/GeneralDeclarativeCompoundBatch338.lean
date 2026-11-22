import Yulang.GeneralDeclarativeCompoundPattern338
import Yulang.GeneralDeclarativeExactNested337

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeCompoundBatch338
open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeEntailment320 (appendFacts model_append)
open GeneralDeclarativeFootprint321 (stateNames)
open GeneralDeclarativeGrowth327 (Extends fits trans facts)
open GeneralDeclarativeObserverGrowth330 (preserve sources_grow)
open GeneralDeclarativeRecordSpine330 (Spine)
open GeneralDeclarativeEndpointRecord336 (Read)
open GeneralDeclarativeEndpointProgram336 (Jobs ready from_supported list_sound)
open GeneralDeclarativeEndpointBatch336 (prepare grows bound)
open GeneralDeclarativeEndpointOverlay336 (Entry footprintKeep receipts)
open GeneralDeclarativeEndpointSupport336 (Certified)
open GeneralDeclarativeEndpointConserve336 (names)
open GeneralDeclarativeExactOverlay337 (ModelsExact approved)
open GeneralDeclarativeExactSupport337 (rows endpointRows endpoints_sound authorize receipts_same)
open GeneralDeclarativeCompoundPattern338 (layout layout_labels)
open GeneralDeclarativeCompoundEndpoints338 (from_visible)
open CommonRoleCanonicalRows (Row normalize)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalCommonBridge (Assignment)

def Visible (p : Supported s done) (arg : Capture) (keys : List Nat) : Prop :=
  ∃ lower upper loEnd hiEnd,
    Spine (restriction p) arg.lower lower loEnd ∧ Spine (restriction p) arg.upper upper hiEnd ∧
    (∀ k ∈ keys, ∃ term, (k,term) ∈ normalize lower) ∧
    (∀ k ∈ keys, ∃ term, (k,term) ∈ normalize upper)

/-- The computed pipeline for one structural node. The layout
numbers are only routing indices; no occurrence is tied here. -/
structure Ticket {s : State} (p : Supported s done) (arg : Capture) (fields : Row Pattern) where
  lower : Row Expr
  upper : Row Expr
  first : Row Expr
  last : Row Expr
  loEnd : Expr
  hiEnd : Expr
  jobs : Jobs
  read : Read p arg ((layout fields).map Prod.fst) lower upper first last loEnd hiEnd
  calculated : ready arg (layout fields) fields.length lower upper first last loEnd hiEnd = some jobs

theorem produce {s : State} {p : Supported s done} {fields : Row Pattern}
    (valid : Bounds s arg) (distinct : (fields.map Prod.fst).Nodup)
    (seen : Visible p arg (fields.map Prod.fst)) : Nonempty (Ticket p arg fields) := by
  obtain ⟨lo,hi,le,ue,spLo,spHi,hasLo,hasHi⟩ := seen
  rw [← layout_labels fields] at distinct hasLo hasHi
  obtain ⟨fr,to,read⟩ := from_visible valid distinct spLo spHi hasLo hasHi
  obtain ⟨jobs,made⟩ := from_supported read fields.length
  exact ⟨⟨lo,hi,fr,to,le,ue,jobs,read,made⟩⟩

open GeneralDeclarativeEndpointBatch336 (slots)

def protectedNames (old : List Entry) (keep : List Nat) (jobs : Jobs) : List Nat :=
  footprintKeep (names old ++ keep) jobs

def intermediate (s : State) (old : List Entry) (keep : List Nat) (jobs : Jobs) : State :=
  prepare s (protectedNames old keep jobs) jobs.length

def minted (s : State) (old : List Entry) (keep : List Nat) (jobs : Jobs) : List Entry :=
  receipts s (protectedNames old keep jobs) jobs

def after (s : State) (old : List Entry) (keep : List Nat) (jobs : Jobs) : State :=
  appendFacts (intermediate s old keep jobs) (rows (minted s old keep jobs))

def middleSupport {s : State} (p : Supported s done) (old : List Entry) (keep : List Nat)
    (jobs : Jobs) : Supported (intermediate s old keep jobs) done :=
  preserve p (grows s (protectedNames old keep jobs) jobs.length)

def afterSupport {s : State} (p : Supported s done) (old : List Entry) (keep : List Nat)
    (jobs : Jobs) : Supported (after s old keep jobs) done :=
  authorize (middleSupport p old keep jobs) (minted s old keep jobs)

theorem grows_after (s : State) (old : List Entry) (keep : List Nat) (jobs : Jobs) :
    Extends s (after s old keep jobs) :=
  trans (grows _ _ _) (facts _ _)

theorem read_grows {s t : State} {p : Supported s done}
    (grown : Extends s t) (r : Read p arg keys ls us first last le ue) :
    Read (preserve p grown) arg keys ls us first last le ue :=
  ⟨fits grown r.valid,r.distinct,
    GeneralDeclarativeObserverGrowth330.spine (sources_grow p grown) r.lo,
    GeneralDeclarativeObserverGrowth330.spine (sources_grow p grown) r.hi,
    r.displayedLow,r.displayedHigh⟩

theorem minted_certified {s : State} {p : Supported s done} (t : Ticket p arg fields)
    (listed : e ∈ minted s old keep t.jobs) :
    Certified (middleSupport p old keep t.jobs) e := by
  exact ⟨arg,layout fields,fields.length,t.lower,t.upper,t.first,t.last,t.loEnd,t.hiEnd,
    t.jobs,s,names old ++ keep,read_grows (grows _ _ _) t.read,t.calculated,listed⟩

theorem minted_bounds {s : State} {old keep jobs} (listed : e ∈ minted s old keep jobs) :
    Bounds (intermediate s old keep jobs) e.2 := by
  obtain ⟨⟨job,i⟩,used,rfl⟩ := List.mem_map.mp listed
  exact bound (by simpa using List.snd_lt_of_mem_zipIdx used)

theorem authored_row {s : State} {p : Supported s done} (t : Ticket p arg fields)
    (listed : e ∈ minted s old keep t.jobs) (wrote : row ∈ endpointRows e) :
    row ∈ (restriction (afterSupport p old keep t.jobs)).equations :=
  GeneralDeclarativeExactSupport337.from_projection listed (minted_certified t listed) wrote

/-- Preserve the old capture footprint with its *actual assignments*.
Appending authored lower/upper rows is conservative because exact
receipts prove those same rows in the patched model. -/
theorem conserves {s : State} {p : Supported s done} (t : Ticket p arg fields)
    (m : Assignment) (fit : ModelsExact s old m) (keep : List Nat) :
    ∃ n, ModelsExact (after s old keep t.jobs) (old ++ minted s old keep t.jobs) n ∧
      ∀ x ∈ stateNames s ++ (names old ++ keep), n x = m x := by
  obtain ⟨n,patch,kept⟩ := approved t.read t.calculated m fit.1 (names old ++ keep)
  have protect (x) (h : x ∈ stateNames s ++ (names old ++ keep)) : n x = m x := by
    rcases List.mem_append.mp h with before|caller
    · exact kept x (List.mem_append_left _ before)
    · exact kept x (List.mem_append_right _ (List.mem_append_right _ caller))
  have oldStill := (receipts_same (m := m) (n := n)
    (fun x h => protect x (List.mem_append_right _ (List.mem_append_left _ h)))).mpr fit.2
  refine ⟨n,⟨(model_append n).mpr ⟨patch.1,?_⟩,?_⟩,protect⟩
  · intro row written
    obtain ⟨e,listed,made⟩ := List.mem_flatMap.mp written
    exact endpoints_sound (patch.2 e listed) row made
  · intro e present
    exact (List.mem_append.mp present).elim (oldStill e) (patch.2 e)

end Yulang.GeneralDeclarativeCompoundBatch338
