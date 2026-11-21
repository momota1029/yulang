import Yulang.GeneralDeclarativeInlineLineage331

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeInlineGround331
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeOrigins321 (Supported Available restriction backed_iff from_source)
open GeneralDeclarativeLowerKnown321 (Knows constructorTag knows_row)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeGrowth327 (Extends)
open GeneralDeclarativeInlineTrace331 (Read)
open GeneralDeclarativeInlineAllocation331 (jobs)
open GeneralDeclarativeInlineMaterial331 (ordinary seed)
open GeneralDeclarativeInlineLineage331 (Trail carries)
open GeneralDeclarativeTermWalk322 (Occurrence)
open GeneralDeclarativeRecordPoints330 (expanded)
open GeneralDeclarativeNewNames321 (numbered rhs_exact)
open GeneralNominalCenteredHeadMatExpressions (Expr)

/-- Only genuine source-backed observations can be stored under the
source origin. An output that happened to have completed is still
not relabelled as source. No completed flag is consulted here. -/
def sourcesOnly {s : State} (p : Supported s done) : Supported s (fun _ => False) :=
  ⟨p.derivesFrom,p.ordinary⟩

theorem actual_source_row {s : State} {p : Supported s done} {e : Equation} :
    e ∈ (restriction (sourcesOnly p)).equations ↔ p.derivesFrom e .source := by
  constructor
  · intro eIn
    obtain ⟨o,proven,allowed⟩ := (backed_iff (sourcesOnly p) e).mp eIn
    cases allowed with
    | source => exact proven
    | completed h => exact False.elim h
  · exact from_source (sourcesOnly p)

theorem job_spelling {e term : Expr} (seen : e ∈ expanded term) :
    e = term ∧ ∀ n, term ≠ .variable n := by
  cases term
  case «variable» => cases seen
  all_goals
    cases List.mem_singleton.mp seen
    exact ⟨rfl,fun _ impossible => by cases impossible⟩

theorem origin_path {s : State} {p : Supported s done}
    (guide : Read (restriction (sourcesOnly p)) .actual (.variable arg.center) pattern uses)
    {row : Equation} (ordinaryRow : row ∈ ordinary s arg targets uses) :
    ∃ loc ∈ uses, row.right = loc.term ∧ (∀ n, loc.term ≠ .variable n) ∧
      Trail (restriction (sourcesOnly p)) (.variable arg.center) loc.term := by
  have hand : row ∈ numbered (seed s arg targets uses) (jobs uses) := ordinaryRow
  have rhs : row.right ∈ jobs uses := by
    rw [← rhs_exact (seed s arg targets uses) (jobs uses)]
    exact List.mem_map.mpr ⟨row,hand,rfl⟩
  obtain ⟨o,seen,real⟩ := List.mem_flatMap.mp rhs
  obtain ⟨spelling,complex⟩ := job_spelling real
  exact ⟨o,seen,spelling,complex,carries guide o seen⟩

/-- Ordinary materialized rows alone do not prove source access.
For a fixed actual traversal and generated batch, the source
view can retain the precise rooted source witness for the fresh
definition, separately from the whole-head semantic read row. -/
def Native {s : State} (p : Supported s done) (arg : Capture)
    (keep : List Nat) (uses : List Occurrence) (row : Equation) : Prop :=
  row ∈ ordinary s arg keep uses ∧
    ∃ pattern, Read (restriction (sourcesOnly p)) .actual (.variable arg.center) pattern uses

def certify {s t : State} (original : Supported s done) (old : Extends s t) (arg : Capture)
    (keep : List Nat) (uses : List Occurrence) (rows : ordinary s arg keep uses ⊆ t.equations) :
    Supported t done :=
  ⟨fun e origin => original.derivesFrom e origin ∨ origin = .source ∧ Native original arg keep uses e,
    fun h => h.elim (fun a => old.equations (original.ordinary a)) (fun a => rows a.2.1)⟩

theorem derived_backed {s t : State} {p : Supported s done} (old : Extends s t)
    (rows : ordinary s arg keep uses ⊆ t.equations)
    (path : Native p arg keep uses row) :
    row ∈ (restriction (certify p old arg keep uses rows)).equations :=
  from_source _ (.inr ⟨rfl,path⟩)

theorem grounded_known {s t : State} {p : Supported s done} (old : Extends s t)
    (rows : ordinary s arg keep uses ⊆ t.equations)
    (path : Native p arg keep uses row) (shape : constructorTag row.right = some tag) :
    Knows (restriction (certify p old arg keep uses rows)) row.left tag :=
  knows_row (derived_backed old rows path) shape

theorem no_forgery {s t : State} {p : Supported s done} (old : Extends s t)
    (rows : ordinary s arg keep uses ⊆ t.equations)
    (support : row ∈ (restriction (certify p old arg keep uses rows)).equations) :
    row ∈ (restriction p).equations ∨
      ∃ loc ∈ uses, row.right = loc.term ∧ (∀ n, loc.term ≠ .variable n) ∧
        Trail (restriction (sourcesOnly p)) (.variable arg.center) loc.term := by
  obtain ⟨origin,why,active⟩ := (backed_iff _ row).mp support
  rcases why with original|⟨_,stored,code,trace⟩
  · exact .inl ((backed_iff _ _).mpr ⟨origin,original,active⟩)
  · exact .inr (origin_path trace stored)

end Yulang.GeneralDeclarativeInlineGround331
