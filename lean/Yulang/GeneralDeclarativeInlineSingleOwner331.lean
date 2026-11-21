import Yulang.GeneralDeclarativeInlineOrigins331

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeInlineSingleOwner331
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeOrigins321 (Supported Available restriction backed_iff from_completed)
open GeneralDeclarativeLowerKnown321 (Knows constructorTag knows_row)
open GeneralDeclarativeGrowth327 (Extends)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeInlineTrace331 (Read)
open GeneralDeclarativeInlineLineage331 (Trail carries)
open GeneralDeclarativeInlineMaterial331 (ordinary seed)
open GeneralDeclarativeInlineAllocation331 (jobs)
open GeneralDeclarativeInlineGround331 (sourcesOnly job_spelling)
open GeneralDeclarativeInlineOrigins331 (fromOrigins complete)
open GeneralDeclarativeNewNames321 (numbered rhs_exact)
open GeneralDeclarativeTermWalk322 (Occurrence)
open GeneralNominalCenteredHeadMatExpressions (Expr)

/-- A proof-facing view which can name exactly one original producer.
It does not set its real completion flag. Normal facts, as in the
underlying declarative state, are retained separately. -/
def only {s : State} (p : Supported s done) (owner : Nat) : Supported s (fun n => n = owner) :=
  ⟨p.derivesFrom,p.ordinary⟩

theorem only_lifts {s : State} (p : Supported s done) (finished : done owner) :
    Extends (restriction (only p owner)) (restriction p) := by
  refine ⟨fun _ h => h,fun _ h => h,?_⟩
  intro eq has
  obtain ⟨o,native,visible⟩ := (backed_iff (only p owner) eq).mp has
  apply (backed_iff p eq).mpr
  refine ⟨o,native,?_⟩
  cases visible with
  | source => exact .source
  | completed which =>
    cases which
    exact .completed finished

/-- A fresh exact compiler row justified by one producer plus original
sources. The record syntax is an independent traversal. It is not
re-labelled as source if the producer happens to finish. -/
def Native {s : State} (p : Supported s done) (owner : Nat)
    (arg : Capture) (keep : List Nat) (uses : List Occurrence) (row : Equation) : Prop :=
  row ∈ ordinary s arg keep uses ∧
    ∃ code, Read (restriction (only p owner)) .actual (.variable arg.center) code uses ∧
      ¬Read (restriction (sourcesOnly p)) .actual (.variable arg.center) code uses

def certify {s t : State} (prior : Supported s done) (old : Extends s t)
    (owner : Nat) (arg : Capture) (keep : List Nat) (uses : List Occurrence)
    (present : ordinary s arg keep uses ⊆ t.equations) : Supported t done :=
  ⟨fun e origin => prior.derivesFrom e origin ∨
      origin = .output owner ∧ Native prior owner arg keep uses e,
    fun actual => actual.elim (fun priorRow => old.equations (prior.ordinary priorRow))
      (fun derived => present derived.2.1)⟩

theorem exact_backing {s t : State} {p : Supported s done} (old : Extends s t)
    (rows : ordinary s arg keep uses ⊆ t.equations) (owner : Nat) :
    row ∈ (restriction (certify p old owner arg keep uses rows)).equations ↔
      row ∈ (restriction p).equations ∨ Native p owner arg keep uses row ∧ done owner := by
  constructor
  · intro h
    obtain ⟨origin,native,active⟩ := (backed_iff _ _).mp h
    rcases native with original|⟨rfl,derived⟩
    · exact .inl ((backed_iff p _).mpr ⟨origin,original,active⟩)
    · cases active with
      | completed yes => exact .inr ⟨derived,yes⟩
  · intro why
    rcases why with oldRow|⟨path,ready⟩
    · obtain ⟨origin,ground,okay⟩ := (backed_iff p _).mp oldRow
      exact (backed_iff _ _).mpr ⟨origin,.inl ground,okay⟩
    · exact from_completed _ (.inr ⟨rfl,path⟩) ready

theorem expansion_after_owner {s t : State} {p : Supported s done} (old : Extends s t)
    (rows : ordinary s arg keep uses ⊆ t.equations)
    (fromOne : Native p owner arg keep uses row) (ready : done owner)
    (shape : constructorTag row.right = some tag) :
    Knows (restriction (certify p old owner arg keep uses rows)) row.left tag :=
  knows_row ((exact_backing old rows owner).mpr (.inr ⟨fromOne,ready⟩)) shape

theorem no_retag {s t : State} {p : Supported s done} (old : Extends s t)
    (rows : ordinary s arg keep uses ⊆ t.equations)
    (claim : (certify p old owner arg keep uses rows).derivesFrom row .source) :
    p.derivesFrom row .source := by
  rcases claim with prior|⟨impossible,_⟩
  · exact prior
  · cases impossible

end Yulang.GeneralDeclarativeInlineSingleOwner331
