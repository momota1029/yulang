import Yulang.GeneralDeclarativeHiddenResolve324
import Yulang.GeneralDeclarativeK2Mono324

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeHiddenStages324
open GeneralDeclarativeHiddenDecl324
open GeneralDeclarativeHiddenState324
open GeneralDeclarativeHiddenProbe324 (root_bounds no_cycle)
open GeneralDeclarativeHiddenResolve324 (root_only child_only)
open GeneralDeclarativeHiddenReads324 (body_root body_child rootUses)
open GeneralDeclarativeExampleSource320 (leaf point)
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeEntailment320 (literal)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeOrigins321 (Supported restriction from_source)
open GeneralDeclarativeOutputOrigins323 (emit)
open GeneralDeclarativePriority321 (Candidates Recurs)
open GeneralDeclarativeNFResolve324 (Rule)
open GeneralDeclarativeNFNode324 (Reads)
open GeneralDeclarativeNFHead324 (Scan produces)
open GeneralDeclarativeRecordWalk323 (closed_record)
open GeneralDeclarativeExactWalk323 (of_rigid)
open GeneralDeclarativeLowerKnown321 (Ready knows_row alias_refl)
open GeneralDeclarativeTrace321 (Trace)
open GeneralDeclarativeEndpointProbe321 (HeadMatches)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open GeneralNominalMaterialization (Mode)
open CommonRoleOutermostResolver (All₂)

inductive Stage where
  | initial
  | parentWritten
  | bothWritten
  deriving DecidableEq

def Stage.ordinary : Stage → State
  | .initial => GeneralDeclarativeHiddenState324.initial
  | .parentWritten => afterParent
  | .bothWritten => final

def Stage.equations (phase : Stage) (complete : Nat → Prop) : Supported phase.ordinary complete :=
  match phase with
  | .initial => sourceSupport complete
  | .parentWritten => emit (sourceSupport complete) 1 [parentRow]
  | .bothWritten => support complete

theorem old_source (phase : Stage) {row : Equation} (known : row ∈ s0Rows) : row ∈ phase.ordinary.equations := by
  cases phase with
  | initial => exact known
  | parentWritten => exact List.mem_append_left _ known
  | bothWritten => exact List.mem_append_left _ (List.mem_append_left _ known)

theorem proved_source (phase : Stage) (complete : Nat → Prop) {row : Equation} (source : row ∈ s0Rows) :
    row ∈ (restriction (phase.equations complete)).equations := by
  cases phase with
  | initial => exact from_source (sourceSupport complete) ⟨source,rfl⟩
  | parentWritten => exact from_source _ (.inl ⟨source,rfl⟩)
  | bothWritten => exact GeneralDeclarativeHiddenProbe324.source_row complete source

theorem final_contains (phase : Stage) : phase.ordinary.equations ⊆ final.equations := by
  intro row used
  cases phase with
  | initial => exact List.mem_append_left _ (List.mem_append_left _ used)
  | parentWritten => exact List.mem_append_left _ used
  | bothWritten => exact used

theorem normal_eq (phase : Stage) : phase.ordinary.normal = final.normal := by cases phase <;> rfl

theorem no_cycle_at (phase : Stage) (name) : ¬GeneralDeclarativeK2Alias321.AliasCycle phase.ordinary
    (GeneralDeclarativeGraphRows321.observed phase.ordinary) name :=
  fun c => no_cycle name (GeneralDeclarativeK2Mono324.preserve (normal_eq phase) (final_contains phase) c)

theorem parent_observed (phase : Stage) (complete : Nat → Prop) (mode : Mode) :
    Trace (restriction (phase.equations complete)) mode 0 normCode [⟨0,mode,3⟩] := by
  have first : (⟨0,opened⟩ : Equation) ∈ s0Rows := by simp [s0Rows]
  have tail : (⟨2,empty⟩ : Equation) ∈ s0Rows := by simp [s0Rows]
  exact .record (alias_refl _) (proved_source phase complete first) .capture
    (.primitive (args := []) (alias_refl _) (proved_source phase complete tail) .nil)

theorem tested_root (phase : Stage) (complete : Nat → Prop) :
    HeadMatches (restriction (phase.equations complete)) catalogue interpretation root parent :=
  .cons ⟨root_bounds _ 0,normCode,[⟨0,.lower,3⟩],[⟨0,.upper,3⟩],normal_compiles,
    parent_observed phase complete .lower,parent_observed phase complete .upper⟩ .nil

theorem tested_leaf (phase : Stage) (complete : Nat → Prop) :
    HeadMatches (restriction (phase.equations complete)) catalogue interpretation child leaf :=
  .cons ⟨root_bounds _ 3,.variable 0,[⟨0,.lower,3⟩],[⟨0,.upper,3⟩],rfl,.capture,.capture⟩ .nil

def candidate (stage : Stage) (complete : Nat → Prop) : Candidates :=
  ⟨HeadMatches (restriction (stage.equations complete)) catalogue interpretation,
   fun d decl => ¬HeadMatches (restriction (stage.equations complete)) catalogue interpretation d decl⟩

abbrev localRule (stage : Stage) (complete : Nat → Prop) :=
  Rule stage.ordinary registry interpretation (stage.equations complete) (candidate stage complete)

theorem no_recurs (phase : Stage) (complete : Nat → Prop) (d : Demand) :
    ¬Recurs phase.ordinary registry interpretation (candidate phase complete) d := by
  rintro (⟨a,_,c⟩|⟨decl,_,i,a,pat,code,_,_,_,site,_,c⟩)
  · exact no_cycle_at phase a.lower c
  · exact no_cycle_at phase site c

theorem root_ready' (phase : Stage) (complete : Nat → Prop) : Ready (phase.equations complete) root := by
  intro arg used
  cases List.mem_singleton.mp used
  exact ⟨_,knows_row (proved_source phase complete (show (⟨0,direct⟩ : Equation) ∈ s0Rows by simp [s0Rows])) rfl⟩

theorem leaf_ready' (phase : Stage) (complete : Nat → Prop) : Ready (phase.equations complete) child := by
  intro arg used
  cases List.mem_singleton.mp used
  exact ⟨_,knows_row (proved_source phase complete
    (show (⟨3,.primitive (.scalar .int) []⟩ : Equation) ∈ s0Rows by simp [s0Rows])) rfl⟩

end Yulang.GeneralDeclarativeHiddenStages324
