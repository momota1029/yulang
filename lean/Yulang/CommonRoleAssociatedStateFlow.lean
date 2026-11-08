import Yulang.CommonRoleCandidateStateFrontier
import Yulang.RoleConstraints
import Yulang.CommonRoleSourceIdentity

/-! Computed associated RHS values produce ordinary equations. The receiver
is a supplied first-order goal, not inferred from singleton visibility.
Only the existing int/str constructor codes are interpreted in this fragment. -/
namespace Yulang.CommonRoleAssociatedStateFlow
open CommonRoleSettledConstraints (State)
open CommonRoleCandidateStateFrontier (Candidate)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)

structure Request (n : Nat) where
  receiver : Roles.Goal
  name : Nat
  output : Fin n

def scalar : Roles.Term → Option Inference.Base
  | .app 0 [] => some .int
  | .app 1 [] => some .str
  | _ => none

def value (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (q : Request n) : Option Inference.Base :=
  if Roles.argsBound q.receiver.args = 0 then
    (Roles.assocOf env roles wf q.receiver q.name).bind scalar
  else none

def produce (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (q : Request n) (s : State n) : Option (State n) :=
  (value env roles wf q).map (CommonRoleCandidateStateFrontier.extend s q.output)

/-- Declaration result and scalar decoding are retained as explicit provenance. -/
def Computed (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (q : Request n) (head : Inference.Base) : Prop :=
  Roles.argsBound q.receiver.args = 0 ∧
    ∃ rhs, Roles.assocOf env roles wf q.receiver q.name = some rhs ∧ scalar rhs = some head

theorem value_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (q : Request n) (head : Inference.Base) :
    value env roles wf q = some head ↔ Computed env roles wf q head := by
  by_cases known : Roles.argsBound q.receiver.args = 0
  · simp [value, Computed, known, Option.bind_eq_some_iff]
  · simp [value, Computed, known]

/-- Lower the ordinary source equation emitted by the existing source adapter.
The left variable must be exactly the requested output identity. -/
def lowerStore (q : Request n) (s : State n) : RoleConstraints.Store → Option (State n)
  | [⟨.var identity, rhs⟩] =>
      if identity = q.output.val then
        (scalar rhs).map (CommonRoleCandidateStateFrontier.extend s q.output)
      else none
  | _ => none

def fromSourceStore (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (q : Request n) (s : State n) : Option (State n) :=
  if Roles.argsBound q.receiver.args = 0 then
    (RoleConstraints.addAssociated env roles wf q.receiver q.name q.output.val []).bind
      (lowerStore q s)
  else none

/-- The new ordinary-slot producer agrees with actual source equation generation. -/
theorem source_store_agrees (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (q : Request n) (s : State n) :
    fromSourceStore env roles wf q s = produce env roles wf q s := by
  by_cases known : Roles.argsBound q.receiver.args = 0
  · cases computed : Roles.assocOf env roles wf q.receiver q.name <;>
      simp [fromSourceStore, produce, value, known, RoleConstraints.addAssociated,
        computed, lowerStore]
  · simp [fromSourceStore, produce, value, known]

theorem produce_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (q : Request n) (s out : State n) :
    produce env roles wf q s = some out ↔
      ∃ head, Computed env roles wf q head ∧
        CommonRoleCandidateStateFrontier.extend s q.output head = out := by
  simp only [produce, Option.map_eq_some_iff, value_exact]

theorem models_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (q : Request n) (s out : State n)
    (head : Inference.Base) (computed : Computed env roles wf q head)
    (produced : produce env roles wf q s = some out)
    (assignment : Fin n → Comp Common.model) :
    All Common.model assignment out.atoms ↔
      All Common.model assignment s.atoms ∧
      Common.Equivalent (assignment q.output).1 (.base head) := by
  have hv := (value_exact ..).mpr computed
  have he : CommonRoleCandidateStateFrontier.extend s q.output head = out := by
    simpa only [produce, hv, Option.map_some, Option.some.injEq] using produced
  rw [← he]
  exact CommonRoleCandidateStateFrontier.extend_exact ..

/-- Unknown receivers remain pending even when only one impl is visible. -/
theorem unknown_preserved (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (q : Request n) (s : State n)
    (unknown : Roles.argsBound q.receiver.args ≠ 0) :
    produce env roles wf q s = none := by simp [produce, value, unknown]

/-- A separate declaration derivation, together with resolved ground receiver,
produces the same equation; no ordinary atom premise is supplied. -/
theorem computed_of_derivation (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (q : Request n) (rhs : Roles.Term) (head : Inference.Base)
    (known : Roles.argsBound q.receiver.args = 0)
    (resolved : Roles.resolve env.cores wf q.receiver = .resolved)
    (derivation : Roles.AssocDerives env roles q.receiver q.name rhs)
    (decoded : scalar rhs = some head) : Computed env roles wf q head :=
  ⟨known, rhs, Roles.assoc_derivation_agrees env roles wf awf _ _ resolved derivation, decoded⟩

/-- No output is produced for an unresolved or unsupported associated result. -/
theorem unresolved_preserved (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (q : Request n) (s : State n)
    (unresolved : Roles.assocOf env roles wf q.receiver q.name = none) :
    produce env roles wf q s = none := by simp [produce, value, unresolved]

def recollect (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (q : Request n) (s : State n)
    (visible : List Candidate) : Option (List Candidate) :=
  (produce env roles wf q s).map fun out =>
    CommonRoleCandidateStateFrontier.collect out q.output visible

theorem recollect_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (q : Request n) (s : State n)
    (head : Inference.Base) (computed : Computed env roles wf q head)
    (visible : List Candidate) (c : Candidate) :
    (∃ found, recollect env roles wf q s visible = some found ∧ c ∈ found) ↔
      c ∈ CommonRoleCandidateStateFrontier.collect s q.output visible ∧ head = c.head := by
  have hv := (value_exact ..).mpr computed
  simp only [recollect, produce, hv, Option.map_some, Option.some.injEq]
  constructor
  · rintro ⟨found, rfl, member⟩
    exact (CommonRoleCandidateStateFrontier.collect_after_equation ..).mp member
  · intro member
    exact ⟨_, rfl, (CommonRoleCandidateStateFrontier.collect_after_equation ..).mpr member⟩

/-- Sibling recollection may inspect a different occurrence of the same source. -/
def recollectAt (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (q : Request n) (s : State n)
    (sibling : Fin n) (visible : List Candidate) : Option (List Candidate) :=
  (produce env roles wf q s).map fun out =>
    CommonRoleCandidateStateFrontier.collect out sibling visible

theorem recollect_shared_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (table : CommonRoleSourceIdentity.Table)
    (q : Request table.length) (s : State table.length)
    (sibling : Fin table.length)
    (same : CommonRoleSourceIdentity.source table sibling =
      CommonRoleSourceIdentity.source table q.output)
    (head : Inference.Base) (computed : Computed env roles wf q head)
    (visible : List Candidate) (c : Candidate) :
    (∃ found, recollectAt env roles wf q (CommonRoleSourceIdentity.extend table s)
      sibling visible = some found ∧ c ∈ found) ↔
      c ∈ CommonRoleCandidateStateFrontier.collect
        (CommonRoleSourceIdentity.extend table s) sibling visible ∧ head = c.head := by
  have hv := (value_exact ..).mpr computed
  simp only [recollectAt, produce, hv, Option.map_some, Option.some.injEq]
  constructor
  · rintro ⟨found, rfl, member⟩
    obtain ⟨vis, fits⟩ := (CommonRoleCandidateStateFrontier.collect_exact ..).mp member
    obtain ⟨old, eq⟩ := (CommonRoleSourceIdentity.fits_after_shared_equation
      table s sibling q.output same head c).mp fits
    exact ⟨(CommonRoleCandidateStateFrontier.collect_exact ..).mpr ⟨vis, old⟩, eq⟩
  · rintro ⟨member, eq⟩
    obtain ⟨vis, old⟩ := (CommonRoleCandidateStateFrontier.collect_exact ..).mp member
    exact ⟨_, rfl, (CommonRoleCandidateStateFrontier.collect_exact ..).mpr
      ⟨vis, (CommonRoleSourceIdentity.fits_after_shared_equation
        table s sibling q.output same head c).mpr ⟨old, eq⟩⟩⟩

namespace Example
open Roles.AssocExamples

def request : Request 1 := ⟨index (box Roles.Examples.str) Roles.Examples.int, 0, 0⟩

theorem declaration_computes :
    Computed (singletonEnv boxImpl) requiredRoles box_paterson request .str :=
  ⟨rfl, Roles.Examples.str, box_value, rfl⟩

/-- The call site supplies a declaration/receiver/output binding, no ordinary atoms. -/
def run : Option (List Candidate) :=
  recollect (singletonEnv boxImpl) requiredRoles box_paterson request State.empty
    [CommonRoleCandidateStateFrontier.leftInt, CommonRoleCandidateStateFrontier.leftStr]

theorem derived_narrowing :
    (∃ found, run = some found ∧ CommonRoleCandidateStateFrontier.leftStr ∈ found) ∧
    ¬ (∃ found, run = some found ∧ CommonRoleCandidateStateFrontier.leftInt ∈ found) := by
  constructor
  · apply (recollect_exact _ _ _ _ _ .str declaration_computes _ _).mpr
    exact ⟨CommonRoleCandidateStateFrontier.before_associated_equation.2, rfl⟩
  · intro h
    have wrong := ((recollect_exact _ _ _ _ _ .str declaration_computes _ _).mp h).2
    cases wrong

/-- Two occurrences of source variable 7: Left consumes slot 0, while the
computed associated body writes slot 1. Ordinary equations are generated. -/
abbrev sourceTable : CommonRoleSourceIdentity.Table := [7, 7]
def rightRequest : Request sourceTable.length :=
  ⟨index (box Roles.Examples.str) Roles.Examples.int, 0, 1⟩
def sharedRun : Option (List Candidate) :=
  recollectAt (singletonEnv boxImpl) requiredRoles box_paterson rightRequest
    (CommonRoleSourceIdentity.extend sourceTable State.empty) 0
    [CommonRoleCandidateStateFrontier.leftInt, CommonRoleCandidateStateFrontier.leftStr]

theorem shared_before (c : Candidate) :
    CommonRoleCandidateStateFrontier.Fits
      (CommonRoleSourceIdentity.extend sourceTable State.empty) 0 c := by
  refine ⟨fun _ => Comp.pure Common.model (.base c.head), ?_, Common.equivalent_refl _⟩
  apply (CommonRoleSourceIdentity.extend_exact ..).mpr
  exact ⟨PresenceNormalForm.all_nil _ _, fun _ _ _ => Common.equivalent_refl _⟩

theorem shared_declaration_narrowing :
    (∃ found, sharedRun = some found ∧ CommonRoleCandidateStateFrontier.leftStr ∈ found) ∧
    ¬ (∃ found, sharedRun = some found ∧ CommonRoleCandidateStateFrontier.leftInt ∈ found) := by
  have computed : Computed (singletonEnv boxImpl) requiredRoles box_paterson rightRequest .str :=
    ⟨rfl, Roles.Examples.str, box_value, rfl⟩
  have same : CommonRoleSourceIdentity.source sourceTable (0 : Fin sourceTable.length) =
      CommonRoleSourceIdentity.source sourceTable rightRequest.output := rfl
  constructor
  · apply (recollect_shared_exact _ _ _ sourceTable rightRequest State.empty 0 same
      .str computed _ _).mpr
    exact ⟨(CommonRoleCandidateStateFrontier.collect_exact ..).mpr
      ⟨by simp, shared_before _⟩, rfl⟩
  · intro h
    have wrong := ((recollect_shared_exact _ _ _ sourceTable rightRequest State.empty 0 same
      .str computed _ _).mp h).2
    cases wrong

end Example
end Yulang.CommonRoleAssociatedStateFlow
