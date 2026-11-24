import Yulang.GeneralDeclarativeI65SourceBoundary382

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open GeneralDeclarativeWitnessNativePreparation360 (Prepared)
open GeneralDeclarativeWitnessNativeValue360 (Write Compiled)
open GeneralDeclarativeWitnessNativeInstall360 (World no_ordinary_override)
open GeneralDeclarativeWitnessNativeSnapshot360 (commit commits_exact_snapshot)
open GeneralDeclarativeWitnessNativeRelease360 (ReleaseAuthority checkExactRelease)
open GeneralDeclarativeWitnessLiteral349 (preserves_iff)
open GeneralDeclarativeGrowth327 (Extends)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeEntailment320 (appendFacts)
open GeneralDeclarativeWitnessOrigins350 (support)
open GeneralDeclarativeOrigins321 (restriction)

/-- Ordinary weakening through the actual native snapshot commit, with
its exact prior ordinary state and compiler retention proof. This is
not a monotonicity statement for matching, pending, or K2. -/
theorem actual_commit_grows_boundary382
    {before after : State} (c : SourceBoundary382 before)
    {env frame d layout table wire version} {p : Prepared env frame d layout}
    (emitted : Compiled p table wire version) {out : World}
    (ran : commit p emitted c.world = some out)
    (same : out.ordinary = after.current.ordinary) :
    Extends before.current.ordinary after.current.ordinary := by
  obtain ⟨prior,actual⟩ := commits_exact_snapshot p emitted ran
  rw [← c.current,prior,← same,no_ordinary_override p emitted actual]
  exact (preserves_iff ..).mp p.retained

/-- Reattach the *same* complete ordinary table and *same* independent
gate after a real commit. Newly emitted ordinary equalities are not
thereby authorized source facts, and no grant is added. -/
def retain_boundary_after_actual_commit382
    {before after : State} (c : SourceBoundary382 before)
    {env frame d layout table wire version} {p : Prepared env frame d layout}
    (emitted : Compiled p table wire version) {out : World}
    (ran : commit p emitted c.world = some out)
    (same : out.ordinary = after.current.ordinary) : SourceBoundary382 after :=
  let grow := actual_commit_grows_boundary382 c emitted ran same
  ⟨c.ledger,⟨fun _ found => grow.equations (c.ordinary.authored found),
    fun chunk found => grow.equations (c.ordinary.produced chunk found)⟩,out,same,c.gate⟩

/-- Conditions for carrying an *existing* read after a typed commit.
An ordinary read stays in its fixed ledger; an older native read needs
its literal target separate plus retained authored source and route. -/
def OriginalReadRetained382 (after : State) (newWrite : Write) : PrimitiveKey382 → Prop
  | .ordinary _ => True
  | .native prior logical => prior.address.target ≠ newWrite.address.target ∧
      originalOfWrite prior ∈ after.origins ∧ OriginRoute after (originalOfWrite prior) logical

/-- Produce the pinned observation under a supplied independently known
grant, by reducing the real exact-release check on the supplied world. -/
def read_under_given_full_grant382
    {s : State} {world : World} {gate : ReleaseAuthority} {written : Write} {logical : Nat}
    (rail : RetainedPhysicalOrigin381 s world written logical)
    (known : written.address ∈ gate.grants) : BoundNativeRead381 s world gate written :=
  let actual := (checkExactRelease world.board gate written).get
    ((exact_native_authority_iff381 rail gate).mpr known)
  ⟨⟨world,rail.current,gate,written,actual,rfl,rfl,rfl⟩,rfl,rfl⟩

/-- Transport, rather than reconstruct from availability: the authored
branch or precise ordinary owner is preserved. A native observation
is reopened in the exact final world under the exact same grant. -/
def carry_existing_primitive_after_commit382
    {before after : State} (c : SourceBoundary382 before)
    {env frame d layout table wire version} {p : Prepared env frame d layout}
    (emitted : Compiled p table wire version) {out : World}
    (ran : commit p emitted c.world = some out)
    (same : out.ordinary = after.current.ordinary)
    {k : PrimitiveKey382} (read : PrimitiveRead382 c k)
    (retains : OriginalReadRetained382 after emitted.write k) :
    PrimitiveRead382 (retain_boundary_after_actual_commit382 c emitted ran same) k :=
  match read with
  | .authored row proof => .authored row proof
  | .completed row owner proof done => .completed row owner proof done
  | .native written logical rail proof =>
    let carried := earlier_source_survives_other_commit382 emitted ran rail retains.1 same retains.2.1 retains.2.2
    let hasGrant := (native_context_read_iff_its_grant381 rail).mp ⟨proof⟩
    .native written logical carried (read_under_given_full_grant382 carried hasGrant)

inductive PrimitiveRouteKind382 where
  | authored
  | completed (owner : Nat)
  | native

def exactPrimitiveRoute382 {s : State} {c : SourceBoundary382 s} {k : PrimitiveKey382} :
    PrimitiveRead382 c k → PrimitiveRouteKind382
  | .authored _ _ => .authored
  | .completed _ owner _ _ => .completed owner
  | .native _ _ _ _ => .native

/-- The unchanged index keeps the full physical native write and the
original logical position; this equality additionally rules out
replacing one ordinary source route by another at the same row. -/
theorem existing_primitive_commit_keeps_actual_route382
    {before after : State} (c : SourceBoundary382 before)
    {env frame d layout table wire version} {p : Prepared env frame d layout}
    (emitted : Compiled p table wire version) {out : World}
    (ran : commit p emitted c.world = some out) (same : out.ordinary = after.current.ordinary)
    {k : PrimitiveKey382} (read : PrimitiveRead382 c k)
    (retains : OriginalReadRetained382 after emitted.write k) :
    exactPrimitiveRoute382 (carry_existing_primitive_after_commit382 c emitted ran same read retains) =
      exactPrimitiveRoute382 read := by
  cases read <;> rfl

def exactPrimitiveRoutes382 {s : State} {c : SourceBoundary382 s} {keys : List PrimitiveKey382} :
    PrimitiveReads382 c keys → List PrimitiveRouteKind382
  | .nil => []
  | .cons here rest => exactPrimitiveRoute382 here :: exactPrimitiveRoutes382 rest

def carry_existing_primitive_list_after_commit382
    {before after : State} (c : SourceBoundary382 before)
    {env frame d layout table wire version} {p : Prepared env frame d layout}
    (emitted : Compiled p table wire version) {out : World}
    (ran : commit p emitted c.world = some out) (same : out.ordinary = after.current.ordinary)
    {keys : List PrimitiveKey382} (reads : PrimitiveReads382 c keys)
    (retains : ∀ k ∈ keys, OriginalReadRetained382 after emitted.write k) :
    PrimitiveReads382 (retain_boundary_after_actual_commit382 c emitted ran same) keys :=
  match reads with
  | .nil => .nil
  | .cons first rest =>
    .cons (carry_existing_primitive_after_commit382 c emitted ran same first
        (retains _ List.mem_cons_self))
      (carry_existing_primitive_list_after_commit382 c emitted ran same rest
        (fun k seen => retains k (List.mem_cons_of_mem _ seen)))

theorem existing_primitive_list_commit_keeps_actual_route_order382
    {before after : State} (c : SourceBoundary382 before)
    {env frame d layout table wire version} {p : Prepared env frame d layout}
    (emitted : Compiled p table wire version) {out : World}
    (ran : commit p emitted c.world = some out) (same : out.ordinary = after.current.ordinary)
    {keys : List PrimitiveKey382} (reads : PrimitiveReads382 c keys)
    (retains : ∀ k ∈ keys, OriginalReadRetained382 after emitted.write k) :
    exactPrimitiveRoutes382
        (carry_existing_primitive_list_after_commit382 c emitted ran same reads retains) =
      exactPrimitiveRoutes382 reads := by
  induction reads with
  | nil => rfl
  | cons first rest ih =>
    simp only [carry_existing_primitive_list_after_commit382,exactPrimitiveRoutes382,
      existing_primitive_commit_keeps_actual_route382,ih]

/-- An actual where equation exists in the post-commit ordinary
snapshot, but cannot be used as an authorized input through the
unchanged provenance manifest if all of its source routes lack authority.
This does not remove the equation from the ordinary K2 graph. -/
theorem actual_where_row_does_not_create_authority382
    {before after : State} (c : SourceBoundary382 before)
    {env frame d layout table wire version} {p : Prepared env frame d layout}
    (emitted : Compiled p table wire version) {out : World}
    (ran : commit p emitted c.world = some out) (same : out.ordinary = after.current.ordinary)
    (row : Equation) (isWhere : row ∈ p.whereRows) (notWritten : row ∉ c.ledger.authored)
    (noCompletion : ∀ owner, (row,owner) ∈ c.ledger.produced → owner ∉ c.ledger.released) :
    row ∈ after.current.ordinary.equations ∧
      ¬Nonempty (PrimitiveRead382 (retain_boundary_after_actual_commit382 c emitted ran same)
        (.ordinary row)) := by
  obtain ⟨_,installed⟩ := commits_exact_snapshot p emitted ran
  let retained := retain_boundary_after_actual_commit382 c emitted ran same
  constructor
  · rw [← same,no_ordinary_override p emitted installed]
    change row ∈ p.before.equations ++ p.whereRows
    exact List.mem_append_right _ isWhere
  · intro reads
    have observed := (boundary_ordinary_read_iff382 retained row).mp reads
    rcases (ordinary_support_requires_actual_origin382 retained.ordinary row).mp observed
      with direct|⟨owner,stored,completed⟩
    · exact notWritten direct
    · exact noCompletion owner stored completed

end Yulang.GeneralDeclarativeI65
