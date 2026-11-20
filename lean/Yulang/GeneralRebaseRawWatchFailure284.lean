import Yulang.GeneralRebaseVersionWatchLower284
import Yulang.GeneralRebaseLooseWatchLower284

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseRawWatchFailure284
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Ty model Equivalent Subtype)
open GeneralPresenceDefinitionRewrite244 (Entry)
open GeneralPresenceOrderedBlock247 (put solve solve_rows solve_outside put_outside)
open GeneralRebaseFutureWatch284 (trim member_exact)
open GeneralRebaseHistoryOrder282 (history decode ordered compatible)

variable {roles : Roles.RoleDecls} {state : State roles} {registry : Registry} {root : Occurrence roles}

theorem ignores_written (seen : Reachable registry root state) (base : Assignment)
    (row : Entry Nat) (member : row ∈ history state) (replacement : Ty) :
    decode state (put model base row.1 replacement) = decode state base := by
  unfold decode
  have record := GeneralNominalVersionedMixedSeedLedger237.reachable seen
  have safe := (ordered state).2.2
  apply GeneralRebaseExactHistory283.unique (history state)
    (GeneralRebaseProspectiveDelta283.descending_history state record)
  · intro n
    exact (solve_rows model _ _ n).trans
      ((GeneralPresenceOrderedBlock247.put_rows model base row.1 replacement n).trans (solve_rows model _ _ n).symm)
  · intro n outside
    rw [solve_outside model _ _ n outside, solve_outside model _ _ n outside]
    exact put_outside model base row.1 replacement n (outside row member)
  · exact fun e => GeneralRebaseExactHistory283.equation _ safe _ e
  · exact fun e => GeneralRebaseExactHistory283.equation _ safe _ e

def eraseProbe (watch : List Nat) (state : State roles) (base : Assignment) (id : Nat) :=
  solve model (trim watch (history state)) (put model base id .bottom)

theorem absent_target (watch : List Nat) (state : State roles) (base : Assignment) (id : Nat)
    (missing : id ∉ watch) : (eraseProbe watch state base id id).1 = .bottom := by
  unfold eraseProbe
  rw [solve_outside model _ _ id (fun row found eq => missing (eq ▸ ((member_exact ..).mp found).2))]
  simp [put]

theorem unmodified_observable (watch : List Nat) (state : State roles) (base : Assignment) (id front : Nat)
    (unchanged : ∀ r ∈ history state, r.1 ≠ front) (distinct : id ≠ front) :
    eraseProbe watch state base id front = base front := by
  unfold eraseProbe
  rw [solve_outside model _ _ front (fun row found => unchanged row ((member_exact ..).mp found).1)]
  exact put_outside model base id .bottom front distinct

theorem omitted_unsound (seen : Reachable registry root state) (base : Assignment)
    (oldValid : Models state base) (watch : List Nat) (row : Entry Nat) (recorded : row ∈ history state)
    (missing : row.1 ∉ watch) (front : Nat)
    (unmodified : ∀ r ∈ history state, r.1 ≠ front)
    (nonbottom : ¬ Subtype (base front).1 .bottom)
    (forces : ∀ a, Models state a → Equivalent (a row.1).1 (a front).1) :
    Models state (decode state (put model base row.1 .bottom)) ∧
      ¬ Models state (eraseProbe watch state base row.1) := by
  constructor
  · rw [ignores_written seen base row recorded .bottom]
    exact (GeneralNominalVersionedSourceCongruence238.source_models_iff (compatible seen oldValid) seen).mpr oldValid
  · intro invalid
    have compare := forces _ invalid
    rw [absent_target watch state base row.1 missing,
      unmodified_observable watch state base row.1 front unmodified (unmodified row recorded)] at compare
    exact nonbottom compare.2

theorem nominal_not_bottom : ¬ Subtype
    (CommonNominalFullCarrier.nominal 0 [.inl (.base .int)]) .bottom := by
  intro bad
  exact GeneralNominalCenteredHeadMatHeadShape.bottom_no_head (.nominal 0 1)
    ⟨[.inl (.base .int)],rfl,(by
      intro depth
      apply (CommonNominalFullDemand.producerLe_iff_probe _ _).mpr
      intro rank env observation accepted
      exact CommonNominalFullDemand.probeAt_bottom rank observation),bad⟩

end Yulang.GeneralRebaseRawWatchFailure284
