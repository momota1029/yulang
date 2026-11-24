import Yulang.GeneralDeclarativeI65PinnedNativeRead381
import Yulang.GeneralDeclarativeWitnessNativeSnapshot360

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open GeneralDeclarativeWitnessNativePreparation360 (Prepared)
open GeneralDeclarativeWitnessNativeValue360 (Write Compiled)
open GeneralDeclarativeWitnessNativeInstall360 (World install atTarget other_target_unchanged no_ordinary_override)
open GeneralDeclarativeWitnessNativeSnapshot360 (commit commits_exact_snapshot)
open GeneralDeclarativeWitnessNativeRelease360 (ReleaseAuthority)

/-- A real snapshot commit fixes its input ordinary state and literal
installed row. The consumer's source must still retain its origin and
the exact original route. This theorem has no grant input or output. -/
theorem exact_snapshot_commit_source382
    {s : State} {logical : Nat} {env frame d layout table wire version}
    {p : Prepared env frame d layout} (emission : Compiled p table wire version)
    {prior final : World} (ran : commit p emission prior = some final)
    (current : final.ordinary = s.current.ordinary)
    (retained : originalOfWrite emission.write ∈ s.origins)
    (route : OriginRoute s (originalOfWrite emission.write) logical) :
    prior.ordinary = layout.named ∧ final.ordinary = p.stage ∧
      RetainedPhysicalOrigin381 s final emission.write logical := by
  obtain ⟨priorExact,installation⟩ := commits_exact_snapshot p emission ran
  exact ⟨priorExact,no_ordinary_override p emission installation,
    retained_physical_origin_of_install381 emission installation current retained route⟩

/-- For the actual new row the externally supplied gate, at the exact
final world of the commit, is still the only authority input. Both
the positive and the absent-grant cases use the same installed row. -/
theorem committed_source_needs_its_exact_gate382
    {s : State} {logical : Nat} {env frame d layout table wire version}
    {p : Prepared env frame d layout} (emission : Compiled p table wire version)
    {prior final : World} (ran : commit p emission prior = some final)
    (current : final.ordinary = s.current.ordinary) (gate : ReleaseAuthority)
    (retained : originalOfWrite emission.write ∈ s.origins)
    (route : OriginRoute s (originalOfWrite emission.write) logical) :
    Nonempty (BoundNativeRead381 s final gate emission.write) ↔
      emission.write.address ∈ gate.grants :=
  native_context_read_iff_its_grant381
    (exact_snapshot_commit_source382 emission ran current retained route).2.2

/-- A real other-target commit preserves the older literal write and
owner; it does not infer an older logical origin from equality of
values. Retention and route are about the new actual source snapshot. -/
theorem earlier_source_survives_other_commit382
    {before after : State} {logical : Nat} {earlier : Write} {env frame d layout table wire version}
    {p : Prepared env frame d layout} (emission : Compiled p table wire version)
    {prior final : World} (ran : commit p emission prior = some final)
    (priorRail : RetainedPhysicalOrigin381 before prior earlier logical)
    (separate : earlier.address.target ≠ emission.write.address.target)
    (current : final.ordinary = after.current.ordinary)
    (retained : originalOfWrite earlier ∈ after.origins)
    (route : OriginRoute after (originalOfWrite earlier) logical) :
    RetainedPhysicalOrigin381 after final earlier logical := by
  obtain ⟨_,performed⟩ := commits_exact_snapshot p emission ran
  unfold install at performed
  split at performed
  · have same := Option.some.inj performed
    cases same
    exact ⟨current,(other_target_unchanged prior.board emission.write
      earlier.address.target separate).trans priorRail.atTarget,
      priorRail.active,priorRail.unique,retained,route⟩
  · cases performed

/-- Transport the *truth* of a pinned read through the transaction with
the same independently supplied gate, including the withheld case.
The before and after read types retain their own exact world indices. -/
theorem earlier_exact_gate_survives_other_commit382
    {before after : State} {logical : Nat} {earlier : Write} {env frame d layout table wire version}
    {p : Prepared env frame d layout} (emission : Compiled p table wire version)
    {prior final : World} (ran : commit p emission prior = some final)
    (priorRail : RetainedPhysicalOrigin381 before prior earlier logical)
    (separate : earlier.address.target ≠ emission.write.address.target)
    (current : final.ordinary = after.current.ordinary) (gate : ReleaseAuthority)
    (retained : originalOfWrite earlier ∈ after.origins)
    (route : OriginRoute after (originalOfWrite earlier) logical) :
    Nonempty (BoundNativeRead381 before prior gate earlier) ↔
      Nonempty (BoundNativeRead381 after final gate earlier) :=
  (native_context_read_iff_its_grant381 priorRail).trans
    (native_context_read_iff_its_grant381
      (earlier_source_survives_other_commit382 emission ran priorRail separate current retained route)).symm

end Yulang.GeneralDeclarativeI65
