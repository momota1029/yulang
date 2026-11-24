import Yulang.GeneralDeclarativeI65LiteralBoundarySources382

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open GeneralDeclarativeWitnessNativePreparation360 (Prepared)
open GeneralDeclarativeWitnessNativeValue360 (Write Compiled)
open GeneralDeclarativeWitnessNativeInstall360 (World)
open GeneralDeclarativeWitnessNativeSnapshot360 (commit)
open GeneralDeclarativeWitnessNativeRelease360 (ReleaseAuthority)
open GeneralDeclarativeWitnessAuthoredProjection358 (Source)
open GeneralDeclarativeWitnessSourceEndpoint359 (Witness Read)
open GeneralDeclarativeWhere319 (Capture)

def endpointThenNativeKeys382 (span : Capture) (lo hi : Witness)
    (written : Write) (logical : Nat) : List PrimitiveKey382 :=
  ((writtenEndpointRows382 span.lower lo).map PrimitiveKey382.ordinary ++
    (writtenEndpointRows382 span.upper hi).map PrimitiveKey382.ordinary) ++ [.native written logical]

/-- Exact input observation for one real snapshot commit. Both authored
endpoint witnesses are independent, and the new native row and scope
are the literal ones installed and retained. Its release still requires
the actual, already supplied grant; the compiler commit does not grant. -/
theorem mixed_endpoints_after_actual_commit_iff_full_grant382
    {before after : State} (c : SourceBoundary382 before)
    {env frame d layout table wire version} {prep : Prepared env frame d layout}
    (emission : Compiled prep table wire version) {out : World}
    (ran : commit prep emission c.world = some out)
    (same : out.ordinary = after.current.ordinary)
    {source : Source} {span : Capture} {lo hi : Witness}
    (sameAuthor : source.authored = c.ledger.authored)
    (lower : Read source after.current.ordinary span.lower lo)
    (upper : Read source after.current.ordinary span.upper hi)
    {logical : Nat} (retained : originalOfWrite emission.write ∈ after.origins)
    (route : OriginRoute after (originalOfWrite emission.write) logical) :
    Nonempty (PrimitiveReads382 (retain_boundary_after_actual_commit382 c emission ran same)
      (endpointThenNativeKeys382 span lo hi emission.write logical)) ↔
      emission.write.address ∈ c.gate.grants := by
  let current := retain_boundary_after_actual_commit382 c emission ran same
  constructor
  · intro reads
    have last : .native emission.write logical ∈
        endpointThenNativeKeys382 span lo hi emission.write logical :=
      List.mem_append_right _ List.mem_cons_self
    have full := (ordered_primitive_boundary_exact382 current _).mp reads _ last
    exact full.2
  · intro grant
    have rail := (exact_snapshot_commit_source382 emission ran same retained route).2.2
    let pinned := read_under_given_full_grant382 (gate := c.gate) rail grant
    obtain ⟨opened⟩ := pinned_origin_exact_release381 rail pinned
    obtain ⟨reads,_⟩ := actual_two_endpoints_and_native_share_literal_source382 current
      sameAuthor lower upper rail opened
    exact ⟨reads⟩

/-- Comparison of two independently reported manifests. This record
update never authenticates or issues the alternative gate. -/
def comparingReportedGate382 {s : State} (c : SourceBoundary382 s) (gate : ReleaseAuthority) :
    SourceBoundary382 s := { c with gate := gate }

/-- Real joint cut: the same actual compiler commit, after-state,
ordinary author data, physical world and literal endpoint reads are
consistent with different primitive read availability at two supplied
gates. This shows the loss from erasing the actual manifest, not
a difference in language verdicts. -/
theorem mixed_commit_read_not_recoverable_from_state_world382
    {before after : State} (c : SourceBoundary382 before)
    {env frame d layout table wire version} {prep : Prepared env frame d layout}
    (emission : Compiled prep table wire version) {out : World}
    (ran : commit prep emission c.world = some out)
    (same : out.ordinary = after.current.ordinary)
    {source : Source} {span : Capture} {lo hi : Witness}
    (sameAuthor : source.authored = c.ledger.authored)
    (lower : Read source after.current.ordinary span.lower lo)
    (upper : Read source after.current.ordinary span.upper hi)
    {logical : Nat} (retained : originalOfWrite emission.write ∈ after.origins)
    (route : OriginRoute after (originalOfWrite emission.write) logical)
    (other : ReleaseAuthority)
    (granted : emission.write.address ∈ c.gate.grants)
    (withheld : emission.write.address ∉ other.grants)
    (erased : State → World → List PrimitiveKey382 → Prop) :
    ¬(let keys := endpointThenNativeKeys382 span lo hi emission.write logical
      (erased after out keys ↔
        Nonempty (PrimitiveReads382 (retain_boundary_after_actual_commit382 c emission ran same) keys)) ∧
      (erased after out keys ↔ Nonempty (PrimitiveReads382
        (retain_boundary_after_actual_commit382 (comparingReportedGate382 c other) emission ran same) keys))) := by
  rintro ⟨first,second⟩
  have yes := (mixed_endpoints_after_actual_commit_iff_full_grant382 c emission ran same
    sameAuthor lower upper retained route).mpr granted
  have no := second.mp (first.mpr yes)
  exact withheld ((mixed_endpoints_after_actual_commit_iff_full_grant382
    (comparingReportedGate382 c other) emission ran same sameAuthor lower upper retained route).mp no)

end Yulang.GeneralDeclarativeI65
