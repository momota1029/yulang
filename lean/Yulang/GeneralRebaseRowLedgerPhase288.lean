import Yulang.GeneralRebaseRowRefreshHalt288
import Yulang.GeneralRebaseForeignLeaf288

/-! Executable fields for a scoped three-stage comparison. They do not
validate arbitrary ledger membership, especially not registry provenance. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28500
set_option maxHeartbeats 16000000
namespace Yulang.GeneralRebaseRowLedgerPhase288
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentFrame287 (after)
open GeneralRebaseRowLedger288 (supplemented unknown_output)
open GeneralRebaseRowRefreshShape288 (actually_nominal)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMixedObservations233 (Refresh)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalState (Known)
open GeneralCanonicalObservations (Recorded)

def hasDescriptor (snapshot : GeneralNominalState.State) (coordinate : Nat) : Bool :=
  (List.ofFn (fun slot => snapshot.base.source slot == coordinate && (snapshot.nominals slot).isSome)).any id

theorem hasDescriptor_exact (snapshot : GeneralNominalState.State) (coordinate : Nat) :
    hasDescriptor snapshot coordinate = true ↔
      ∃ slot, snapshot.base.source slot = coordinate ∧ ∃ d, snapshot.nominals slot = some d := by
  unfold hasDescriptor
  rw [List.any_eq_true]
  constructor
  · rintro ⟨b,member,value⟩
    obtain ⟨slot,read⟩ := List.mem_ofFn.mp member
    have eq : b = true := value
    rw [eq,Bool.and_eq_true] at read
    exact ⟨slot,beq_iff_eq.mp read.1,Option.isSome_iff_exists.mp read.2⟩
  · rintro ⟨slot,source,d,found⟩
    refine ⟨true,List.mem_ofFn.mpr ⟨slot,?_⟩,rfl⟩
    simp only [source,BEq.rfl,found,Option.isSome_some,Bool.and_self]

theorem absent_if_unknown {snapshot : GeneralNominalState.State} {coordinate : Nat}
    (unknown : ¬ Known snapshot coordinate) : hasDescriptor snapshot coordinate = false := by
  apply Bool.eq_false_iff.mpr
  intro pos
  obtain ⟨slot,atSlot,d,seen⟩ := (hasDescriptor_exact snapshot coordinate).mp pos
  exact unknown ⟨slot,atSlot,.inr ⟨d,seen⟩⟩

inductive Phase where | rawStop | ready | finished
  deriving Repr, DecidableEq

def phase (state : State roles) : Phase :=
  if state.plans.length = 2 then
    if hasDescriptor state.core.erased.current.context.state 2 then .finished else .ready
  else .rawStop

def next : Phase → Option Phase
  | .ready => some .finished
  | .rawStop | .finished => none

inductive Family : State roles → Prop where
  | original : Family (after true)
  | guarded : Family supplemented
  | finished (ctx : GeneralNominalCandidates.Context) : Refresh supplemented ctx → Known ctx.state 2 →
      Family (refresh supplemented ctx)

theorem original_phase : phase (after true) = .rawStop := rfl

theorem guarded_phase : phase supplemented = .ready := by
  unfold phase
  rw [show supplemented.plans.length = 2 from rfl,ite_eq_left rfl]
  change (if hasDescriptor (GeneralRebaseRowGeneratedChild287.current true).state 2 = true
    then Phase.finished else Phase.ready) = Phase.ready
  rw [absent_if_unknown (unknown_output true)]
  rfl

theorem finished_phase {ctx : GeneralNominalCandidates.Context} (certificate : Refresh supplemented ctx)
    (known : Known ctx.state 2) : phase (refresh supplemented ctx) = .finished := by
  have marked := actually_nominal ctx certificate known
  have present : hasDescriptor ctx.state 2 = true :=
    (hasDescriptor_exact ctx.state 2).mpr ⟨certificate.refines.base.embed (2 : Fin 3),
      certificate.refines.base.source (2 : Fin 3),_,marked⟩
  unfold phase
  rw [show (refresh supplemented ctx).plans.length = 2 from rfl,ite_eq_left rfl]
  change (if hasDescriptor ctx.state 2 = true then Phase.finished else Phase.ready) = Phase.finished
  rw [present,ite_eq_left rfl]

theorem unscoped_phase : phase GeneralRebaseForeignLeaf288.unscoped = .ready := by
  unfold phase
  rw [show GeneralRebaseForeignLeaf288.unscoped.plans.length = 2 from rfl,ite_eq_left rfl]
  change (if hasDescriptor (GeneralRebaseRowGeneratedChild287.current false).state 2 = true
    then Phase.finished else Phase.ready) = Phase.ready
  rw [absent_if_unknown (unknown_output false)]
  rfl

theorem phase_cannot_certify_membership :
    phase GeneralRebaseForeignLeaf288.unscoped = phase supplemented ∧
    ¬ Family GeneralRebaseForeignLeaf288.unscoped := by
  refine ⟨unscoped_phase.trans guarded_phase.symm,?_⟩
  intro lies
  cases lies

end Yulang.GeneralRebaseRowLedgerPhase288
