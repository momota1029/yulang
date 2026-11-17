import Yulang.GeneralNominalVersionedAggregateLedger236
import Yulang.GeneralNominalVersionedMixedGrowth234
set_option backward.isDefEq.respectTransparency false
/-! Actual plan snapshots retain one allocation seed. Historical aggregate-ID
lookup therefore does not need a separate seed-equality assumption. -/
namespace Yulang.GeneralNominalVersionedMixedSeedLedger237
open GeneralNominalVersionedJournal232 GeneralNominalVersionedMixedKernel234
open GeneralNominalVersionedAggregateLedger236 (packetEntries)
variable {roles : Roles.RoleDecls}
def Recorded (state : State roles) : Prop :=
 ∀ plan ∈ state.plans, plan.packet.context.state.seed = state.core.erased.current.context.state.seed

theorem lift (legacy : Legacy.State roles) : Recorded (GeneralNominalVersionedJournal232.lift legacy) := by
 intro plan member; cases member

theorem step (action : Step registry root before after) (recorded : Recorded before) : Recorded after := by
 have seed := (GeneralNominalVersionedMixedGrowth234.step action).seed
 obtain ⟨focus,generated,action⟩ := action
 cases action with
 | administrative action =>
   cases action <;> intro plan member <;> exact (recorded plan member).trans seed.symm
 | refresh | merge => intro plan member; exact (recorded plan member).trans seed.symm
 | install effect enabled novel =>
   intro plan member
   rcases List.mem_cons.mp member with rfl | member
   · rfl
   · exact (recorded plan member).trans seed.symm

theorem steps (path : B4Target.Steps (Step registry root) before after) (recorded : Recorded before) : Recorded after := by
 induction path with
 | refl => exact recorded
 | tail _ action ih => exact step action ih

theorem reachable (path : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state) :
 Recorded state := by
 obtain ⟨first,⟨legacy,_,same⟩,trace⟩ := path
 subst first
 exact steps trace (lift legacy)

def IdCovered (pool : List Nat) (state : State roles) (packet : GeneralNominalSaturationState.Packet roles) : Prop :=
 ∀ entry ∈ packetEntries packet, entry.1 ∈ pool →
 ∃ prior ∈ state.plans, ∃ old ∈ packetEntries prior.packet, old.1 = entry.1

theorem covered (recorded : Recorded state) (context : packet.context = state.core.erased.current.context)
 (ids : IdCovered pool state packet) : GeneralNominalVersionedAggregateLedger236.ProtectedCovered pool state packet := by
 intro entry member inside
 obtain ⟨prior,present,old,oldMember,same⟩ := ids entry member inside
 exact ⟨prior,present,(recorded prior present).trans (congrArg (fun context => context.state.seed) context).symm,
   old,oldMember,same⟩

def entries (state : State roles) : List GeneralNominalFiniteEquationRealization236.Entry :=
 state.plans.flatMap fun plan => packetEntries plan.packet

theorem same_entry (recorded : Recorded state) (one : first ∈ entries state)
 (two : last ∈ entries state) (same : first.1 = last.1) : first.2 = last.2 := by
 obtain ⟨a,am,one⟩ := List.mem_flatMap.mp one
 obtain ⟨b,bm,two⟩ := List.mem_flatMap.mp two
 have seed := (recorded a am).trans (recorded b bm).symm
 unfold packetEntries at one two
 rw [seed] at one
 exact GeneralNominalVersionedAggregateLedger236.same_target one two same

theorem source_same_entry
 (path : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state)
 (one : first ∈ entries state) (two : last ∈ entries state) (same : first.1 = last.1) : first.2 = last.2 :=
 same_entry (reachable path) one two same
end Yulang.GeneralNominalVersionedMixedSeedLedger237
