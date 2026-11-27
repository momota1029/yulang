import Yulang.GeneralDeclarativeI65I74ExactForwardingReplay467
import Yulang.GeneralDeclarativeI65I74PreparedExecution467
import Yulang.GeneralDeclarativeI65I74ExistingForwardedAddress467
import Yulang.GeneralDeclarativeI65I74ProjectionBatchInput464

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.ReceivedPhaseReplay467
open Yulang.GeneralDeclarativeI65
open GeneralDeclarativeI65.I72.NativeProducer465
open GeneralDeclarativeI65.I72.ExactForwardingReplay467
open GeneralDeclarativeI65.I72.NamedProjection464 (exactOrdinaryState exact_ordinary_snapshot_iff)
open GeneralDeclarativeWitnessNativePortTransport361 (Port transport)
open GeneralDeclarativeWitnessNativeDirectSource361 (Wire)
open GeneralDeclarativeWitnessSequentialNative360 (Sequence)
open GeneralDeclarativeWitnessNestedInstall360 (Run)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarativeWitnessDeclaredState357 (AuthoredNominal)
open GeneralDeclarativeWitnessNativeRelease360 (ReleaseAuthority)
open GeneralDeclarativeWitnessNativeInstall360 (interpreted)
open GeneralDeclarativeWitnessSequentialReceiver361 (Received receive layout)
open GeneralDeclarativeWitnessNativeReceiver360 (key)
open GeneralDeclarativeWitnessNativePreparation360 (prepare context)
open GeneralDeclarativeWitnessScopedBindings359 (slots)
open GeneralDeclarativeWitnessCompiler350 (execute)
open GeneralDeclarativeI65.I72.PreparedExecution467 (native_preparation_replays_exact_independent_record)

theorem independent_exact_receiver_execution_replays {negative} {r : Run negative}
    {seq : Sequence r} (rec : Received seq) : receive seq = some rec := by
  rcases rec with ⟨prepared,head,span,bound,center,body,ran,noWrites,noKids,kept⟩
  have p := native_preparation_replays_exact_independent_record prepared
  unfold receive
  simp [p,Bind.bind,Option.bind,head]
  split
  · rename_i absent
    rw [bound] at absent
    cases absent
  · rename_i actual eq
    have identical := Option.some.inj (bound.symm.trans eq)
    subst actual
    simp only [dite_eq_left center]
    split
    · rename_i absent
      rw [ran] at absent
      cases absent
    · rename_i emitted eq
      have same := Option.some.inj (ran.symm.trans eq)
      subst emitted
      simp [noWrites,noKids,kept]


/-- The supplied current ordinary snapshot and ledgers remain inputs. The
catalogue is pinned to the same authenticated compiler run by construction. -/
structure SuppliedReceiverLedger where
  ordinary : GeneralDeclarativeHead320.State
  visible : List AuthoredNominal
  modes : CommonDeclaredNominalInspection.Registry
  origins : List Origin
  routes : List GeneralDeclarativeI65.Alias

def SuppliedReceiverLedger.core (a : SuppliedReceiverLedger) (env : Environment) : GeneralDeclarativeI65.State :=
  ⟨⟨env,a.ordinary,a.visible⟩,a.modes,a.origins,a.routes⟩

/-- Observe the already installed parent's complete address from the
actual receiving compiler world. This is an internal read and never
commits an origin, a candidate, or a raw step. -/
def checkForwardedInActualReceiver {negative} {r : Run negative}
    (seq : Sequence r) (ledger : SuppliedReceiverLedger) (gate : ReleaseAuthority)
    (w : Wire) (ordinal : Nat) : Bool :=
  match transport seq gate w, receive seq with
  | some _,some rec =>
    if same : exactOrdinaryState rec.world.ordinary ledger.ordinary = true then
      checkPhaseOrigin (s := ledger.core r.env)
        ⟨rec.world,(exact_ordinary_snapshot_iff ..).mp same,gate⟩ r.typed.write rec.span.center ordinal
    else false
  | _,_ => false

def ExactForwardedReceiver {negative} {r : Run negative}
    (seq : Sequence r) (ledger : SuppliedReceiverLedger) (gate : ReleaseAuthority)
    (w : Wire) (ordinal : Nat) : Prop :=
  Nonempty (Port seq gate w) ∧ ∃ rec : Received seq,
    ∃ same : rec.world.ordinary = ledger.ordinary,
      PhaseOriginAt (s := ledger.core r.env) ⟨rec.world,same,gate⟩
        r.typed.write rec.span.center ordinal

theorem one_existing_forwarded_receiver_iff_finite_data {negative} {r : Run negative}
    (seq : Sequence r) (ledger : SuppliedReceiverLedger) (gate : ReleaseAuthority)
    (w : Wire) (ordinal : Nat) :
    checkForwardedInActualReceiver seq ledger gate w ordinal = true ↔
      ExactForwardedReceiver seq ledger gate w ordinal := by
  constructor
  · intro yes
    cases src : transport seq gate w with
    | none => simp [checkForwardedInActualReceiver,src] at yes
    | some port =>
      cases got : receive seq with
      | none => simp [checkForwardedInActualReceiver,src,got] at yes
      | some rec =>
        by_cases same : exactOrdinaryState rec.world.ordinary ledger.ordinary = true
        · have atPhase : checkPhaseOrigin (s := ledger.core r.env)
              ⟨rec.world,(exact_ordinary_snapshot_iff ..).mp same,gate⟩
              r.typed.write rec.span.center ordinal = true := by
            simpa [checkForwardedInActualReceiver,src,got,same] using yes
          exact ⟨⟨port⟩,rec,(exact_ordinary_snapshot_iff ..).mp same,
            (finite_phase_origin_check_iff_literal_placed_active_row ..).mp atPhase⟩
        · simp [checkForwardedInActualReceiver,src,got,same] at yes
  · rintro ⟨⟨port⟩,rec,same,released⟩
    have src := independent_exact_forwarded_port_replays port
    have got := independent_exact_receiver_execution_replays rec
    have exact := (exact_ordinary_snapshot_iff ..).mpr same
    have ok := (finite_phase_origin_check_iff_literal_placed_active_row ..).mpr released
    simp [checkForwardedInActualReceiver,src,got,exact,ok]

theorem same_fitting_receiver_reads_old_physical_code_not_fresh_assignment
    {negative} {r : Run negative} {seq : Sequence r} {ledger : SuppliedReceiverLedger}
    {gate : ReleaseAuthority} {w : Wire} {ordinal : Nat}
    (accepted : checkForwardedInActualReceiver seq ledger gate w ordinal = true)
    (m : Model) (fits : GeneralDeclarativeI65.Fits (ledger.core r.env) m) :
    ∃ rec : Received seq,
      receive seq = some rec ∧
      rec.world.ordinary = ledger.ordinary ∧
      rec.world.board = seq.final.board ∧
      rec.span.center = r.typed.write.address.target ∧ rec.body.fixed = [] ∧
      m.nativeSyntax rec.span.center = some (GeneralDeclarativeWitnessNativeOrder362.node r.typed.write.code) ∧
      interpreted rec.world.board m.assignment rec.span.center = some (r.typed.write.code.eval m.assignment) := by
  obtain ⟨⟨port⟩,rec,same,atOrigin⟩ := (one_existing_forwarded_receiver_iff_finite_data ..).mp accepted
  have endpoints := GeneralDeclarativeI65.I72.ExistingForwardedAddress467.receiving_compiler_body_keeps_the_exact_parent_address_and_output port rec
  have both := GeneralDeclarativeI65.I72.ExistingForwardedAddress467.existing_forwarded_address_same_state_semantics
    port rec (ledger.core r.env) same ordinal atOrigin.1 atOrigin.2.1 m fits
  exact ⟨rec,independent_exact_receiver_execution_replays rec,same,endpoints.1,endpoints.2.2.1,
    endpoints.2.2.2.2,both⟩

end Yulang.GeneralDeclarativeI65.I72.ReceivedPhaseReplay467
