import Yulang.GeneralRebaseReceiptFixture289

/-! Semantic adequacy is restricted to actual raw paths. A bare Wire or an
arbitrary state with the same Models is not a certification of provenance. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28500
set_option maxHeartbeats 18000000
namespace Yulang.GeneralRebaseReceiptWitness289
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentPacket287 (child)
open GeneralRebaseRowParentFrame287 (after effect)
open GeneralRebaseRowLeafSlice288 (prior)
open GeneralRebaseRowLeafWitness288 (leaf)
open GeneralRebaseReceiptFixture289 (wire request endpoint_decision initial_no_producer)
open GeneralRebaseReceiptWire289 (check)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalSaturationState (Generated)
open GeneralRebaseInertLeaf288 (Leaf)
open GeneralRebaseLeafOutput288 (Extension)

def ActualPath (choice : Bool) (s : State roles) : Prop :=
  B4Target.Steps (Step (registry choice) root) before s

structure Witness (choice : Bool) (s : State roles) : Prop where
  producerRecorded : effect choice ∈ s.effects
  generation : Generated s.core.erased.current root (child choice)
  sourceLeaf : ∃ key p, Leaf (registry choice) s (child choice) key p
  exactOutputCut : Extension s (prior choice) (effect choice)

theorem witness_initial_absent (choice : Bool) : ¬ Witness choice before := by
  intro p
  exact List.not_mem_nil p.producerRecorded

theorem witness_positive : Witness true (after true) := by
  exact ⟨List.mem_singleton_self _,GeneralRebaseRowParentStep287.generated true,⟨1,_,leaf⟩,
    (GeneralRebaseRowLeafSlice288.extension_iff true).mpr rfl⟩

theorem witness_negative_absent : ¬ Witness false (after false) := by
  intro p
  have h := (GeneralRebaseRowLeafSlice288.extension_iff false).mp p.exactOutputCut
  cases h

theorem check_iff (choice : Bool) {s : State roles} (path : ActualPath choice s) :
    check (wire choice s) (request choice) = .ready ↔ Witness choice s := by
  rcases GeneralRebaseRowActualPaths287.one_or_zero choice s path with rfl | rfl
  · rw [initial_no_producer]
    exact ⟨(fun h => nomatch h),fun h => (witness_initial_absent choice h).elim⟩
  · rw [endpoint_decision]
    cases choice
    · exact ⟨(fun h => nomatch h),fun h => (witness_negative_absent h).elim⟩
    · exact ⟨fun _ => witness_positive,fun _ => rfl⟩

theorem only_actual_release (choice : Bool) {s : State roles} (path : ActualPath choice s) :
    Witness choice s ↔ choice = true ∧ s = after choice := by
  rcases GeneralRebaseRowActualPaths287.one_or_zero choice s path with rfl | rfl
  · constructor
    · exact fun h => (witness_initial_absent _ h).elim
    · rintro ⟨_,bad⟩
      have length := congrArg (fun j : State roles => j.effects.length) bad
      change 0 = (1 : Nat) at length
      cases length
  · cases choice
    · exact ⟨fun h => (witness_negative_absent h).elim,fun ⟨impossible,_⟩ => nomatch impossible⟩
    · exact ⟨fun _ => ⟨rfl,rfl⟩,fun _ => witness_positive⟩

theorem after_reachable (choice : Bool) : ActualPath choice (after choice) :=
  .tail .refl (GeneralRebaseRowParentStep287.actual_step choice)

end Yulang.GeneralRebaseReceiptWitness289
