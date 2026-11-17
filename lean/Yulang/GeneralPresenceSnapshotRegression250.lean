import Yulang.GeneralPresencePersistentSnapshot250
import Yulang.CommonNominalFullConstructors
/-! Snapshot refresh is intentionally different from simultaneous cyclic
interpretation. This internal regression is not a source-language rejection. -/
namespace Yulang.GeneralPresenceSnapshotRegression250
open Core.PresenceGeneration PresenceNormalForm
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOrderedBlock247
open GeneralPresenceOrderedDependence247 GeneralPresenceOrderedSubstitution247
open CommonNominalFullCarrier

def old : List (Entry Nat) := [(2,.var 0),(3,.var 1)]
def raw : List (Entry Nat) := [(2,.var 3),(3,.var 2)]
def next : List (Entry Nat) := GeneralPresencePersistentSnapshot250.refresh old raw

theorem old_safe : SafeOrder old := by
 simp [old,SafeOrder,GeneralPresenceUsedSupport245.typedReads]

theorem raw_not_safe : ¬ SafeOrder raw := by
 simp [raw,SafeOrder,GeneralPresenceUsedSupport245.typedReads]

theorem snapshot_shape : next = [(2,.var 1),(3,.var 0)] := rfl

theorem next_safe : SafeOrder next := GeneralPresencePersistentSnapshot250.refresh_safe old raw old_safe

theorem full_targets : next.map Prod.fst = [2,3] := rfl

def before : Nat → Comp model := fun name =>
 (if name = 1 then .emptyRecord else model.exactEmpty,Common.rowEmpty)
def after : Nat → Comp model := solve model next before

theorem snapshot_satisfied : All model after (block next) :=
 block_satisfied model (subtype_refl) next next_safe before

theorem same_equations_not_satisfied : ¬ All model after (block raw) := by
 intro valid
 have bad : Subtype (after 2).1 (after 3).1 :=
   valid (.tyLe (.var 2) (.var 3)) (by simp [raw,block,equations])
 have two : (after 2).1 = .emptyRecord := rfl
 have three : (after 3).1 = model.exactEmpty := rfl
 rw [two,three] at bad
 exact width_not_below_exactEmpty bad

theorem omitted_slots_retained :
 (GeneralPresencePersistentSnapshot250.refresh old []).map Prod.fst = [2,3] := rfl

theorem later_slot_reactivated :
 GeneralPresencePersistentSnapshot250.refresh (GeneralPresencePersistentSnapshot250.refresh old []) raw = next := rfl
end Yulang.GeneralPresenceSnapshotRegression250
