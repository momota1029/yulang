import Yulang.GeneralRebaseWatchTrace284

namespace Yulang.GeneralRebaseFutureCounter284
open GeneralPresenceDefinitionRewrite244 (Entry)
open GeneralPresenceOrderedBlock247 (solve SafeOrder)
open GeneralRebaseFutureWatch284 (Closed Covers trim)
open GeneralRebaseWatchStep284 (NoReveal next)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (model)

def before : List (Entry Nat) := [(4,.var 1)]
def packet : List (Entry Nat) := [(5,.var 4)]
def allAfter : List (Entry Nat) := before ++ packet
def present : List Nat := [1]
def future : List Nat := [1,4,5]
def base : Assignment := fun n => (if n = 1 then .top else .bottom, Common.rowEmpty)

theorem closed_now : Closed present before := by
  intro e member asked
  rcases List.mem_singleton.mp member with rfl
  simp [present] at asked

theorem closed_next : Closed future allAfter := by
  intro e member asked i seen
  change e ∈ ([(4,.var 1),(5,.var 4)] : List (Entry Nat)) at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl <;> cases List.mem_singleton.mp seen <;> decide

theorem erased : trim present before = [] := rfl

theorem noReveal_fails : ¬ NoReveal present future before := by
  intro safe
  have wrongly : 4 ∈ present := safe (4,.var 1) (List.mem_singleton_self _) (by decide)
  simp [present] at wrongly

theorem future_breaks :
    (solve model (next future (trim present before) packet) base 5).1 ≠
      (solve model allAfter base 5).1 := by
  change (.bottom : CommonNominalFullCarrier.Ty) ≠ .top
  intro equal
  cases equal

end Yulang.GeneralRebaseFutureCounter284
