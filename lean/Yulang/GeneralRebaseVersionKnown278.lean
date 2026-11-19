import Yulang.GeneralRebaseInstallTimeline278
import Yulang.GeneralRebaseVersionRefreshLeaf278

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 26000
set_option maxHeartbeats 7500000
namespace Yulang.GeneralRebaseVersionKnown278
open GeneralDictionaryVersionLoopIteration239 (state stages)
open GeneralDictionaryVersionLoopBook239 (context allocations reservations atoms)
open GeneralDictionaryVersionLoopFamilyBase238 (source source_small source_large foo pair)
open GeneralDictionaryVersionLoopNames238 (lower lower_above)
open GeneralRebaseVersionMicro278 (raw installed refreshed)
open GeneralRebaseInstallTimeline278 (observedCount)
open GeneralRebaseRoundMicro278 (Tick)
open GeneralNominalState (Known)

def position (n i : Nat) (inRange : i < n) : Fin (n+4) := ⟨i+4,by omega⟩

theorem position_reads (n i : Nat) (inRange : i < n) :
    source n (position n i inRange) = lower (i+1) := by
  rw [source_large _ (by change 4 ≤ i+4; omega)]
  congr 1

theorem read_implies (n i : Nat) (loc : Fin (n+4)) (found : source n loc = lower (i+1)) : i < n := by
  by_cases small : loc.val < 4
  · rw [source_small loc small] at found
    have above := lower_above i
    omega
  · rw [source_large loc (by omega)] at found
    have exact := GeneralDictionaryVersionLoopNames238.injective found
    have bounded := loc.isLt
    omega

theorem point_known (n i : Nat) : Known (context n).state (lower (i+1)) ↔ i < n := by
  constructor
  · rintro ⟨slot,located,_⟩
    exact read_implies n i slot located
  · intro seen
    let slot := position n i seen
    refine ⟨slot,position_reads n i seen,Or.inr ⟨foo n,?_⟩⟩
    change (if slot.val=3 then some (pair n) else if slot.val=2 ∨ 4 ≤ slot.val then some (foo n) else none) = some (foo n)
    have notThree : ¬ slot.val = 3 := by dsimp [slot,position]; omega
    have old : slot.val=2 ∨ 4 ≤ slot.val := Or.inr (by dsimp [slot,position]; omega)
    simp only [notThree,old,ite_false,ite_true]

theorem exposed_known (n i : Nat) : Known
    (GeneralDictionaryVersionLoopFamilyExpose238.exposed n (allocations n) (reservations n) (atoms n)).state
    (lower (i+1)) ↔ i < n+1 := by
  constructor
  · rintro ⟨slot,located,_⟩
    exact read_implies (n+1) i slot located
  · intro seen
    let slot := position (n+1) i seen
    refine ⟨slot,position_reads (n+1) i seen,?_⟩
    change _ ∨ ∃ desc, (if slot.val=n+4 then some (GeneralDictionaryVersionLoopFamilyRefines238.looseDescriptor n)
      else if slot.val=3 then some (GeneralDictionaryVersionLoopFamilyRefines238.rootDescriptor n)
      else if slot.val=2 ∨ 4 ≤ slot.val then some (foo (n+1)) else none) = some desc
    by_cases fresh : slot.val = n+4
    · exact Or.inr ⟨GeneralDictionaryVersionLoopFamilyRefines238.looseDescriptor n,by simp only [fresh,ite_true]⟩
    · have notThree : ¬ slot.val = 3 := by dsimp [slot,position]; omega
      have supported : slot.val=2 ∨ 4 ≤ slot.val := Or.inr (by dsimp [slot,position]; omega)
      exact Or.inr ⟨foo (n+1),by simp only [fresh,notThree,supported,ite_false,ite_true]⟩

theorem prefix_known (t : Tick) (i : Nat) :
    Known (raw t).core.erased.current.context.state (lower (i+1)) ↔ i < observedCount t := by
  rcases t with ⟨n,p⟩
  cases p
  · change Known (state n).core.erased.current.context.state (lower (i+1)) ↔ i<n
    rw [(stages n).shape.current]
    exact point_known n i
  · exact point_known n i
  · exact exposed_known n i

end Yulang.GeneralRebaseVersionKnown278
