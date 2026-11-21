import Yulang.GeneralDeclarativeSupportExample321

namespace Yulang.GeneralDeclarativeSupportCut321
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeSupportExample321 (origins demand state unfinished_blocks_second alternate_origins)
open GeneralDeclarativeLowerKnown321 (Ready ready_iff_not_delayed)

theorem same_state_distinct_support :
    Ready (origins True (fun _ => False)) demand ∧ ¬Ready (origins False (fun _ => False)) demand :=
  ⟨alternate_origins _ (.inr trivial),fun ready =>
    (ready_iff_not_delayed _ _).mp ready (unfinished_blocks_second _ (fun impossible => impossible))⟩

/-- Erasing provenance is sufficient to define ordinary models but loses
readiness, even if the same exact equation appears in both states. The
separate source derivation must not be reconstructed from a model set. -/
theorem no_bare_state_readiness (onlyState : State → Demand → Prop)
    (exact : ∀ backup : Prop, onlyState state demand ↔
      Ready (origins backup (fun _ => False)) demand) : False :=
  let established := (exact True).mpr same_state_distinct_support.1
  same_state_distinct_support.2 ((exact False).mp established)

end Yulang.GeneralDeclarativeSupportCut321
