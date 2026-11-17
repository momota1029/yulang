import Yulang.GeneralDictionaryVersionLoopRetarget237
import Yulang.GeneralNominalVersionedDependency236
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
/-! The verified local retarget produces a genuinely new repeated-capture
version, not an ordinary-context replay. No second installation or infinite
trace is asserted. -/
namespace Yulang.GeneralDictionaryVersionLoopNext237
open GeneralDictionaryVersionLoopSource237
open GeneralDictionaryVersionLoopPacket237 (lo hi origin0 origin1)
open GeneralDictionaryVersionLoopRetarget237
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
noncomputable abbrev current := retargeted.core.erased.current.context
noncomputable abbrev packet : GeneralNominalSaturationState.Packet roles :=
 ⟨registry,current,GeneralNominalDemandMerging.pointSite root,declaration,declaration_checked,[((3 : Fin 5),(3 : Fin 5))]⟩
noncomputable abbrev calculated : Report current.state where
 captures := [⟨0,((4 : Fin 5),(4 : Fin 5)),some origin0⟩,⟨0,((4 : Fin 5),(4 : Fin 5)),some origin1⟩]
 inspected := [((3 : Fin 5),(3 : Fin 5))]
 checked := [((3 : Fin 5),(3 : Fin 5)),((3 : Fin 5),(3 : Fin 5)),((4 : Fin 5),(4 : Fin 5)),((4 : Fin 5),(4 : Fin 5))]
 anchors := [(origin0,((4 : Fin 5),(4 : Fin 5))),(origin1,((4 : Fin 5),(4 : Fin 5)))]

theorem report_exact : report current declaration [((3 : Fin 5),(3 : Fin 5))] = calculated := by
 unfold report
 rw [show GeneralNominalInspection.queries current.state current.interpretation declaration =
   [.nominal 5 [.variables [0],.variables [0]]] from GeneralDictionaryVersionLoopPacket237.query]
 have nominal : current.state.nominals (3 : Fin 5) = some retarget := rfl
 simp [inspectMany,inspect,Report.visit,Report.append,typeArguments,calculated,nominal,retarget]
 rfl

theorem bindings_exact : packet.bindings = [(0,lo,lo),(0,lo,lo)] := by
 change bindings current.state (report current declaration [((3 : Fin 5),(3 : Fin 5))]) = _
 rw [report_exact]
 rfl

abbrev nextLo := GeneralNominalAggregateVersion231.slot 3 0 0 0 0 [(0,lo,lo),(0,lo,lo)]
abbrev nextHi := GeneralNominalAggregateVersion231.slot 3 0 0 1 0 [(0,lo,lo),(0,lo,lo)]
theorem grows : lo < nextLo :=
 (GeneralNominalVersionedDependency236.endpoints_below_slot 3 0 0 0 0 [(0,lo,lo),(0,lo,lo)]
   (by exact List.mem_cons_self : (lo,lo) ∈ GeneralNominalAllocation.occurrences [(0,lo,lo),(0,lo,lo)] 0)).1

theorem version_changed : GeneralNominalAggregateVersion231.version packet.bindings 0 ≠
 GeneralNominalAggregateVersion231.version GeneralDictionaryVersionLoopPacket237.packet.bindings 0 := by
 rw [bindings_exact,GeneralDictionaryVersionLoopPacket237.bindings_exact]
 intro equal
 have same := GeneralNominalAggregateVersion231.version_eq_iff.mp equal
 have head := List.cons.inj same |>.1
 have endpoint := congrArg Prod.fst head
 change lo = 2 at endpoint
 have large := GeneralDictionaryVersionLoopRefreshBase237.lo_large
 omega

theorem distinct_old_upper : nextLo ≠ hi :=
 GeneralNominalAggregateVersion231.distinct_purpose 3 0 0 0 1 0 _ _ (by decide)
end Yulang.GeneralDictionaryVersionLoopNext237
