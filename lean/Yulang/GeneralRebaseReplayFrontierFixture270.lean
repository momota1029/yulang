import Yulang.GeneralRebaseReplayFrontier270
import Yulang.GeneralRebaseReplayFixture270

set_option maxHeartbeats 5000000
set_option maxRecDepth 22000
namespace Yulang.GeneralRebaseReplayFrontierFixture270
open GeneralRebaseReplayFrontier270 (Frontier traces search no_visible_advance)
open GeneralRebaseReplaySearch270 (Replay)
open GeneralRebaseReplayScript270 (Script)

namespace Compound
open GeneralRebaseReplayFixture270.Compound (installCmd actual concrete_exit)
open GeneralDictionaryCompoundSource238 (registry)
open GeneralDictionaryJournalRefinement228Source (root)
open GeneralDictionaryCompoundFrame238 (before installed)
open GeneralRebaseSourceStrictFixture265 (owners pool)

noncomputable def offered : Frontier registry root 1 before := [⟨installCmd,()⟩]

theorem visible_exit :
 (search 1 before offered owners pool).map Subtype.val = some installed := by
 have shape : traces 1 before offered = [⟨before,.done before⟩,⟨installed,actual⟩] := rfl
 have initial : GeneralRebaseReplayScript270.first owners pool (.done before : Script registry root before before) = none := rfl
 unfold search
 rw [shape]
 simp only [List.findSome?_cons,initial,List.findSome?_nil]
 cases eq : GeneralRebaseReplayScript270.first owners pool actual with
 | none => simpa only [eq,Option.map_none] using concrete_exit
 | some witness => simpa only [eq,Option.orElse_some] using concrete_exit

/-- Finite checked search succeeds on the real install and exact target,
where no-depth search cannot by itself certify terminality. -/
theorem depth_zero : search (registry:=registry) (root:=root) 0 before () owners pool = none := rfl

end Compound

namespace Refresh
open GeneralRebaseReplayFixture270.Refresh (refreshCmd reviseCmd genuine owners pool no_hit)
open GeneralDictionaryVersionLoopSource237 (registry root)
open GeneralDictionaryVersionLoopFrame237 (installed)
open GeneralDictionaryVersionLoopRetarget237 (retargeted)

noncomputable def offered : Frontier registry root 2 installed := [⟨refreshCmd,[⟨reviseCmd,()⟩]⟩]

theorem computed_none : search 2 installed offered owners pool = none := by
 apply Option.isNone_iff_eq_none.mp
 decide +kernel

theorem supplied_path : (⟨retargeted,genuine⟩ : Replay registry root installed) ∈ traces 2 installed offered := by
 apply List.mem_cons_of_mem
 apply List.mem_flatMap.mpr
 refine ⟨⟨refreshCmd,[⟨reviseCmd,()⟩]⟩,List.mem_cons_self,?_⟩
 apply List.mem_map.mpr
 refine ⟨⟨retargeted,.execute reviseCmd (.done retargeted)⟩,?_,rfl⟩
 apply List.mem_cons_of_mem
 exact List.mem_cons_self

theorem all_supplied_are_lulls (program : Replay registry root installed)
 (seen : program ∈ traces 2 installed offered) :
 GeneralRebaseWeakProgress268.Lull registry root owners pool installed program.1 :=
 no_visible_advance 2 installed offered owners pool computed_none program seen

end Refresh
end Yulang.GeneralRebaseReplayFrontierFixture270
