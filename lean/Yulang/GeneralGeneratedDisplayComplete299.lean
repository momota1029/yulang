import Yulang.GeneralGeneratedSelectedExact299
import Yulang.GeneralGeneratedDictionaryRootedFixtures299

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralGeneratedDisplayComplete299
open GeneralNominalExamples (registry displayRoot displayChild)
open GeneralDeclarationExamples (roles)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedJournal232 (Models)
open GeneralRebaseCompiledDisplay277 (after)
open GeneralGeneratedDisplayTable299 (decode table)
open GeneralGeneratedDisplayObserved299 (observedTable checked_rows faithful known)
open GeneralGeneratedDictionaryRootedFixtures299 (rooted_observed)
open GeneralGeneratedDictionaryRun299 (Closed run Entry)
open GeneralGeneratedMixedCurrentNodes299 (Providers scoped_nodes)
open GeneralGeneratedMixedRooted299 (scope_after_halt)
open GeneralGeneratedDictionaryNodes299 (Nodes)
open CommonRoleOutermostResolver (Dictionary Child)
open B4TargetV8

theorem observed_closed : Closed observedTable := by
  rw [checked_rows]
  exact GeneralGeneratedDisplayTable299.closed

theorem checked_all_rows (i : Nat) (e : Entry) (read : observedTable i = some e) (d : Dictionary) :
    run observedTable 2 i = some d ↔ Classify (boundary roles) registry after (decode i) (.selected d) :=
  GeneralGeneratedSelectedExact299.bounded_exact (b:=boundary roles) (r:=registry) (s:=after)
    observedTable decode faithful observed_closed [0,1] known i read d

theorem modeled (i : Nat) (d : Dictionary) (got : run observedTable 2 i = some d)
    (m) (valid : Models after m) : (boundary roles).Evidence registry after m (decode i) d := by
  have suppliers : Providers registry after observedTable decode := by
    rw [checked_rows]
    exact GeneralGeneratedDisplayBothCurrent299.providers
  have reached := GeneralRebaseCompiledInstall277.reachable
  have scope := scope_after_halt observedTable decode 0 (rfl : decode 0 = displayRoot)
    rooted_observed reached faithful suppliers ⟨m,valid⟩ GeneralRebasePackedNodeCompose298.no_second_raw_step
  have localRule := scoped_nodes observedTable decode reached faithful scope suppliers
  exact GeneralGeneratedDictionaryNodes299.same_model (b:=boundary roles) (r:=registry) (s:=after)
    observedTable decode localRule m valid 2 i d got

theorem exact_and_modeled (i : Nat) (e : Entry) (seen : observedTable i = some e) (d : Dictionary) :
    run observedTable 2 i = some d ↔
      Classify (boundary roles) registry after (decode i) (.selected d) ∧
      ∀ m, Models after m → (boundary roles).Evidence registry after m (decode i) d := by
  exact ⟨fun got => ⟨(checked_all_rows i e seen d).mp got,modeled i d got⟩,
    fun proof => (checked_all_rows i e seen d).mpr proof.1⟩

theorem actual_accessibility :
    Acc (Child (Local (boundary roles) registry after)) displayRoot ∧
    Acc (Child (Local (boundary roles) registry after)) displayChild := by
  have runRoot : run observedTable 2 0 = some (.node 1 [.node 3 []]) := by
    rw [checked_rows]; exact GeneralGeneratedDisplayTable299.computed_root
  have runChild : run observedTable 1 1 = some (.node 3 []) := by
    rw [checked_rows]; exact GeneralGeneratedDisplayTable299.computed_child
  exact ⟨GeneralGeneratedSemanticAcc299.semantic_accessible (b:=boundary roles) (r:=registry) (s:=after)
    observedTable decode faithful 2 0 _ runRoot,
    GeneralGeneratedSemanticAcc299.semantic_accessible (b:=boundary roles) (r:=registry) (s:=after)
      observedTable decode faithful 1 1 _ runChild⟩

end Yulang.GeneralGeneratedDisplayComplete299
