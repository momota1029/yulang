import Yulang.GeneralRebaseLoopView282
import Yulang.GeneralRebaseTerminalBridge274
import Yulang.GeneralRebaseTerminalMixedRefresh274

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 30000
set_option maxHeartbeats 11000000
namespace Yulang.GeneralRebaseOptionalView282
open GeneralRebaseWholeRow282 (Keeps Projection initialNames initial_projection)
open GeneralRebaseWholeJournal282 (View)
open GeneralRebasePrivateStore282 (Joint)
open GeneralRebaseTermCopy281 (Respects)
open GeneralRebaseLiveStore282 (live)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
open GeneralDictionaryVersionedSecondInstall233 (installed)
open GeneralDictionaryOptionalInitial229 (registry declaration)
open GeneralDictionaryJournalRefinement228Source (root modelHigh)
open GeneralRebaseCompoundPublic273 (Fixed)
open GeneralRebaseTerminalRows274 (terminal_leaf_exact terminal_public)
open GeneralRebaseCompoundRows273 (Agrees)

theorem agreement_exact (m outer : Assignment) :
    Keeps (initialNames 4) m outer ↔ Agrees m outer := by
  unfold Keeps Agrees GeneralNominalCenteredFrame179.Agree initialNames
  simp only [List.mem_range]
  exact and_congr ⟨fun h id small => h id (by omega),fun h id small => h id (by omega)⟩ Iff.rfl

theorem projected_original (data : Payload) (outer : Assignment) :
    Projection (initialNames 4) (Joint installed registry root data) outer ↔
      Fixed outer ∧ data = .node declaration.id [] := by
  constructor
  · rintro ⟨m,agree,held,ev⟩
    have publicHeld := (terminal_public outer).mp ⟨m,(agreement_exact m outer).mp agree,held⟩
    exact ⟨publicHeld,GeneralRebaseTerminalEvidence278.leaf_shape
      (d := declaration) rfl rfl ev⟩
  · rintro ⟨valid,rfl⟩
    obtain ⟨m,agree,held,ev⟩ := (terminal_leaf_exact outer).mpr valid
    exact ⟨m,(agreement_exact m outer).mpr agree,held,ev⟩

theorem seed_exact : (GeneralRebaseMixedOwnedTrace277.raw installed).seed = 4 := rfl

theorem compiled_terminal (data : Payload) (outer : Assignment) :
    Projection (initialNames 4) (fun m => View installed registry root data m ∧ Respects (live installed) m) outer ↔
      Fixed outer ∧ data = .node declaration.id [] := by
  have exact := initial_projection GeneralRebaseTerminalMixedRefresh274.mixed_reachable registry root data outer
  rw [seed_exact] at exact
  exact exact.trans (projected_original data outer)

theorem rejects_uncommitted (data : Payload) :
    ¬ Projection (initialNames 4) (fun m => View installed registry root data m ∧ Respects (live installed) m) modelHigh := by
  intro purported
  have fixed := ((compiled_terminal data modelHigh).mp purported).1
  have value := fixed 4 (by decide)
  rw [GeneralDictionaryJournalRefinement228Source.high_value] at value
  exact GeneralDictionaryOptionalOutput229.not_width ⟨value.2,value.1⟩

end Yulang.GeneralRebaseOptionalView282
