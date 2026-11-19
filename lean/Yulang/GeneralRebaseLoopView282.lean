import Yulang.GeneralRebaseWholeRow282
import Yulang.GeneralRebaseLoopConstant282
import Yulang.GeneralRebaseVersionEvidence278
import Yulang.GeneralRebaseLooseEvidence278

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29000
set_option maxHeartbeats 11000000
namespace Yulang.GeneralRebaseLoopView282
open GeneralRebaseWholeRow282 (Keeps Projection initialNames initial_projection)
open GeneralRebaseWholeJournal282 (View)
open GeneralRebasePrivateStore282 (Joint)
open GeneralRebaseTermCopy281 (Respects)
open GeneralRebaseLiveStore282 (live)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)

namespace Version
open GeneralDictionaryVersionLoopSource237 (snapshot root registry)
open GeneralDictionaryVersionLoopIteration239 (state stages)
open GeneralRebaseVersionMicro278 (exact_public)
open GeneralVersionBoundaryCompletion259 (Agree agrees complete)
open GeneralRebaseVersionEvidence278 (enter_exact same_witness_leaves)
open GeneralRebaseLoopBase282.Version (decode_reach)
open GeneralRebaseLoopConstant282.Version (simple constant_exact)

theorem agreement_exact (a b : Assignment) : Keeps (initialNames 3) a b ↔ Agree a b := by
  unfold Keeps Agree GeneralNominalCenteredFrame179.Agree initialNames
  simp only [List.mem_range]
  exact and_congr ⟨fun h i bound => h i (by omega),fun h i bound => h i (by omega)⟩ Iff.rfl

theorem projected_original (n : Nat) (data : Payload) (outer : Assignment) :
    Projection (initialNames 3) (Joint (state n) registry root data) outer ↔
    GeneralNominalState.Models snapshot outer ∧ data = .node 0 [] := by
  constructor
  · rintro ⟨m,keeps,valid,ev⟩
    exact ⟨(exact_public ⟨n,.enter⟩ outer).mp ⟨m,(agreement_exact m outer).mp keeps,valid⟩,
      ((enter_exact n m data).mp ev).1⟩
  · rintro ⟨source,rfl⟩
    exact ⟨complete outer,(agreement_exact _ _).mpr (agrees outer),
      GeneralRebaseVersionMicro278.complete_all ⟨n,.enter⟩ outer source,
      (same_witness_leaves outer source n).1⟩

theorem seed_exact (n : Nat) : (GeneralRebaseMixedOwnedTrace277.raw (state n)).seed = 3 := by
  change (state n).core.erased.current.context.state.seed = _
  rw [(stages n).shape.current]

theorem projected_constant (n : Nat) (data : Payload) (outer : Assignment) :
    Projection (initialNames 3) (fun m =>
      View (state (n+1)) registry root data m ∧ Respects simple m) outer ↔
    GeneralNominalState.Models snapshot outer ∧ data = .node 0 [] := by
  have norm := initial_projection (decode_reach (n+1)) registry root data outer
  rw [seed_exact] at norm
  have old := norm.trans (projected_original (n+1) data outer)
  constructor
  · rintro ⟨m,agree,view,fixed⟩
    exact old.mp ⟨m,agree,view,(constant_exact n m).mpr fixed⟩
  · intro live
    obtain ⟨m,agree,view,table⟩ := old.mpr live
    exact ⟨m,agree,view,(constant_exact n m).mp table⟩

end Version

namespace Loose
open GeneralDictionaryLooseLoopSource240 (snapshot root registry)
open GeneralDictionaryLooseIterationIteration240 (state stages)
open GeneralRebaseLooseMicro278 (exact_public)
open GeneralDictionaryInitialProjection257 (Agree)
open GeneralDictionaryInitialFill258 (public_agrees complete)
open GeneralRebaseLooseEvidence278 (enter_exact same_witness_leaves)
open GeneralRebaseLoopBase282.Loose (decode_reach)
open GeneralRebaseLoopConstant282.Loose (simple constant_exact)

theorem agreement_exact (a b : Assignment) : Keeps (initialNames 4) a b ↔ Agree a b := by
  unfold Keeps GeneralDictionaryInitialProjection257.Agree GeneralNominalCenteredFrame179.Agree initialNames
  simp only [List.mem_range]
  exact and_congr ⟨fun h i bound => h i (by omega),fun h i bound => h i (by omega)⟩ Iff.rfl

theorem projected_original (n : Nat) (data : Payload) (outer : Assignment) :
    Projection (initialNames 4) (Joint (state n) registry root data) outer ↔
    GeneralNominalState.Models snapshot outer ∧ data = .node 0 [] := by
  constructor
  · rintro ⟨m,keeps,valid,ev⟩
    exact ⟨(exact_public ⟨n,.enter⟩ outer).mp ⟨m,(agreement_exact m outer).mp keeps,valid⟩,
      ((enter_exact n m data).mp ev).1⟩
  · rintro ⟨source,rfl⟩
    exact ⟨complete outer,(agreement_exact _ _).mpr (public_agrees outer),
      GeneralRebaseLooseMicro278.complete_all ⟨n,.enter⟩ outer source,
      (same_witness_leaves outer source n).1⟩

theorem seed_exact (n : Nat) : (GeneralRebaseMixedOwnedTrace277.raw (state n)).seed = 4 := by
  change (state n).core.erased.current.context.state.seed = _
  rw [(stages n).shape.current]

theorem projected_constant (n : Nat) (data : Payload) (outer : Assignment) :
    Projection (initialNames 4) (fun m =>
      View (state (n+1)) registry root data m ∧ Respects simple m) outer ↔
    GeneralNominalState.Models snapshot outer ∧ data = .node 0 [] := by
  have norm := initial_projection (decode_reach (n+1)) registry root data outer
  rw [seed_exact] at norm
  have old := norm.trans (projected_original (n+1) data outer)
  constructor
  · rintro ⟨m,agree,view,fixed⟩
    exact old.mp ⟨m,agree,view,(constant_exact n m).mpr fixed⟩
  · intro live
    obtain ⟨m,agree,view,table⟩ := old.mpr live
    exact ⟨m,agree,view,(constant_exact n m).mp table⟩

end Loose

end Yulang.GeneralRebaseLoopView282
