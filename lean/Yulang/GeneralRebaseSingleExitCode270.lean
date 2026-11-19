import Yulang.GeneralRebaseRankOne269

namespace Yulang.GeneralRebaseSingleExitCode270
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State)
open GeneralSourceState (Output)
open GeneralRebaseStep258 (Fact)
open GeneralRebaseCompression266 (Basis)
open GeneralRebaseLiveProjection264 (project)
open GeneralRebaseWeakProgress268 (Weak)
open GeneralRebaseBehavior269 (sourceBasis code)
open GeneralRebaseRankOne269 (zero_code)
open FiniteRankBehavior269 (Code catalogue)
open FiniteBehaviorClassifier269 (classify)
open GeneralRebaseFiniteSlices268 (slices)

def isEmptyLeaf (c : Code (List Fact)) : Bool := c.label.isEmpty && c.children.isEmpty

theorem isEmptyLeaf_exact (c : Code (List Fact)) : isEmptyLeaf c = true ↔ c = .node [] [] := by
 cases c with
 | node label kids =>
   simp [isEmptyLeaf,Code.label,Code.children,Bool.and_eq_true,List.isEmpty_iff]

def compile (basis current : List Fact) : Code (List Fact) :=
 .node current ((catalogue (slices basis) (current.length - 1)).filter isEmptyLeaf)

/-- Complete executable code when some real weak exit exists and every
weak exit exhausts the fixed basis. One witness alone is not the coverage
proof, and the theorem does not assume finite concrete stutter branching. -/
theorem exact_code (registry : Registry) (root : Occurrence roles) (owners : List Nat) (pool : List Output)
 (source : State roles) (existsExit : ∃ after, Weak registry root owners pool source after)
 (allEmpty : ∀ after, Weak registry root owners pool source after → (project owners pool after).remaining = []) :
 code registry root owners pool source = compile (Basis owners pool) (project owners pool source).remaining := by
 classical
 let b := sourceBasis registry root owners pool
 change classify b source = _
 rw [classify.eq_1 b source]
 apply congrArg (Code.node (project owners pool source).remaining)
 apply List.filter_congr
 intro candidate _
 rw [Bool.eq_iff_iff,decide_eq_true_eq,isEmptyLeaf_exact]
 constructor
 · rintro ⟨next,same⟩
   exact same.symm.trans (zero_code registry root owners pool next.val (allEmpty next.val next.property))
 · intro empty
   obtain ⟨next,step⟩ := existsExit
   exact ⟨⟨next,step⟩,(zero_code registry root owners pool next (allEmpty next step)).trans empty.symm⟩

end Yulang.GeneralRebaseSingleExitCode270
