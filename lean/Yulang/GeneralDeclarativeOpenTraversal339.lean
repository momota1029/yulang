import Yulang.GeneralDeclarativeOpenExec339
import Yulang.GeneralDeclarativeCompoundInputs338

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeOpenTraversal339
open GeneralDeclarativeCompoundTree338 (World Span Tree Forest fitsModel footprint scope advance advance_grows
  together identity tree_exact forest_exact)
open GeneralDeclarativeCompoundBatch338 (Ticket protectedNames)
open GeneralDeclarativeEndpointBatch336 (patch)
open GeneralDeclarativeOpenExec339 (values execute)
open GeneralNominalCommonBridge (Assignment)

def afterModel {w : World done} (t : Ticket w.source a f) (keep : List Nat) (m : Assignment) : Assignment :=
  patch w.state (protectedNames w.reads keep t.jobs) (values m t.jobs) m

inductive Run {done : Nat → Prop} (keep : List Nat) : World done → Assignment → World done → Assignment → Prop where
  | stay : Run keep w m w m
  | phase {w : World done} (t : Ticket w.source a f) :
      Run keep w m (advance w t keep) (afterModel t keep m)
  | chain : Run keep w m middle n → Run keep middle n v z → Run keep w m v z

def Realizes (keep : List Nat) (w v : World done) : Prop :=
  ∀ m, fitsModel w m → ∃ n, Run keep w m v n ∧ fitsModel v n ∧ ∀ x ∈ footprint w keep, n x = m x

theorem run_sound (run : Run keep w m v n) (fit : fitsModel w m) :
    w.Grows v ∧ fitsModel v n ∧ ∀ x ∈ footprint w keep, n x = m x := by
  induction run with
  | stay =>
    exact ⟨⟨GeneralDeclarativeClauseBatch327.reflexive _,fun _ h => h,
      GeneralDeclarativeClauseBatch327.reflexive _⟩,fit,fun _ _ => rfl⟩
  | phase ticket =>
    refine ⟨advance_grows ticket keep,?_⟩
    exact execute ticket _ fit keep
  | chain a b ai bi =>
    obtain ⟨old,mid,first⟩ := ai fit
    obtain ⟨current,last,preserved⟩ := bi mid
    exact ⟨together old current,last,fun x h => (preserved x (scope old h)).trans (first x h)⟩

theorem compose {w mid v : World done} (a : Realizes keep w mid) (b : Realizes keep mid v) :
    Realizes keep w v := by
  intro m fit
  obtain ⟨n,first,newFit,_⟩ := a m fit
  obtain ⟨z,last,_,_⟩ := b n newFit
  let total := Run.chain first last
  exact ⟨z,total,(run_sound total fit).2⟩

/-- Re-evaluate all record residual jobs of the existing normalized
traversal in their actual source models. The very same depth-first
capture list, authorized state, and sidecars remain valid. -/
theorem realize_tree (tree : Tree keep w a pat v uses) : Realizes keep w v := by
  refine Tree.rec (motive_1 := fun w _ _ v _ _ => Realizes keep w v)
    (motive_2 := fun w _ v _ _ => Realizes keep w v) ?_ ?_ ?_ ?_ tree
  · intros; exact fun m fit => ⟨m,.stay,fit,fun _ _ => rfl⟩
  · intros
    rename_i arg fields pat tail tasks rest middle body final tailUses world ticket
      nonempty cut dispatch forest tailProof runForest runTail
    have stageNative : Realizes keep world (advance world ticket keep) := by
      intro m fit
      exact ⟨_,.phase ticket,execute ticket m fit keep⟩
    exact compose stageNative (compose runForest runTail)
  · intros; exact fun m fit => ⟨m,.stay,fit,fun _ _ => rfl⟩
  · intros
    apply compose <;> assumption

end Yulang.GeneralDeclarativeOpenTraversal339
