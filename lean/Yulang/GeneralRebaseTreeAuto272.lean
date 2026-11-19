import Yulang.GeneralRebaseTreeSeedExtract272
import Yulang.GeneralRebaseTreeRecordFixture272

namespace Yulang.GeneralRebaseTreeAuto272
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedCycles232 (Cyclic Equal)
open GeneralNominalRecursiveInspection (Origin)
open GeneralRebaseTreeInterpreter272 (Source inspect inspect_sound)
open GeneralRebaseTreeSeedExtract272 (seed seed_uniform)
open GeneralRebaseTreeSchemaClosure272 (close close_stable Stable)
open GeneralRebaseUniformTree272 (Uniform close_uniform equal_sound)
open GeneralRebasePartialBool268 (Answer Reflect)

def source (state : State roles) (depth : Nat) : Source := close state (seed state depth)

theorem source_uniform (state : State roles) (depth : Nat) : Uniform state (source state depth) :=
 close_uniform state _ (seed_uniform state depth)

theorem source_stable (state : State roles) (depth : Nat) : Stable state (source state depth) :=
 close_stable state _

def check (state : State roles) (depth : Nat) (o : Origin) : Answer :=
 inspect (source state depth) o

theorem check_sound (state : State roles) (m : GeneralNominalCommonBridge.Assignment) (valid : Models state m)
 (depth : Nat) (o : Origin) : Reflect (Cyclic state o) (check state depth o) :=
 inspect_sound state m valid _ (source_uniform state depth m valid) o

theorem check_equality (state : State roles) (full : ∃ m, Models state m) (depth : Nat) (a b : Origin) :
 Reflect (Equal state a b) (GeneralRebaseFiniteTreeCompare272.modelLookup (source state depth) a b) :=
 equal_sound state _ (source_uniform state depth) full a b

namespace Actual252
open GeneralDictionaryOutputDepthInstall252 (installed installed_model)
open GeneralDictionaryOutputDepth252 (model)
open GeneralRebaseUniformTree272.Actual252 (backToInput)

noncomputable def derived := source installed 2

theorem input_learned : (seed installed 2 2).isSome = true := by decide +kernel

theorem output_not_seeded : (seed installed 2 3).isSome = false := by decide +kernel

theorem output_derived : (derived 3).isSome = true := by decide +kernel

theorem checked : GeneralRebaseFiniteTreeCompare272.modelLookup derived backToInput (.source 2) = some true := by
 decide +kernel

theorem automated_equal : Equal installed backToInput (.source 2) := by
 have proof := check_equality installed ⟨model,installed_model⟩ 2 backToInput (.source 2)
 change Reflect _ (GeneralRebaseFiniteTreeCompare272.modelLookup derived backToInput (.source 2)) at proof
 rw [checked] at proof
 exact proof

end Actual252

namespace Branching
open GeneralRebaseRecordAcyclicFixture271 (journal model full_model)

theorem all_tree : (seed journal 3 0).isSome = true := by decide +kernel

theorem fuel_failure : (seed journal 2 0).isSome = false := by decide +kernel

theorem auto_acyclic : check journal 3 (.source 0) = some false := by decide +kernel

theorem proved : ¬ Cyclic journal (.source 0) := by
 have proof := check_sound journal model full_model 3 (.source 0)
 rw [auto_acyclic] at proof
 exact proof

end Branching
end Yulang.GeneralRebaseTreeAuto272
