import Yulang.GeneralRebaseFiniteTreeCompare272
import Yulang.GeneralRebaseTreeLeastClosure272
import Yulang.GeneralRebaseTreeSchemaActual252272

namespace Yulang.GeneralRebaseUniformTree272
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedCycles232 (Equal)
open GeneralNominalRecursiveInspection (Origin)
open GeneralRebaseTreeInterpreter272 (Source Certified)
open GeneralRebaseTreeSchema272 (rounds rounds_sound)
open GeneralRebaseTreeSchemaClosure272 (close close_sound)
open GeneralRebaseFiniteTreeCompare272 (modelLookup local_sound)
open GeneralRebasePartialBool268 (Answer Reflect)
open CommonNominalFullCarrier

def Uniform (state : State roles) (src : Source) : Prop :=
 ∀ m, Models state m → Certified m src

theorem rounds_uniform (state : State roles) (seed : Source) (cert : Uniform state seed) (n : Nat) :
 Uniform state (rounds state n seed) :=
 fun m holds => rounds_sound state m holds n seed (cert m holds)

theorem close_uniform (state : State roles) (seed : Source) (cert : Uniform state seed) :
 Uniform state (close state seed) :=
 fun m holds => close_sound state m holds seed (cert m holds)

theorem equal_sound (state : State roles) (seed : Source) (cert : Uniform state seed)
 (model : ∃ m, Models state m) (a b : Origin) :
 Reflect (Equal state a b) (modelLookup seed a b) := by
 cases computed : modelLookup seed a b with
 | none => trivial
 | some yes =>
   cases yes with
   | false =>
     obtain ⟨m,valid⟩ := model
     have witness := local_sound m seed (cert m valid) a b
     rw [computed] at witness
     exact fun h => witness (h m valid)
   | true =>
     intro m valid
     have one := local_sound m seed (cert m valid) a b
     rw [computed] at one
     exact one

namespace Actual252
open GeneralDictionaryOutputDepth252 (plan)
open GeneralDictionaryOutputDepthInstall252 (installed installed_model)
open GeneralRebaseTreeSchemaActual252272 (seed input derived output output_from_actual_schema input_checked)
open GeneralRebaseTreeInterpreter272 (run)
open GeneralRebaseFiniteTree272 (value)

theorem seed_uniform : Uniform installed seed := by
 intro m valid id tree hit
 unfold seed at hit
 split at hit
 · cases Option.some.inj hit
   exact ⟨input_checked,GeneralDictionaryOutputDepth252.foo_fixed m (valid.2.1 plan List.mem_cons_self).1⟩
 · contradiction

theorem derived_uniform : Uniform installed derived :=
 rounds_uniform installed seed seed_uniform 1

def backToInput : Origin := .nominal (.nominal (.source 3) 0 0) 0 0

theorem checked_selection : run derived backToInput = .found input := by
 simp only [backToInput,run,output_from_actual_schema]
 rfl

theorem checked_source : run derived (.source 2) = .found input := by
 have before : seed 2 = some input := rfl
 have preserves := GeneralRebaseTreeSchemaClosure272.preserves installed 1 seed 2 input before
 simp only [run,derived,preserves]

theorem computed_equal : modelLookup derived backToInput (.source 2) = some true := by
 unfold modelLookup
 rw [checked_selection,checked_source]
 change some (GeneralRebaseFiniteTreeCode272.same input input) = some true
 rw [(GeneralRebaseFiniteTreeCode272.same_exact input input).mpr rfl]

theorem actual_equal : Equal installed backToInput (.source 2) := by
 have cert := equal_sound installed derived derived_uniform
   ⟨GeneralDictionaryOutputDepth252.model,installed_model⟩ backToInput (.source 2)
 rw [computed_equal] at cert
 exact cert

end Actual252
end Yulang.GeneralRebaseUniformTree272
