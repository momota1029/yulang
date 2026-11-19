import Yulang.GeneralRebaseTreeSchema272
import Yulang.GeneralRebaseTreeCoverage272
import Yulang.GeneralRebaseInstalledOutputCycles271
import Yulang.GeneralDictionaryOptionalExpression229

set_option maxRecDepth 25000
set_option maxHeartbeats 2400000
namespace Yulang.GeneralRebaseTreeSchemaActual252272
open CommonNominalFullCarrier
open GeneralNominalRecursiveInspection (Origin)
open GeneralNominalVersionedCycles232 (Cyclic)
open GeneralDictionaryOutputDepth252 (model)
open GeneralDictionaryOutputDepthInstall252 (installed installed_model)
open GeneralRebaseFiniteTree272 (Tree Canonical value scalar)
open GeneralRebaseTreeConstructors272 (nominalTree nominal_tree_canonical scalar_canonical)
open GeneralRebaseTreeInterpreter272 (Certified run inspect)
open GeneralRebaseTreeSchema272 (rounds rounds_sound)

def input : Tree := nominalTree 0 [scalar .int]

theorem input_checked : Canonical input :=
 nominal_tree_canonical 0 _ (by intro x member; cases List.mem_singleton.mp member; exact scalar_canonical _)

def seed : Nat → Option Tree
 | 2 => some input
 | _ => none

theorem seed_certified : Certified model seed := by
 intro id tree hit
 unfold seed at hit
 split at hit
 · cases Option.some.inj hit
   exact ⟨input_checked,subtype_refl _,subtype_refl _⟩
 · contradiction

def output : Tree := nominalTree 0 [nominalTree 0 [input]]

noncomputable def derived : Nat → Option Tree := rounds installed 1 seed

theorem output_not_seeded : seed 3 = none := rfl

theorem output_from_actual_schema : derived 3 = some output := by
 let actualPlan := GeneralDictionaryOutputDepth252.plan
 change GeneralRebaseTreeSchema272.enrich seed actualPlan 3 = _
 have fromBinder : GeneralRebaseTreeSchema272.environment actualPlan seed .actual 0 = some input := by
   change seed (GeneralNominalVersionedFrame231.binder GeneralDictionaryOutputDepth252.plan 0) = _
   rw [GeneralDictionaryOutputDepth252.binder_exact]
   rfl
 unfold GeneralRebaseTreeSchema272.enrich GeneralRebaseTreeSchema272.compute
 change (none : Option Tree).or ((GeneralNominalVersionedPlans231.emittedSchema GeneralDictionaryOutputDepth252.plan).equations.findSome? _) = _
 rw [GeneralDictionaryOutputDepth252.emitted_exact]
 simp [GeneralRebaseTreeSchema272.entry,GeneralDictionaryOutputDepth252.rhs,
   GeneralRebaseTreeExprCompile272.compile,GeneralRebaseTreeExprCompile272.many,fromBinder,output,
   Bind.bind,Option.bind,Option.or]

theorem witness_checked : Certified model derived := rounds_sound installed model installed_model 1 seed seed_certified

theorem at_output : Canonical output ∧ Equivalent (model 3).1 (value output) :=
 witness_checked 3 output output_from_actual_schema

def three_selects : Origin := .nominal (.nominal (.nominal (.source 3) 0 0) 0 0) 0 0

theorem computed_last : run derived three_selects = .found (scalar .int) := by
 simp only [three_selects,run,output_from_actual_schema]
 rfl

theorem actual_no_recursion (o : Origin) (root : GeneralRebaseTreeCoverage272.rootSource o = 3) :
 ¬ Cyclic installed o := by
 have known := GeneralRebaseTreeInterpreter272.inspect_sound installed model installed_model derived witness_checked o
 rw [GeneralRebaseTreeCoverage272.returns_negative derived o ⟨output,by rw [root]; exact output_from_actual_schema⟩] at known
 exact known

/-- This is the existing actual optional-output expression, not a toy:
the finite grammar must not silently replace its union with either branch. -/
theorem optional_abstains :
 GeneralRebaseTreeExprCompile272.compile (fun _ _ => none) .actual GeneralDictionaryOptionalExpression229.expression = none := rfl

end Yulang.GeneralRebaseTreeSchemaActual252272
