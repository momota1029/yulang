import Yulang.GeneralRebaseNamedRequest260
namespace Yulang.GeneralRebaseEqualOutputs260
open GeneralNominalCenteredHeadMatSchemas
open GeneralNominalCommonBridge (Assignment)
open GeneralSourceState (Output)

/-- All ordered same-name request pairs at one fixed observation. -/
def schema (outputs : List Output) : Schema :=
 ⟨outputs.flatMap (fun first =>
   (outputs.filter fun last => first.name == last.name).map fun last =>
     ⟨first.target,.actual,.variable last.target⟩),false⟩

def variables (assignment : Assignment) (_ : GeneralNominalMaterialization.Mode) (name : Nat) := (assignment name).1

theorem holds_exact (outputs : List Output) (assignment : Assignment) :
 (schema outputs).Holds (variables assignment) assignment ↔
 ∀ first ∈ outputs, ∀ last ∈ outputs, first.name = last.name →
 CommonNominalFullCarrier.Equivalent (assignment first.target).1 (assignment last.target).1 := by
 constructor
 · intro valid first one last two names
   have member : (⟨first.target,.actual,.variable last.target⟩ : Equation) ∈ (schema outputs).equations := by
     apply List.mem_flatMap.mpr
     refine ⟨first,one,List.mem_map.mpr ⟨last,?_,rfl⟩⟩
     exact List.mem_filter.mpr ⟨two,by simpa using names⟩
   exact valid _ member
 · intro valid equation member
   obtain ⟨first,one,within⟩ := List.mem_flatMap.mp member
   obtain ⟨last,two,rfl⟩ := List.mem_map.mp within
   obtain ⟨present,names⟩ := List.mem_filter.mp two
   exact valid first one last present (by simpa using names)

theorem translated (outputs : List Output) : (schema outputs).unknown = false := rfl

/-- The actual alias-class request list is noncomputable here. This is a
fixed-state semantic table, not an executable global source compiler. -/
noncomputable def actual (state : GeneralNominalCenteredSteps.State roles) (root : GeneralSourceDictionaries.Occurrence roles) :=
 schema (GeneralNominalCenteredHeadOutputs.requests state root)

theorem actual_exact (state : GeneralNominalCenteredSteps.State roles) (root : GeneralSourceDictionaries.Occurrence roles)
 (assignment : Assignment) :
 (actual state root).Holds (variables assignment) assignment ↔
 GeneralNominalCenteredHeadOutputs.EqualOutputs state root assignment := holds_exact ..

theorem class_effects (state : GeneralNominalCenteredSteps.State roles) (root : GeneralSourceDictionaries.Occurrence roles)
 (plan : GeneralNominalCenters.Plan roles) (assignment : Assignment) :
 GeneralNominalVersionedEffects231.ClassEffects state root plan assignment ↔
 (∀ output ∈ GeneralNominalCenteredHeadOutputs.requests state root, ∀ body,
  GeneralDictionaryAssociatedProvenance.lookup roles plan.packet.declaration output.name = some body →
  GeneralNominalVersionedEffects231.BodyHolds plan output.target assignment body) ∧
 (actual state root).Holds (variables assignment) assignment := by
 unfold GeneralNominalVersionedEffects231.ClassEffects
 rw [actual_exact]
end Yulang.GeneralRebaseEqualOutputs260
