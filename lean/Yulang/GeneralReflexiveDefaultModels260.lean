import Yulang.GeneralReflexiveDefaultSource260
namespace Yulang.GeneralReflexiveDefaultModels260
open GeneralRebaseStep258
open GeneralDictionaryAllocDefaultSource202
open GeneralDictionaryVersionedDefault202233 (current)
open GeneralReflexiveDefaultSource260 (facts initialState finalState body schema)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

def factHolds (assignment : Assignment) : Fact → Prop
 | .installed owner => owner = 37
 | .binder index => GeneralRebaseOwnedOutputKeys260.Holds 37 schema
     (GeneralNominalVersionedEffects231.bodyVariables plan assignment body) assignment (.binder index)
 | _ => False

def Models := GeneralRebaseFactSemantics259.Models (basis := facts)
 (GeneralNominalVersionedJournal232.Models current) factHolds

theorem output_meaning (assignment : Assignment) : factHolds assignment (.binder 1408) := by
 have all := GeneralRebaseOwnedOutputKeys260.all_exact 37 schema
   (GeneralNominalVersionedEffects231.bodyVariables plan assignment body) assignment
 rw [GeneralReflexiveDefaultSource260.output_keys] at all
 simp only [List.mem_singleton,forall_eq] at all
 exact all.mpr ((GeneralReflexiveDefaultSource260.body_meaning assignment).mpr ⟨subtype_refl _,subtype_refl _⟩)

theorem all_facts (assignment : Assignment) : ∀ fact ∈ facts, factHolds assignment fact := by
 intro fact member
 rcases List.mem_cons.mp member with rfl | last
 · rfl
 · cases List.mem_singleton.mp last
   exact output_meaning assignment

/-- Every finite subset has exactly the original model set in this reflexive
source. No assignment completion or public-output release is needed. -/
theorem models_exact (state : State facts) (assignment : Assignment) : Models state assignment ↔
 GeneralNominalVersionedJournal232.Models current assignment := by
 constructor
 · exact And.left
 · intro source
   exact ⟨source,fun fact member => all_facts assignment fact (List.mem_filter.mp member).1⟩

theorem same_assignment (first last : State facts) (assignment : Assignment) :
 Models first assignment ↔ Models last assignment :=
 (models_exact first assignment).trans (models_exact last assignment).symm

theorem evidence (state : State facts) (assignment : Assignment) (valid : Models state assignment) :
 GeneralNominalVersionedEvidence231.Evidence registry current.core assignment root (.node 37 []) :=
 GeneralDictionaryVersionedDefault202233.evidence assignment ((models_exact state assignment).mp valid)
end Yulang.GeneralReflexiveDefaultModels260
