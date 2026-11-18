import Yulang.GeneralDefaultRebaseRun260
namespace Yulang.GeneralDefaultRebaseCompletion260
open GeneralDictionaryDefaultGap206Source
open GeneralDictionaryVersionedGap206233 (current)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

def identity (name : Nat) : Core.PresenceGeneration.CompTerm Nat := ⟨.var name,.var name⟩
def view := GeneralNominalRebaseRawView243.compile snapshot identity

theorem models_exact (assignment : Assignment) : view.Models assignment ↔ GeneralNominalState.Models snapshot assignment :=
 GeneralNominalRebaseRawView243.compile_exact snapshot identity assignment

theorem unused_output : 0 ∉ GeneralNominalActiveSupport258.support view := by decide

theorem source_iff (first last : Assignment)
 (rows : ∀ name, (first name).2 = (last name).2)
 (types : ∀ name, name ≠ 0 → (first name).1 = (last name).1) :
 GeneralNominalState.Models snapshot first ↔ GeneralNominalState.Models snapshot last := by
 rw [← models_exact first,← models_exact last]
 exact GeneralNominalActiveSupport258.models_iff view first last rows
   (fun name present => types name (by intro same; subst name; exact unused_output present))

def complete (assignment : Assignment) : Assignment :=
 GeneralPresenceOrderedBlock247.put CommonNominalFullCarrier.model assignment 0 (assignment 1).1

theorem rows (assignment : Assignment) (name : Nat) : (complete assignment name).2 = (assignment name).2 :=
 GeneralPresenceOrderedBlock247.put_rows ..

theorem outside (assignment : Assignment) (name : Nat) (different : name ≠ 0) : complete assignment name = assignment name :=
 GeneralPresenceOrderedBlock247.put_outside _ _ _ _ name (Ne.symm different)

theorem source_exact (assignment : Assignment) :
 GeneralNominalState.Models snapshot (complete assignment) ↔ GeneralNominalState.Models snapshot assignment :=
 source_iff _ _ (rows assignment) (fun name different => congrArg Prod.fst (outside assignment name different))

theorem classes (assignment : Assignment) :
 GeneralNominalVersionedEffects231.ClassEffects current.core root plan (complete assignment) := by
 apply (GeneralDefaultRebaseBody260.classes_exact _).mpr
 rw [outside assignment 1 (by decide)]
 change Equivalent (GeneralPresenceOrderedBlock247.put CommonNominalFullCarrier.model assignment 0 (assignment 1).1 0).1 (assignment 1).1
 simp only [GeneralPresenceOrderedBlock247.put,ite_true]
 exact ⟨subtype_refl _,subtype_refl _⟩

theorem final (assignment : Assignment) (source : GeneralNominalState.Models snapshot assignment) :
 GeneralDefaultRebaseModels260.Models GeneralDefaultRebaseSource260.finalState (complete assignment) :=
 (GeneralDefaultRebaseModels260.final_exact _).mpr
   ⟨(GeneralDefaultRebaseBody260.current_source _).mpr ((source_exact assignment).mpr source),classes assignment⟩
end Yulang.GeneralDefaultRebaseCompletion260
