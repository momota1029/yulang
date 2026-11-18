import Yulang.GeneralDictionaryOutputInputs258
import Yulang.GeneralNominalActiveSupport258
namespace Yulang.GeneralDictionaryOutputFrame258
open GeneralDictionaryOutputDepth252
open GeneralNominalCommonBridge (Assignment)
open Core.PresenceGeneration
open CommonNominalFullCarrier

def identity (name : Nat) : CompTerm Nat := ⟨.var name,.var name⟩
def view := GeneralNominalRebaseRawView243.compile snapshot identity

theorem models_exact (assignment : Assignment) :
 view.Models assignment ↔ GeneralNominalState.Models snapshot assignment :=
 GeneralNominalRebaseRawView243.compile_exact snapshot identity assignment

theorem support_small (name : Nat) (present : name ∈ GeneralNominalActiveSupport258.support view) : name ≤ 2 := by
 have bound : ∀ name ∈ GeneralNominalActiveSupport258.support view, name ≤ 2 := by decide
 exact bound name present

theorem unused_output : 3 ∉ GeneralNominalActiveSupport258.support view := by
 intro present
 have bound := support_small 3 present
 omega

theorem source_iff (first last : Assignment)
 (rows : ∀ name, (first name).2 = (last name).2)
 (types : ∀ name, name ≤ 2 → (first name).1 = (last name).1) :
 GeneralNominalState.Models snapshot first ↔ GeneralNominalState.Models snapshot last := by
 rw [← models_exact first,← models_exact last]
 exact GeneralNominalActiveSupport258.models_iff view first last rows
   (fun name present => types name (support_small name present))

def complete (assignment : Assignment) : Assignment :=
 GeneralPresenceOrderedBlock247.put CommonNominalFullCarrier.model assignment 3
   (nominal 0 [.inl (nominal 0 [.inl (assignment 2).1])])

theorem rows (assignment : Assignment) (name : Nat) : (complete assignment name).2 = (assignment name).2 :=
 GeneralPresenceOrderedBlock247.put_rows ..

theorem outside (assignment : Assignment) (name : Nat) (different : name ≠ 3) : complete assignment name = assignment name :=
 GeneralPresenceOrderedBlock247.put_outside _ _ _ _ name (Ne.symm different)

theorem source_exact (assignment : Assignment) :
 GeneralNominalState.Models snapshot (complete assignment) ↔ GeneralNominalState.Models snapshot assignment :=
 source_iff _ _ (rows assignment) (fun name small => congrArg Prod.fst (outside assignment name (by omega)))
end Yulang.GeneralDictionaryOutputFrame258
