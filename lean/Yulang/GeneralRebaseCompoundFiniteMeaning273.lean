import Yulang.GeneralRebaseCompoundSourceTypes273
import Yulang.GeneralRebaseSourceStepDriver270
import Yulang.GeneralDictionaryCompoundPoint238

set_option maxRecDepth 16000
set_option maxHeartbeats 2700000
namespace Yulang.GeneralRebaseCompoundFiniteMeaning273
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseCompoundSourceTypes273 (PublicSource Body before_exact restricted_exact source_depends_on_types)
open GeneralRebaseCompoundPublic273 (AgreesTypes)
open GeneralRebaseStep258 (Fact State initial done present)
open GeneralRebaseFactSemantics259 (Models initial_exact done_exact)
open GeneralRebaseSourceStrictFixture265 (owners owner pool output)
open GeneralRebaseCompression266 (Basis)
open GeneralRebaseLiveProjection264 (project)
open GeneralDictionaryCompoundFrame238 (before installed)
open GeneralDictionaryCompoundPoint238 (point)
open GeneralRebaseSourceStepDriver270 (next)
open GeneralRebaseSourceStepDriver270.Compound (computed_initial matches_concrete)

abbrev support := Basis owners pool
def bodyFact : Fact := GeneralRebaseUniversalBasis263.bodyKey owner output
def pairFact : Fact := GeneralRebaseOneOutputFacts270.pairKey owner output

theorem distinct : bodyFact ≠ pairFact := by decide +kernel

theorem named_basis : support = [bodyFact,pairFact] := by decide +kernel

def factHolds (m : Assignment) (f : Fact) : Prop :=
 if f = bodyFact then Body m
 else f = pairFact ∧ CommonNominalFullCarrier.Equivalent (m 4).1 (m 4).1

def Meaning (s : State support) (m : Assignment) : Prop :=
 Models PublicSource factHolds s m

/-- The synchronized pair marker is reflexive, not a second independent
model witness. The strict body fact retains the actual optional-field type. -/
theorem finished_exact (m : Assignment) :
 Meaning (done support) m ↔ PublicSource m ∧ Body m := by
 rw [Meaning,done_exact]
 constructor
 · rintro ⟨source,holds⟩
   have body := holds bodyFact (by rw [named_basis]; exact List.mem_cons_self)
   exact ⟨source,by simpa only [factHolds,reduceCtorEq,ite_true] using body⟩
 · rintro ⟨source,body⟩
   refine ⟨source,?_⟩
   intro fact h
   rw [named_basis] at h
   rcases List.mem_cons.mp h with rfl | only
   · simpa only [factHolds,reduceCtorEq,ite_true] using body
   · cases List.mem_singleton.mp only
     change (if pairFact = bodyFact then Body m else _)
     simp only [Ne.symm distinct,ite_false]
     exact ⟨True.intro,CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩

theorem original_before_public (boundary : Assignment) :
 (∃ old, AgreesTypes old boundary ∧ GeneralNominalVersionedJournal232.Models before old) ↔
 Meaning (project owners pool before) boundary := by
 rw [computed_initial,Meaning,initial_exact]
 constructor
 · rintro ⟨old,agree,valid⟩
   exact (source_depends_on_types old boundary agree).mp ((before_exact old).mp valid)
 · intro checked
   exact ⟨boundary,fun _ _ => rfl,(before_exact _).mpr checked⟩

theorem original_installed_public (boundary : Assignment) :
 (∃ old, AgreesTypes old boundary ∧ GeneralNominalVersionedJournal232.Models installed old) ↔
 Meaning (project owners pool installed) boundary := by
 have full := GeneralRebaseCompoundProjection270.all_weak_targets installed
   GeneralRebaseCompoundProjection270.some_weak_target
 have doneEq : project owners pool installed = done support := GeneralRebaseStep258.state_ext _ _ full
 rw [doneEq,finished_exact,← restricted_exact]
 exact GeneralRebaseCompoundPublic273.public_exact boundary

theorem point_uses_same_meaning (boundary : Assignment) :
 (∃ old, AgreesTypes old boundary ∧ GeneralNominalVersionedJournal232.Models point old) ↔
 Meaning (project owners pool installed) boundary := by
 simp only [GeneralDictionaryCompoundPoint238.models_iff]
 exact original_installed_public boundary

theorem executable_public_step (boundary : Assignment) :
 ∃ finish, next support (project owners pool before) = some finish ∧
  (Meaning finish boundary ↔ ∃ old, AgreesTypes old boundary ∧ GeneralNominalVersionedJournal232.Models installed old) :=
 ⟨project owners pool installed,matches_concrete,(original_installed_public boundary).symm⟩

end Yulang.GeneralRebaseCompoundFiniteMeaning273
