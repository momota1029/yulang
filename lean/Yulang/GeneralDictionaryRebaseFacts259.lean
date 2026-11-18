import Yulang.GeneralRebaseFactSemantics259
namespace Yulang.GeneralDictionaryRebaseFacts259
open GeneralRebaseStep258
open GeneralDictionaryRebaseStep258 (facts initialState finalState)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryLooseLoopSource240 (snapshot)
open GeneralDictionaryLooseLoopPacket240 (actual)
open CommonNominalFullCarrier

def value (assignment : Assignment) (atom : Nat) : Ty :=
 if atom = 0 then (assignment 2).1 else (assignment 4).1

def factHolds (assignment : Assignment) : Fact → Prop
 | .lower owner atom => owner = 0 ∧ atom ≤ 1 ∧ Subtype (value assignment atom) (assignment actual).1
 | .upper owner atom => owner = 0 ∧ atom ≤ 1 ∧ Subtype (assignment actual).1 (value assignment atom)
 | .binder 0 => Subtype (assignment 2).1 (assignment actual).1
 | .binder 1 => Subtype (assignment actual).1 (assignment 2).1
 | .binder _ => False
 | .installed owner => owner = 0

def Models (state : State facts) (assignment : Assignment) : Prop :=
 GeneralRebaseFactSemantics259.Models (GeneralNominalState.Models snapshot) factHolds state assignment

theorem initial_exact (assignment : Assignment) : Models initialState assignment ↔ GeneralNominalState.Models snapshot assignment :=
 GeneralRebaseFactSemantics259.initial_exact ..

theorem final_exact (assignment : Assignment) : Models finalState assignment ↔
 GeneralNominalState.Models snapshot assignment ∧ GeneralDictionaryBinderFact257.Holds assignment := by
 rw [Models,GeneralRebaseFactSemantics259.done_exact]
 constructor
 · rintro ⟨source,all⟩
   exact ⟨source,all (.binder 1) (by simp [facts]),all (.binder 0) (by simp [facts])⟩
 · rintro ⟨source,upper,lower⟩
   have cross := GeneralDictionaryNoModelRefinement257.initial_cross assignment
     ((GeneralDictionaryInitialFill258.raw_initial assignment).mpr source)
   refine ⟨source,?_⟩
   intro fact member
   simp only [facts,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl | rfl | rfl | rfl | rfl
   · rfl
   · exact ⟨rfl,by decide,lower⟩
   · exact ⟨rfl,by decide,subtype_trans upper cross⟩
   · exact lower
   · exact upper

theorem prior_final_exact (assignment : Assignment) : Models finalState assignment ↔
 GeneralDictionaryRebasePublic258.Models finalState assignment := by
 rw [final_exact,GeneralDictionaryRebasePublic258.final_exact,GeneralDictionaryFiniteJournal257.models_exact,
   GeneralDictionaryNoModelRefinement257.all_iff_zero,GeneralDictionaryInitialFill258.raw_initial]

theorem completed (state : State facts) (boundary : Assignment)
 (source : GeneralNominalState.Models snapshot boundary) : Models state (GeneralDictionaryInitialFill258.complete boundary) := by
 have final := (prior_final_exact _).mpr ((GeneralDictionaryRebaseCertificate259.certificate 0 boundary source).final)
 obtain ⟨raw,all⟩ := (GeneralRebaseFactSemantics259.done_exact _ _ _).mp final
 refine ⟨raw,?_⟩
 intro fact present
 exact all fact ((GeneralRebaseFactSemantics259.present_iff state fact).mp present).1

theorem public_models (state : State facts) (boundary : Assignment) :
 (∃ assignment, GeneralDictionaryInitialProjection257.Agree assignment boundary ∧ Models state assignment) ↔
 GeneralNominalState.Models snapshot boundary := by
 constructor
 · rintro ⟨assignment,same,valid⟩
   have small := (GeneralDictionaryInitialFill258.raw_initial assignment).mpr valid.1
   exact (GeneralDictionaryInitialFill258.raw_initial boundary).mp
     ((GeneralDictionarySourceExtension258.view_agree 0 assignment boundary same).mp small)
 · intro source
   exact ⟨GeneralDictionaryInitialFill258.complete boundary,GeneralDictionaryInitialFill258.public_agrees boundary,
     completed state boundary source⟩

theorem write_exact (state : State facts) (proposal : Proposal) (assignment : Assignment) :
 Models (write state proposal) assignment ↔ Models state assignment ∧
 ∀ fact ∈ facts, fact ∈ proposal → factHolds assignment fact := GeneralRebaseFactSemantics259.write_exact ..
end Yulang.GeneralDictionaryRebaseFacts259
