import Yulang.GeneralRebaseRefreshSelected275

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27500
set_option maxHeartbeats 9300000
namespace Yulang.GeneralRebaseRefreshPublic275
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralDictionaryOptionalInitial229 (registry sourceRegistry declaration)
open GeneralDictionaryVersionedSecondInstall233 (installed)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalVersionedEvidence231 (Evidence)
open GeneralDictionaryReadback (Payload payload_iff_erased)
open GeneralRebaseRefreshEvidence275 (all_histories leaves)
open GeneralRebaseCompoundRows273 (Agrees)
open GeneralRebaseCompoundRowsMeaning273 (Public)
open GeneralRebaseCompoundPublic273 (Fixed)
open GeneralRebaseTerminalDecode274 (decode)
open GeneralRebaseTerminalStableCells274 (StoreChecked)
open GeneralRebaseTerminalPayload274 (accepts accepted_shape)

abbrev After (state : State roles) := B4Target.Steps (Step registry root) installed state

theorem same_models {first last : State roles} (one : After first) (two : After last) (m : Assignment) :
 Models first m ↔ Models last m :=
 ((all_histories one).1.anchor.models m).trans ((all_histories two).1.anchor.models m).symm

theorem same_public {first last : State roles} (one : After first) (two : After last) (boundary : Assignment) :
 Public first boundary ↔ Public last boundary := by
 have eq := same_models one two
 constructor
 · rintro ⟨m,agrees,model⟩
   exact ⟨m,agrees,(eq _).mp model⟩
 · rintro ⟨m,agrees,model⟩
   exact ⟨m,agrees,(eq _).mpr model⟩

theorem payload_shape {state : State roles} (m : Assignment) (data : Payload)
 (valid : Evidence registry state.core m root data) : data = .node declaration.id [] := by
 have erasable := (payload_iff_erased _ _ _).mpr valid
 cases erasable with
 | node rule children =>
   obtain ⟨p,recorded⟩ := rule
   have decl := (GeneralRebaseRefreshFrame275.of_frame recorded.frame).declaration_eq
   have key := recorded.frame.key_eq
   rw [decl] at key
   have none : GeneralNominalVersionedFrame231.children p.packet = [] := by
     unfold GeneralNominalVersionedFrame231.children GeneralDictionaryEmissionPlans.children
     have leaf : p.packet.declaration.requirements = [] := by rw [decl]
     rw [GeneralRebaseRetarget275.no_emission _ _ _ _ _ leaf]
     rfl
   rw [recorded.children_eq,none] at children
   cases children
   rw [← key]

theorem checked {state : State roles} (path : After state) (m : Assignment)
 (valid : Models state m) (data : Payload) :
 accepts data = true ↔ Evidence registry state.core m root data := by
 rw [accepted_shape]
 constructor
 · rintro rfl
   exact leaves (all_histories path).2 m valid
 · exact payload_shape m data

theorem public_exact {state : State roles} (path : After state) (boundary : Assignment) :
 Public state boundary ↔ Fixed boundary :=
 (same_public path (.refl : After installed) boundary).trans (GeneralRebaseTerminalRows274.terminal_public boundary)

theorem decode_exact {state : State roles} (path : After state) (boundary : Assignment) (data : Payload) :
 (Fixed boundary ∧ accepts data = true) ↔
 (Models state (decode boundary) ∧ Evidence registry state.core (decode boundary) root data ∧
    StoreChecked (decode boundary)) := by
 constructor
 · rintro ⟨fixed,computed⟩
   have model := (same_models (.refl : After installed) path _).mp (GeneralRebaseTerminalDecode274.terminal boundary fixed)
   exact ⟨model,(checked path _ model data).mp computed,GeneralRebaseTerminalDecode274.realizes_run boundary fixed⟩
 · rintro ⟨model,evidence,_⟩
   refine ⟨(public_exact path boundary).mp ⟨decode boundary,GeneralRebaseTerminalDecode274.agrees boundary,model⟩,?_⟩
   exact (checked path _ model data).mpr evidence

end Yulang.GeneralRebaseRefreshPublic275
