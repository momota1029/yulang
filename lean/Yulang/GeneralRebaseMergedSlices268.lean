import Yulang.GeneralRebaseFiniteSlices268
import Yulang.GeneralRebaseMergedGate268

namespace Yulang.GeneralRebaseMergedSlices268
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMergedConflict232 (ContextModels ClassEquations MergedOutputConflict)
open GeneralNominalVersionedMergedConflict232.Old (ContextPresent MergedClass Registered)
open GeneralRebaseFiniteSlices268 (slices exact_slices membership_cover)
open GeneralRebasePartialBool268 (Reflect Answer both neg)
open GeneralRebasePartialFinite268 (any any_sound transfer)
open GeneralRebaseRawK2Probe268 (bool_reflect)

abbrev Atom := PresenceNormalForm.Atom Nat

def atoms (state : State roles) : List Atom := state.core.erased.current.context.state.ordinary

def classes (state : State roles) : List (Occurrence roles) :=
 state.core.erased.current.sites.map (·.occurrence)

theorem registered_exact (state : State roles) (focus : Occurrence roles) :
 focus ∈ classes state ↔ Registered state.legacy focus := by simp [classes,Registered,GeneralNominalCenteredHeadAllocMergedConflict.Registered]

theorem context_congr (state : State roles) (one two : List Atom) (first last : List (Occurrence roles))
 (sameAtoms : ∀ a, a ∈ one ↔ a ∈ two) (sameClasses : ∀ f, f ∈ first ↔ f ∈ last) (model) :
 ContextModels state one first model ↔ ContextModels state two last model := by
 simp only [ContextModels,PresenceNormalForm.All,sameAtoms,sameClasses]

def Bad (state : State roles) (focus : Occurrence roles) (used : List Atom) (linked : List (Occurrence roles)) : Prop :=
 (∃ model, ContextModels state used linked model) ∧
 ¬ ∃ model, ContextModels state used linked model ∧ ClassEquations state focus model

theorem bounded_iff (state : State roles) (focus : Occurrence roles) :
 MergedOutputConflict state focus ↔ MergedClass state.legacy focus ∧
 ∃ used ∈ slices (atoms state), ∃ linked ∈ slices (classes state), Bad state focus used linked := by
 constructor
 · rintro ⟨merged,used,linked,present,bad⟩
   have allowedClasses : linked ⊆ classes state := fun _ member => (registered_exact state _).mpr (present.2 _ member)
   obtain ⟨a,inA,equalA⟩ := membership_cover (present := atoms state) present.1
   obtain ⟨c,inC,equalC⟩ := membership_cover allowedClasses
   have same := context_congr state a used c linked equalA equalC
   obtain ⟨⟨model,admissible⟩,no⟩ := bad
   exact ⟨merged,a,inA,c,inC,⟨model,(same model).mpr admissible⟩,
     fun ⟨other,valid,holds⟩ => no ⟨other,(same other).mp valid,holds⟩⟩
 · rintro ⟨merged,used,inA,linked,inC,bad⟩
   refine ⟨merged,used,linked,⟨((exact_slices ..).mp inA).subset,?_⟩,bad⟩
   intro f member
   exact (registered_exact state f).mp (((exact_slices ..).mp inC).subset member)

def probe (state : State roles) (focus : Occurrence roles)
 (context extended : List Atom → List (Occurrence roles) → Answer) : Answer :=
 if GeneralRebaseMergedGate268.member state focus then
   any (fun used => any (fun linked => both (context used linked) (neg (extended used linked)))
     (slices (classes state))) (slices (atoms state))
 else some false

theorem probe_sound (state : State roles) (focus : Occurrence roles)
 (context extended : List Atom → List (Occurrence roles) → Answer)
 (known : ∀ used ∈ slices (atoms state), ∀ linked ∈ slices (classes state),
   Reflect (∃ model, ContextModels state used linked model) (context used linked))
 (extra : ∀ used ∈ slices (atoms state), ∀ linked ∈ slices (classes state),
   Reflect (∃ model, ContextModels state used linked model ∧ ClassEquations state focus model)
     (extended used linked)) : Reflect (MergedOutputConflict state focus) (probe state focus context extended) := by
 apply transfer (bounded_iff state focus).symm
 have memberExact := GeneralRebaseMergedGate268.member_exact state focus
 unfold probe
 split
 · rename_i yes
   apply transfer (p := ∃ used ∈ slices (atoms state), ∃ linked ∈ slices (classes state), Bad state focus used linked)
   · exact ⟨fun h => ⟨memberExact.mp yes,h⟩,And.right⟩
   · apply any_sound
     intro used onAtoms
     apply any_sound
     intro linked onClasses
     exact GeneralRebasePartialBool268.both_sound (known used onAtoms linked onClasses)
       (GeneralRebasePartialBool268.neg_sound (extra used onAtoms linked onClasses))
 · rename_i no
   exact fun h => no (memberExact.mpr h.1)

theorem probe_total (state : State roles) (focus : Occurrence roles)
 (context extended : List Atom → List (Occurrence roles) → Answer)
 (known : ∀ used ∈ slices (atoms state), ∀ linked ∈ slices (classes state), context used linked ≠ none)
 (extra : ∀ used ∈ slices (atoms state), ∀ linked ∈ slices (classes state), extended used linked ≠ none) :
 probe state focus context extended ≠ none := by
 unfold probe
 split
 · apply GeneralRebasePartialFinite268.any_total
   intro used a
   apply GeneralRebasePartialFinite268.any_total
   intro linked c
   exact GeneralRebasePartialBool268.total_both (known used a linked c)
     (GeneralRebasePartialBool268.total_neg (extra used a linked c))
 · simp

end Yulang.GeneralRebaseMergedSlices268
