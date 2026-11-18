import Yulang.GeneralRebaseSourceRequests264
namespace Yulang.GeneralRebaseMergeRequests264
open GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232
open GeneralNominalSaturationState (Alias)
open GeneralNominalCenteredHeadOutputs (requests)
open GeneralSourceState (Output)

/-- One undirected bridge between two old alias classes. -/
def Joined (state : GeneralNominalSaturationState.State roles) (first last a b : Nat) : Prop :=
 Alias state a b ∨ (Alias state a first ∧ Alias state last b) ∨ (Alias state a last ∧ Alias state first b)

theorem joined_symm (same : Joined state first last a b) : Joined state first last b a := by
 rcases same with old | ⟨left,right⟩ | ⟨left,right⟩
 · exact Or.inl old.symm
 · exact Or.inr (Or.inr ⟨right.symm,left.symm⟩)
 · exact Or.inr (Or.inl ⟨right.symm,left.symm⟩)

theorem joined_trans (one : Joined state first last a b) (two : Joined state first last b c) :
 Joined state first last a c := by
 rcases one with old | ⟨left,right⟩ | ⟨left,right⟩
 · rcases two with next | ⟨start,finish⟩ | ⟨start,finish⟩
   · exact Or.inl (old.trans next)
   · exact Or.inr (Or.inl ⟨old.trans start,finish⟩)
   · exact Or.inr (Or.inr ⟨old.trans start,finish⟩)
 · rcases two with next | ⟨start,finish⟩ | ⟨start,finish⟩
   · exact Or.inr (Or.inl ⟨left,right.trans next⟩)
   · exact Or.inr (Or.inl ⟨left,finish⟩)
   · exact Or.inl (left.trans finish)
 · rcases two with next | ⟨start,finish⟩ | ⟨start,finish⟩
   · exact Or.inr (Or.inr ⟨left,right.trans next⟩)
   · exact Or.inl (left.trans finish)
   · exact Or.inr (Or.inr ⟨left,finish⟩)

theorem alias_merge (state : State roles) (first last : Site roles) (a b : Nat) :
 Alias (GeneralNominalVersionedAdministrative232.merge state first last).core.erased.current a b ↔
 Joined state.core.erased.current first.occurrence.identity last.occurrence.identity a b := by
 constructor
 · intro same
   induction same with
   | refl => exact Or.inl (.refl _)
   | edge member =>
     rcases List.mem_cons.mp member with equal | prior
     · obtain ⟨rfl,rfl⟩ := Prod.mk.inj equal
       exact Or.inr (Or.inl ⟨.refl _,.refl _⟩)
     · exact Or.inl (.edge prior)
   | symm _ ih => exact joined_symm ih
   | trans _ _ one two => exact joined_trans one two
 · intro same
   have old : ∀ {a b}, Alias state.core.erased.current a b →
     Alias (GeneralNominalVersionedAdministrative232.merge state first last).core.erased.current a b := by
     intro a b alias
     induction alias with
     | refl => exact .refl _
     | edge member => exact .edge (List.mem_cons_of_mem _ member)
     | symm _ ih => exact .symm ih
     | trans _ _ one two => exact .trans one two
   have bridge : Alias (GeneralNominalVersionedAdministrative232.merge state first last).core.erased.current
       first.occurrence.identity last.occurrence.identity := .edge (List.mem_cons_self ..)
   rcases same with same | ⟨left,right⟩ | ⟨left,right⟩
   · exact old same
   · exact (old left).trans (bridge.trans (old right))
   · exact (old left).trans (bridge.symm.trans (old right))

/-- Exact class union, including third-party and one-sided requests. -/
theorem requests_merge (state : State roles) (first last : Site roles)
 (root : Occurrence roles) (output : Output) :
 output ∈ requests (GeneralNominalVersionedAdministrative232.merge state first last).core root ↔
 output ∈ requests state.core root ∨
 (Alias state.core.erased.current root.identity first.occurrence.identity ∧ output ∈ requests state.core last.occurrence) ∨
 (Alias state.core.erased.current root.identity last.occurrence.identity ∧ output ∈ requests state.core first.occurrence) := by
 constructor
 · intro member
   obtain ⟨site,present,same,within⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp member
   rcases (alias_merge state first last _ _).mp same with old | ⟨left,right⟩ | ⟨left,right⟩
   · exact Or.inl (GeneralNominalCenteredHeadOutputs.request_retained site present old within)
   · exact Or.inr (Or.inl ⟨left,GeneralNominalCenteredHeadOutputs.request_retained site present right within⟩)
   · exact Or.inr (Or.inr ⟨left,GeneralNominalCenteredHeadOutputs.request_retained site present right within⟩)
 · rintro (member | ⟨left,member⟩ | ⟨left,member⟩)
   · exact (GeneralRebaseSourceRequests264.merge_growth state first last).requests root output member
   · obtain ⟨site,present,right,within⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp member
     exact GeneralNominalCenteredHeadOutputs.request_retained site present
       ((alias_merge state first last _ _).mpr (Or.inr (Or.inl ⟨left,right⟩))) within
   · obtain ⟨site,present,right,within⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp member
     exact GeneralNominalCenteredHeadOutputs.request_retained site present
       ((alias_merge state first last _ _).mpr (Or.inr (Or.inr ⟨left,right⟩))) within

theorem requests_unaffected (state : State roles) (first last : Site roles) (root : Occurrence roles)
 (awayFirst : ¬ Alias state.core.erased.current root.identity first.occurrence.identity)
 (awayLast : ¬ Alias state.core.erased.current root.identity last.occurrence.identity)
 (output : Output) :
 output ∈ requests (GeneralNominalVersionedAdministrative232.merge state first last).core root ↔
 output ∈ requests state.core root := by
 rw [requests_merge]
 simp only [awayFirst,awayLast,false_and,or_false]
end Yulang.GeneralRebaseMergeRequests264
