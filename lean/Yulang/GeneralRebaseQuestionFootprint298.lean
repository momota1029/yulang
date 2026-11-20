import Yulang.GeneralRebaseRevisitedTrace298
import Yulang.GeneralRebaseRowJournal298

namespace Yulang.GeneralRebaseQuestionFootprint298
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (model)
open GeneralNominalRebaseJournalView243 (Journal)
open GeneralRebaseSymbolicQuestions298 (Body Head)
open GeneralRebaseSignedModels297 (Sign)

structure Footprint where
  types : List Nat
  rows : List Nat

def append (a b : Footprint) : Footprint := ⟨a.types ++ b.types,a.rows ++ b.rows⟩

def agrees (f : Footprint) (a b : Assignment) : Prop :=
  (∀ n ∈ f.types, (a n).1 = (b n).1) ∧ ∀ n ∈ f.rows, (a n).2 = (b n).2

theorem agrees_append {f g : Footprint} {a b : Assignment} :
    agrees (append f g) a b ↔ agrees f a b ∧ agrees g a b := by
  unfold agrees append
  simp only [List.mem_append,or_imp,forall_and]
  exact ⟨fun ⟨⟨a,b⟩,c,d⟩ => ⟨⟨a,c⟩,b,d⟩,fun ⟨⟨a,b⟩,c,d⟩ => ⟨⟨a,c⟩,b,d⟩⟩

/-- Compare the type and row changes separately on independent coordinates.
No global equality of row values is required at the public interface. -/
theorem typed_cut (P : Assignment → Prop) (f : Footprint)
    (typeCase : ∀ a b : Assignment, (∀ n, (a n).2 = (b n).2) →
      (∀ n ∈ f.types, (a n).1 = (b n).1) → (P a ↔ P b))
    (rowCase : ∀ a b : Assignment, (∀ n, (a n).1 = (b n).1) →
      (∀ n ∈ f.rows, (a n).2 = (b n).2) → (P a ↔ P b))
    (a b : Assignment) (equal : agrees f a b) : P a ↔ P b :=
  let c : Assignment := fun n => ((b n).1,(a n).2)
  (typeCase a c (fun _ => rfl) equal.1).trans (rowCase c b (fun _ => rfl) equal.2)

def prior (view : Journal) : Footprint :=
  ⟨GeneralNominalJournalSupport249.support view,GeneralRebaseRowJournal298.support view⟩

theorem prior_exact (view : Journal) (a b : Assignment) (equal : agrees (prior view) a b) :
    view.Models a ↔ view.Models b :=
  typed_cut view.Models (prior view) (GeneralNominalJournalSupport249.models_iff view)
    (GeneralRebaseRowJournal298.models_iff view) a b equal

def head (h : Head) : Footprint :=
  ⟨GeneralNominalViewSupport249.support h.view ++ GeneralNominalProjectionSupport249.support h.projection,
   GeneralRebaseRowView298.support h.view ++ GeneralRebaseRowProjection298.support h.projection⟩

theorem head_exact (h : Head) (a b : Assignment) (equal : agrees (head h) a b) : h.Holds a ↔ h.Holds b := by
  apply typed_cut h.Holds (head h) _ _ a b equal
  · intro a b rows types
    exact and_congr (GeneralNominalViewSupport249.models_iff h.view a b rows
      (fun n h => types n (List.mem_append_left _ h)))
      (GeneralNominalProjectionSupport249.models_iff h.projection a b rows
        (fun n h => types n (List.mem_append_right _ h)))
  · intro a b types rows
    exact and_congr (GeneralRebaseRowView298.models_iff h.view a b types
      (fun n h => rows n (List.mem_append_left _ h)))
      (GeneralRebaseRowProjection298.models_iff h.projection a b types
        (fun n h => rows n (List.mem_append_right _ h)))

abbrev Candidate := GeneralNominalRebasePacketView243.Packet × GeneralNominalRebaseClassView243.View

def candidate (c : Candidate) : Footprint :=
  ⟨GeneralNominalPacketSupport249.support c.1 ++ GeneralNominalClassSupport249.support c.2,
   GeneralRebaseRowPacket298.support c.1 ++ GeneralRebaseRowClass298.support c.2⟩

theorem candidate_exact (c : Candidate) (a b : Assignment) (equal : agrees (candidate c) a b) :
    (c.1.Holds a ∧ c.2.Holds a) ↔ (c.1.Holds b ∧ c.2.Holds b) := by
  apply typed_cut (fun m => c.1.Holds m ∧ c.2.Holds m) (candidate c) _ _ a b equal
  · intro a b rows types
    exact and_congr (GeneralNominalPacketSupport249.packet_iff c.1 a b rows
      (fun n h => types n (List.mem_append_left _ h)))
      (GeneralNominalClassSupport249.holds_iff c.2 a b rows
        (fun n h => types n (List.mem_append_right _ h)))
  · intro a b types rows
    exact and_congr (GeneralRebaseRowPacket298.packet_iff c.1 a b types
      (fun n h => rows n (List.mem_append_left _ h)))
      (GeneralRebaseRowClass298.holds_iff c.2 a b types
        (fun n h => rows n (List.mem_append_right _ h)))

def atoms (as : List GeneralNominalRebaseRawView243.Atom) : Footprint :=
  ⟨GeneralPresenceConsumerSupport246.listTypedReads as,GeneralRebaseRowBasis298.listRowReads as⟩

theorem atoms_exact (as : List GeneralNominalRebaseRawView243.Atom) (a b : Assignment)
    (equal : agrees (atoms as) a b) :
    PresenceNormalForm.All model a as ↔ PresenceNormalForm.All model b as :=
  typed_cut (fun m => PresenceNormalForm.All model m as) (atoms as)
    (fun x y rows => GeneralPresenceConsumerSupport246.all_iff model x y rows as)
    (fun x y types => GeneralRebaseRowBasis298.all_iff model x y types as) a b equal

def question (j : Journal) : Body → Footprint
 | .head h => head h
 | .install c _ => append (prior j) (candidate c)
 | .mergeFailure as => append (prior j) (atoms as)

theorem question_exact (j : Journal) (q : Body) (a b : Assignment)
    (equal : agrees (question j q) a b) : q.Holds j a ↔ q.Holds j b := by
  cases q with
  | head h => exact head_exact h a b equal
  | install c sg =>
    have split := agrees_append.mp equal
    cases sg
    · exact and_congr (prior_exact j a b split.1) (candidate_exact c a b split.2)
    · exact and_congr (prior_exact j a b split.1) (not_congr (candidate_exact c a b split.2))
  | mergeFailure as =>
    have split := agrees_append.mp equal
    exact and_congr (prior_exact j a b split.1) (not_congr (atoms_exact as a b split.2))

end Yulang.GeneralRebaseQuestionFootprint298
