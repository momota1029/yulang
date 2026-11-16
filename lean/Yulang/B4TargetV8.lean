import Yulang.B4TargetV7

/-! I-41: contradictory actual-argument sharing is a rejection, not a new
pending case. Known K2 retains priority and competing candidates remain
ambiguous. Ordinary V7 rules apply when sharing is consistent. -/
namespace Yulang.B4TargetV8
open CommonRoleOutermostResolver
open B4Target (Vocabulary Steps)
open B4TargetV3 (Executor)
universe u
variable {v : Vocabulary.{u}}

structure SourceBoundary (v : Vocabulary) extends toV7 : B4TargetV7.SourceBoundary v where
  SharingConflict : v.Registry → v.State → v.Demand → Prop

abbrev prior (b : SourceBoundary v) : B4TargetV5.SourceBoundary v := B4TargetV7.prior b.toV7
abbrev base (b : SourceBoundary v) : B4Target.SourceBoundary v := B4TargetV7.base b.toV7
abbrev Reachable (b : SourceBoundary v) := B4TargetV7.Reachable b.toV7
abbrev SafeKnown (b : SourceBoundary v) := B4TargetV7.SafeKnown b.toV7
abbrev Unique (b : SourceBoundary v) := B4TargetV7.Unique b.toV7

def PriorityAmbiguity (b : SourceBoundary v) (r : v.Registry) (s : v.State) (d : v.Demand) : Prop :=
  ¬ (¬ b.RootPending r s d ∧ (b.RootK2 r s d ∨ b.CandidateK2 r s d)) ∧
    ∃ a xs z ys, b.Survivor r s d a xs ∧ b.Survivor r s d z ys ∧ a ≠ z

def RejectReason (b : SourceBoundary v) (r : v.Registry) (s : v.State) (d : v.Demand) : Prop :=
  (b.SharingConflict r s d ∧ ¬ PriorityAmbiguity b r s d) ∨
    (¬ b.SharingConflict r s d ∧ B4TargetV7.RejectReason b.toV7 r s d)

inductive Local (b : SourceBoundary v) (r : v.Registry) (s : v.State) :
    v.Demand → Frontier v.Demand → Prop where
  | ordinary : ¬ b.SharingConflict r s d → B4TargetV7.Local b.toV7 r s d frontier → Local b r s d frontier
  | sharingRejected : b.SharingConflict r s d → ¬ PriorityAmbiguity b r s d → Local b r s d .rejected
  | sharingAmbiguous : b.SharingConflict r s d → PriorityAmbiguity b r s d → Local b r s d .ambiguous

inductive Classify (b : SourceBoundary v) (r : v.Registry) (s : v.State) : v.Demand → Result → Prop where
  | pending : Local b r s d .pending → Classify b r s d .pending
  | rejected : Local b r s d .rejected → Classify b r s d .rejected
  | ambiguous : Local b r s d .ambiguous → Classify b r s d .ambiguous
  | selected : Local b r s d (.selected key children) →
      All₂ (fun child dictionary => Classify b r s child (.selected dictionary)) children dictionaries →
      Classify b r s d (.selected (.node key dictionaries))

abbrev SaturationTotal (b : SourceBoundary v) (e : Executor v) : Prop := B4TargetV7.SaturationTotal b.toV7 e
abbrev OrderIndependent (b : SourceBoundary v) (e : Executor v) : Prop := B4TargetV7.OrderIndependent b.toV7 e

def Exact (b : SourceBoundary v) (e : Executor v) : Prop :=
  ∀ r, b.Checked r → ∀ s d tree, b.Initial r d s →
    ((e.run r s d).2 = tree ↔ Resolves (Local b r (e.run r s d).1) d tree)
def DictionarySound (b : SourceBoundary v) (e : Executor v) : Prop :=
  ∀ r, b.Checked r → ∀ s d dictionary, b.Initial r d s →
    Classify b r (e.run r s d).1 d (.selected dictionary) →
    ∀ model, b.Models (e.run r s d).1 model → b.Evidence r (e.run r s d).1 model d dictionary

def NoFalseRejection (b : SourceBoundary v) (e : Executor v) : Prop :=
  ∀ r, b.Checked r → ∀ s d, b.Initial r d s →
    (e.run r s d).2 = .rejected → RejectReason b r (e.run r s d).1 d

def Statement (b : SourceBoundary v) (e : Executor v) : Prop :=
  SaturationTotal b e ∧ Exact b e ∧ OrderIndependent b e ∧ DictionarySound b e ∧ NoFalseRejection b e

variable {b : SourceBoundary v} {r : v.Registry} {s : v.State} {d : v.Demand}

theorem local_total (coherent : B4TargetV3.SurvivorChildrenFunctional (base b) r s d) :
    ∃ frontier, Local b r s d frontier := by
  classical
  by_cases conflict : b.SharingConflict r s d
  · by_cases ambiguity : PriorityAmbiguity b r s d
    · exact ⟨.ambiguous,.sharingAmbiguous conflict ambiguity⟩
    · exact ⟨.rejected,.sharingRejected conflict ambiguity⟩
  · obtain ⟨frontier,chosen⟩ := B4TargetV7.local_total coherent
    exact ⟨frontier,.ordinary conflict chosen⟩

theorem local_functional (one : Local b r s d first) (two : Local b r s d last) : first = last := by
  cases one with
  | ordinary clear chosen =>
    cases two with
    | ordinary _ other => exact B4TargetV7.local_functional chosen other
    | sharingRejected conflict _ => exact False.elim (clear conflict)
    | sharingAmbiguous conflict _ => exact False.elim (clear conflict)
  | sharingRejected conflict unambiguous =>
    cases two with
    | ordinary clear _ => exact False.elim (clear conflict)
    | sharingRejected => rfl
    | sharingAmbiguous _ ambiguity => exact False.elim (unambiguous ambiguity)
  | sharingAmbiguous conflict ambiguity =>
    cases two with
    | ordinary clear _ => exact False.elim (clear conflict)
    | sharingRejected _ unambiguous => exact False.elim (unambiguous ambiguity)
    | sharingAmbiguous => rfl

theorem selected_iff : Local b r s d (.selected key children) ↔
    B4TargetV7.Local b.toV7 r s d (.selected key children) ∧ ¬ b.SharingConflict r s d := by
  constructor
  · intro chosen; cases chosen with | ordinary clear old => exact ⟨old,clear⟩
  · rintro ⟨old,clear⟩; exact .ordinary clear old

theorem rejected_iff : Local b r s d .rejected ↔ RejectReason b r s d := by
  constructor
  · intro chosen
    cases chosen with
    | ordinary clear old => exact Or.inr ⟨clear, B4TargetV7.rejected_iff.mp old⟩
    | sharingRejected conflict unambiguous => exact Or.inl ⟨conflict,unambiguous⟩
  · rintro (⟨conflict,unambiguous⟩ | ⟨clear,old⟩)
    · exact .sharingRejected conflict unambiguous
    · exact .ordinary clear (B4TargetV7.rejected_iff.mpr old)

theorem conflict_not_pending (conflict : b.SharingConflict r s d) : ¬ Local b r s d .pending := by
  intro pending; cases pending with | ordinary clear _ => exact clear conflict

theorem unique_not_priorityAmbiguity (unique : Unique b r s d key children) : ¬ PriorityAmbiguity b r s d := by
  rintro ⟨_,a,xs,z,ys,one,two,different⟩
  exact B4TargetV3.unique_not_ambiguous unique one two different

theorem sharing_unique_rejected (conflict : b.SharingConflict r s d)
    (unique : Unique b r s d key children) : Local b r s d .rejected :=
  .sharingRejected conflict (unique_not_priorityAmbiguity unique)

theorem child_prior (edge : Child (Local b r s) child parent) : Child (B4TargetV7.Local b.toV7 r s) child parent := by
  obtain ⟨key,children,selected,member⟩ := edge
  exact ⟨key,children,(selected_iff.mp selected).1,member⟩

theorem local_transport {other : SourceBoundary v} {rr : v.Registry} {ss : v.State} {dd : v.Demand}
    (ordinary : ∀ frontier, B4TargetV7.Local b.toV7 r s d frontier ↔ B4TargetV7.Local other.toV7 rr ss dd frontier)
    (conflict : b.SharingConflict r s d ↔ other.SharingConflict rr ss dd)
    (ambiguity : PriorityAmbiguity b r s d ↔ PriorityAmbiguity other rr ss dd) (frontier) :
    Local b r s d frontier ↔ Local other rr ss dd frontier := by
  constructor <;> intro given
  · cases given with
    | ordinary clear chosen => exact .ordinary ((not_congr conflict).mp clear) ((ordinary _).mp chosen)
    | sharingRejected present clear => exact .sharingRejected (conflict.mp present) ((not_congr ambiguity).mp clear)
    | sharingAmbiguous present chosen => exact .sharingAmbiguous (conflict.mp present) (ambiguity.mp chosen)
  · cases given with
    | ordinary clear chosen => exact .ordinary ((not_congr conflict).mpr clear) ((ordinary _).mpr chosen)
    | sharingRejected present clear => exact .sharingRejected (conflict.mpr present) ((not_congr ambiguity).mpr clear)
    | sharingAmbiguous present chosen => exact .sharingAmbiguous (conflict.mpr present) (ambiguity.mpr chosen)

/-- Adding a contradiction cannot turn a demand into a pending demand. -/
theorem pending_iff : Local b r s d .pending ↔
    B4TargetV7.Local b.toV7 r s d .pending ∧ ¬ b.SharingConflict r s d := by
  constructor
  · intro chosen; cases chosen with | ordinary clear old => exact ⟨old, clear⟩
  · rintro ⟨old, clear⟩; exact .ordinary clear old

/-- A sharing contradiction never manufactures a selected dictionary node. -/
theorem conflict_not_selected (conflict : b.SharingConflict r s d) :
    ¬ Local b r s d (.selected key children) := by
  intro selected
  exact (selected_iff.mp selected).2 conflict

/-- The old classifier is retained verbatim at any demand with no sharing conflict. -/
theorem local_iff_prior (clear : ¬ b.SharingConflict r s d) (frontier) :
    Local b r s d frontier ↔ B4TargetV7.Local b.toV7 r s d frontier := by
  constructor
  · intro chosen
    cases chosen with
    | ordinary _ old => exact old
    | sharingRejected conflict _ => exact False.elim (clear conflict)
    | sharingAmbiguous conflict _ => exact False.elim (clear conflict)
  · exact .ordinary clear

end Yulang.B4TargetV8
