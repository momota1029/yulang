import Yulang.B4TargetV5
import Yulang.B4TargetV3Totality

/-! The initial-state target with a post-choice output-conflict reason.
Survivor denotes head applicability. Conflict never removes a candidate:
its rejection rule requires a unique head, and ambiguity remains unchanged. -/
namespace Yulang.B4TargetV6
open CommonRoleOutermostResolver
open B4Target (Vocabulary Steps)
open B4TargetV3 (Executor SameDiagnostic)
universe u
variable {v : Vocabulary.{u}}

structure SourceBoundary (v : Vocabulary) extends toV5 : B4TargetV5.SourceBoundary v where
  OutputConflict : v.Registry → v.State → v.Demand → Nat → Prop

abbrev prior (b : SourceBoundary v) : B4TargetV5.SourceBoundary v := b.toV5
abbrev base (b : SourceBoundary v) : B4Target.SourceBoundary v := (prior b).toSourceBoundary
abbrev Reachable (b : SourceBoundary v) := B4TargetV5.Reachable (prior b)
abbrev SafeKnown (b : SourceBoundary v) := B4Target.SafeKnown (base b)
abbrev Unique (b : SourceBoundary v) := B4Target.Unique (base b)

def RejectReason (b : SourceBoundary v) (r : v.Registry) (s : v.State) (d : v.Demand) : Prop :=
  ¬ b.RootPending r s d ∧ (b.RootK2 r s d ∨ b.CandidateK2 r s d ∨
    (¬ b.InspectionPending r s d ∧
      ((∀ key children, ¬ b.Survivor r s d key children) ∨
        ∃ key children, Unique b r s d key children ∧ b.OutputConflict r s d key)))

inductive Local (b : SourceBoundary v) (r : v.Registry) (s : v.State) :
    v.Demand → Frontier v.Demand → Prop where
  | pending : b.RootPending r s d → Local b r s d .pending
  | inspectionPending : ¬ b.RootPending r s d → b.InspectionPending r s d →
      ¬ b.RootK2 r s d → ¬ b.CandidateK2 r s d → Local b r s d .pending
  | rejected : RejectReason b r s d → Local b r s d .rejected
  | ambiguous : SafeKnown b r s d → b.Survivor r s d a xs → b.Survivor r s d z ys →
      a ≠ z → Local b r s d .ambiguous
  | selected : SafeKnown b r s d → Unique b r s d key children → ¬ b.OutputConflict r s d key →
      Local b r s d (.selected key children)

inductive Classify (b : SourceBoundary v) (r : v.Registry) (s : v.State) : v.Demand → Result → Prop where
  | pending : b.RootPending r s d → Classify b r s d .pending
  | inspectionPending : ¬ b.RootPending r s d → b.InspectionPending r s d →
      ¬ b.RootK2 r s d → ¬ b.CandidateK2 r s d → Classify b r s d .pending
  | rejected : RejectReason b r s d → Classify b r s d .rejected
  | ambiguous : SafeKnown b r s d → b.Survivor r s d a xs → b.Survivor r s d z ys →
      a ≠ z → Classify b r s d .ambiguous
  | selected : SafeKnown b r s d → Unique b r s d key children → ¬ b.OutputConflict r s d key →
      All₂ (fun child dictionary => Classify b r s child (.selected dictionary)) children dictionaries →
      Classify b r s d (.selected (.node key dictionaries))

abbrev SaturationTotal (b : SourceBoundary v) (e : Executor v) : Prop := B4TargetV5.SaturationTotal (prior b) e

def Exact (b : SourceBoundary v) (e : Executor v) : Prop :=
  ∀ r, b.Checked r → ∀ s d tree, b.Initial r d s →
    ((e.run r s d).2 = tree ↔ Resolves (Local b r (e.run r s d).1) d tree)

abbrev OrderIndependent (b : SourceBoundary v) (e : Executor v) : Prop := B4TargetV5.OrderIndependent (prior b) e

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

theorem prior_rejection (reason : B4TargetV3.RejectReason (base b) r s d) : RejectReason b r s d := by
  rcases reason with ⟨known,root | candidate | empty⟩
  · exact ⟨known,Or.inl root⟩
  · exact ⟨known,Or.inr (Or.inl candidate)⟩
  · exact ⟨known,Or.inr (Or.inr ⟨empty.1,Or.inl empty.2⟩)⟩

theorem output_conflict_rejected (safe : SafeKnown b r s d)
    (unique : Unique b r s d key children) (conflict : b.OutputConflict r s d key) :
    Local b r s d .rejected :=
  .rejected ⟨safe.1,Or.inr (Or.inr ⟨safe.2.2.2,Or.inr ⟨key,children,unique,conflict⟩⟩)⟩

theorem inspection_not_rejected (pending : b.InspectionPending r s d)
    (root : ¬ b.RootK2 r s d) (candidate : ¬ b.CandidateK2 r s d) : ¬ RejectReason b r s d := by
  rintro ⟨_,old | old | ready⟩
  · exact root old
  · exact candidate old
  · exact ready.1 pending

theorem ambiguous_not_rejected (safe : SafeKnown b r s d)
    (one : b.Survivor r s d a xs) (two : b.Survivor r s d z ys) (different : a ≠ z) :
    ¬ RejectReason b r s d := by
  rintro ⟨_,root | candidate | ⟨_,empty | ⟨key,children,unique,_⟩⟩⟩
  · exact safe.2.1 root
  · exact safe.2.2.1 candidate
  · exact empty a xs one
  · exact B4TargetV3.unique_not_ambiguous unique one two different

theorem selected_not_rejected (safe : SafeKnown b r s d)
    (unique : Unique b r s d key children) (clear : ¬ b.OutputConflict r s d key) : ¬ RejectReason b r s d := by
  rintro ⟨_,root | candidate | ⟨_,empty | ⟨other,cs,chosen,conflict⟩⟩⟩
  · exact safe.2.1 root
  · exact safe.2.2.1 candidate
  · exact empty key children unique.1
  · exact clear ((unique.2 other cs chosen.1).1 ▸ conflict)

theorem local_total (coherent : B4TargetV3.SurvivorChildrenFunctional (base b) r s d) :
    ∃ frontier, Local b r s d frontier := by
  classical
  obtain ⟨frontier,old⟩ := B4TargetV3.local_total coherent
  cases old with
  | pending h => exact ⟨.pending,.pending h⟩
  | inspectionPending a c e f => exact ⟨.pending,.inspectionPending a c e f⟩
  | rejected reason => exact ⟨.rejected,.rejected (prior_rejection reason)⟩
  | ambiguous safe one two different => exact ⟨.ambiguous,.ambiguous safe one two different⟩
  | @selected key children safe unique =>
      by_cases conflict : b.OutputConflict r s d key
      · exact ⟨.rejected,output_conflict_rejected safe unique conflict⟩
      · exact ⟨.selected key children,.selected safe unique conflict⟩

theorem local_functional (first : Local b r s d left) (last : Local b r s d right) : left = right := by
  cases first with
  | pending pending =>
      cases last with
      | pending => rfl
      | inspectionPending => rfl
      | rejected reason => exact False.elim (reason.1 pending)
      | ambiguous safe _ _ _ => exact False.elim (safe.1 pending)
      | selected safe _ _ => exact False.elim (safe.1 pending)
  | inspectionPending started pending root candidate =>
      cases last with
      | pending => rfl
      | inspectionPending => rfl
      | rejected reason => exact False.elim (inspection_not_rejected pending root candidate reason)
      | ambiguous safe _ _ _ => exact False.elim (safe.2.2.2 pending)
      | selected safe _ _ => exact False.elim (safe.2.2.2 pending)
  | rejected reason =>
      cases last with
      | pending pending => exact False.elim (reason.1 pending)
      | inspectionPending _ pending root candidate =>
          exact False.elim (inspection_not_rejected pending root candidate reason)
      | rejected => rfl
      | ambiguous safe one two different => exact False.elim (ambiguous_not_rejected safe one two different reason)
      | selected safe unique clear => exact False.elim (selected_not_rejected safe unique clear reason)
  | ambiguous safe one two different =>
      cases last with
      | pending pending => exact False.elim (safe.1 pending)
      | inspectionPending _ pending _ _ => exact False.elim (safe.2.2.2 pending)
      | rejected reason => exact False.elim (ambiguous_not_rejected safe one two different reason)
      | ambiguous => rfl
      | selected _ unique _ => exact False.elim (B4TargetV3.unique_not_ambiguous unique one two different)
  | selected safe unique clear =>
      cases last with
      | pending pending => exact False.elim (safe.1 pending)
      | inspectionPending _ pending _ _ => exact False.elim (safe.2.2.2 pending)
      | rejected reason => exact False.elim (selected_not_rejected safe unique clear reason)
      | ambiguous _ one two different => exact False.elim (B4TargetV3.unique_not_ambiguous unique one two different)
      | selected _ other _ =>
          obtain ⟨keys,children⟩ := unique.2 _ _ other.1
          cases keys; cases children; rfl

theorem ambiguous_only (safe : SafeKnown b r s d)
    (one : b.Survivor r s d a xs) (two : b.Survivor r s d z ys) (different : a ≠ z)
    (frontier) : Local b r s d frontier ↔ frontier = .ambiguous :=
  ⟨fun localRule => local_functional localRule (.ambiguous safe one two different),
    fun same => same ▸ Local.ambiguous safe one two different⟩

theorem selected_clear (chosen : Local b r s d (.selected key children)) : ¬ b.OutputConflict r s d key := by
  cases chosen with | selected _ _ clear => exact clear

end Yulang.B4TargetV6
