import Yulang.B4TargetV3Functionality

/-!
# Exact local-totality boundary

Excluded middle alone cannot force an arbitrary Survivor relation to assign
one child list to each implementation key. The conditional theorem below
states that missing mathematical premise explicitly; it is not a new field in
SourceBoundary and not an unconditional completion of I-19 or general B4.
-/
namespace Yulang.B4TargetV3
open CommonRoleOutermostResolver
open B4Target (Vocabulary SourceBoundary SafeKnown Unique)
universe u
variable {v : Vocabulary.{u}} {b : SourceBoundary v} {r : v.Registry} {s : v.State} {d : v.Demand}

/-- A local property to derive from the actual candidate construction, not an oracle. -/
def SurvivorChildrenFunctional (b : SourceBoundary v) (r : v.Registry) (s : v.State)
    (d : v.Demand) : Prop :=
  ∀ key first last, b.Survivor r s d key first → b.Survivor r s d key last → first = last

/-- Totality for arbitrary source boundaries with deterministic surviving children.
This is weaker than unconditional totality: the explicit coherence hypothesis
cannot be derived from excluded middle, as the companion regression proves. -/
theorem local_total (coherent : SurvivorChildrenFunctional b r s d) :
    ∃ frontier, Local b r s d frontier := by
  classical
  by_cases pending : b.RootPending r s d
  · exact ⟨.pending, .pending pending⟩
  by_cases root : b.RootK2 r s d
  · exact ⟨.rejected, .rejected ⟨pending, .inl root⟩⟩
  by_cases candidate : b.CandidateK2 r s d
  · exact ⟨.rejected, .rejected ⟨pending, .inr (.inl candidate)⟩⟩
  by_cases inspecting : b.InspectionPending r s d
  · exact ⟨.pending, .inspectionPending pending inspecting root candidate⟩
  have safe : SafeKnown b r s d := ⟨pending, root, candidate, inspecting⟩
  by_cases existsSurvivor : ∃ key children, b.Survivor r s d key children
  · obtain ⟨key, children, survivor⟩ := existsSurvivor
    by_cases other : ∃ key' children', b.Survivor r s d key' children' ∧ key ≠ key'
    · obtain ⟨key', children', found, distinct⟩ := other
      exact ⟨.ambiguous, .ambiguous safe survivor found distinct⟩
    · refine ⟨.selected key children, .selected safe ⟨survivor, ?_⟩⟩
      intro key' children' found
      have same : key' = key := by
        apply Classical.byContradiction
        intro distinct
        exact other ⟨key', children', found, Ne.symm distinct⟩
      subst key'
      exact ⟨rfl, coherent key children' children found survivor⟩
  · refine ⟨.rejected, .rejected ⟨pending, .inr (.inr ⟨inspecting, ?_⟩)⟩⟩
    intro key children survivor
    exact existsSurvivor ⟨key, children, survivor⟩

/-- Root-known inspection is exactly pending, unless a K2 reason takes priority. -/
theorem inspection_pending_only (started : ¬ b.RootPending r s d)
    (pending : b.InspectionPending r s d) (root : ¬ b.RootK2 r s d)
    (candidate : ¬ b.CandidateK2 r s d) (out : Result) :
    Classify b r s d out ↔ out = .pending := by
  constructor
  · intro derived
    exact classify_functional derived (.inspectionPending started pending root candidate)
  · rintro rfl
    exact .inspectionPending started pending root candidate

theorem inspection_pending_tree_only (started : ¬ b.RootPending r s d)
    (pending : b.InspectionPending r s d) (root : ¬ b.RootK2 r s d)
    (candidate : ¬ b.CandidateK2 r s d) (tree : Tree) :
    Resolves (Local b r s) d tree ↔ tree = .pending := by
  constructor
  · intro derived
    exact resolves_functional b r s _ _ _ derived
      (.pending (.inspectionPending started pending root candidate))
  · rintro rfl
    exact .pending (.inspectionPending started pending root candidate)

/-- The guard on emptiness does not accidentally suppress root K2. -/
theorem rootK2_rejects (started : ¬ b.RootPending r s d) (k2 : b.RootK2 r s d) :
    Local b r s d .rejected := .rejected ⟨started, .inl k2⟩

/-- Candidate K2 also takes priority even while inspection is unfinished. -/
theorem candidateK2_rejects (started : ¬ b.RootPending r s d) (k2 : b.CandidateK2 r s d) :
    Local b r s d .rejected := .rejected ⟨started, .inr (.inl k2)⟩

end Yulang.B4TargetV3
