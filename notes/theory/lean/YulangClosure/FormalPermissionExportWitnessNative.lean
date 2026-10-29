import YulangClosure.FormalPermissionExportWitness

/-! Conditional instantiation using ONLY row pairs printed by the failed Rust
runs. Unknown identities, metadata, paths, capture/root and node indices remain
parameters. No passing trace, native decoder authenticity or unequal transport
is asserted. Snapshot/origin DATA stay fixed when observation fields mutate. -/
namespace YulangClosure.FormalPermissionExportWitnessNative
open FormalPermissionSourceOrigin FormalPermissionCaptureConstruction
open FormalPermissionExportWitness
noncomputable section

/-- Attributable to run-1 stdout's failed strict-inequality assertion. -/
def run1Rows : List (Nat × Nat) := [(19, 19), (21, 21)]
/-- Attributable to run-2 stdout's failed strict-inequality assertion. -/
def run2Rows : List (Nat × Nat) := [(21, 21), (23, 23)]

theorem recorded_rows_are_identity :
    (∀ pair ∈ run1Rows, pair.1 = pair.2) ∧
      (∀ pair ∈ run2Rows, pair.1 = pair.2) := by decide

/-- Parameters are not invented native metadata or node receipts. -/
def entries (r₁ r₂ : Nat) (m₁ m₂ : Metadata) (p₁ p₂ : List Step) : List Retained :=
  [⟨m₁, p₁, r₁⟩, ⟨m₂, p₂, r₂⟩]

def snapshot (rows : List (Nat × Nat)) (r₁ r₂ capture root n₁ n₂ : Nat) : CaptureSnapshot :=
  ⟨capture, root, rows, [((r₁, false), n₁), ((r₂, false), n₂)]⟩

def observations (c : Context) (r₁ r₂ capture root n₁ n₂ : Nat)
    (m₁ m₂ : Metadata) (p₁ p₂ : List Step) : List Observation :=
  [⟨0, .definition c.owner, m₁, p₁, r₁, r₁, false, capture, root, n₁, n₁⟩,
   ⟨1, .definition c.owner, m₂, p₂, r₂, r₂, false, capture, root, n₂, n₂⟩]

/-- Only the observed numeric row pairs are specialized; other fields are free. -/
theorem run1_expected (c : Context) (capture root n₁ n₂ : Nat)
    (m₁ m₂ : Metadata) (p₁ p₂ : List Step) :
    expectedAll c (snapshot run1Rows 19 21 capture root n₁ n₂) 0
      (entries 19 21 m₁ m₂ p₁ p₂) =
      some (observations c 19 21 capture root n₁ n₂ m₁ m₂ p₁ p₂) := rfl

theorem run2_expected (c : Context) (capture root n₁ n₂ : Nat)
    (m₁ m₂ : Metadata) (p₁ p₂ : List Step) :
    expectedAll c (snapshot run2Rows 21 23 capture root n₁ n₂) 0
      (entries 21 23 m₁ m₂ p₁ p₂) =
      some (observations c 21 23 capture root n₁ n₂ m₁ m₂ p₁ p₂) := rfl

/-- Successful native-to-code decoding and entry correspondence remain explicit
conditional premises, not established by the two row-pair diagnostics. -/
theorem run1_decode (c : Context) (s : State) (code : ValueCode)
    (out : ValueDecoded c false s) (capture root n₁ n₂ : Nat)
    (m₁ m₂ : Metadata) (p₁ p₂ : List Step)
    (decoded : decodeValue c false s code = some out)
    (retained : out.entries = entries 19 21 m₁ m₂ p₁ p₂) :
    decodeObserved c s code (snapshot run1Rows 19 21 capture root n₁ n₂)
      (observations c 19 21 capture root n₁ n₂ m₁ m₂ p₁ p₂) = some out := by
  have checked : observationsMatch c (snapshot run1Rows 19 21 capture root n₁ n₂)
      out.entries (observations c 19 21 capture root n₁ n₂ m₁ m₂ p₁ p₂) = true := by
    apply (observations_match_iff _ _ _ _).mpr
    rw [retained]
    exact run1_expected c capture root n₁ n₂ m₁ m₂ p₁ p₂
  simp [decodeObserved, decoded, checked]

theorem run2_decode (c : Context) (s : State) (code : ValueCode)
    (out : ValueDecoded c false s) (capture root n₁ n₂ : Nat)
    (m₁ m₂ : Metadata) (p₁ p₂ : List Step)
    (decoded : decodeValue c false s code = some out)
    (retained : out.entries = entries 21 23 m₁ m₂ p₁ p₂) :
    decodeObserved c s code (snapshot run2Rows 21 23 capture root n₁ n₂)
      (observations c 21 23 capture root n₁ n₂ m₁ m₂ p₁ p₂) = some out := by
  have checked : observationsMatch c (snapshot run2Rows 21 23 capture root n₁ n₂)
      out.entries (observations c 21 23 capture root n₁ n₂ m₁ m₂ p₁ p₂) = true := by
    apply (observations_match_iff _ _ _ _).mpr
    rw [retained]
    exact run2_expected c capture root n₁ n₂ m₁ m₂ p₁ p₂
  simp [decodeObserved, decoded, checked]

/-- Fixed snapshot includes the independently supplied materialized-row datum.
Changing q alone cannot produce a record returned by the existing decoder. -/
theorem changed_q_rejected (c : Context) (fixed : CaptureSnapshot) (lineage : Nat)
    (origin : Retained) (observation : Observation) (changed : Nat)
    (wrong : changed ≠ representative fixed origin.allocatedRow) :
    expected c fixed lineage origin ≠ some {observation with canonicalRow := changed} := by
  intro accepted
  have row := (expected_fields accepted).2.2.2.1
  change changed = representative fixed origin.allocatedRow at row
  exact wrong row

/-- Actual native materialization/authentication of this snapshot is OPEN. -/
theorem run1_snapshot_rows (capture root n₁ n₂ : Nat) :
    representative (snapshot run1Rows 19 21 capture root n₁ n₂) 19 = 19 ∧
      representative (snapshot run1Rows 19 21 capture root n₁ n₂) 21 = 21 := ⟨rfl, rfl⟩

theorem run2_snapshot_rows (capture root n₁ n₂ : Nat) :
    representative (snapshot run2Rows 21 23 capture root n₁ n₂) 21 = 21 ∧
      representative (snapshot run2Rows 21 23 capture root n₁ n₂) 23 = 23 := ⟨rfl, rfl⟩

/-- Origin concrete operands stay fixed even if two exports agree with each other. -/
theorem wrong_concrete_rejected (c : Context) (fixed : CaptureSnapshot) (lineage : Nat)
    (origin : Retained) (observation : Observation) (wrongSet : List Nat)
    (wrong : wrongSet ≠ origin.metadata.concrete) :
    expected c fixed lineage origin ≠
      some {observation with metadata := {observation.metadata with concrete := wrongSet}} := by
  intro accepted
  have concrete := congrArg Metadata.concrete (expected_fields accepted).1
  change wrongSet = origin.metadata.concrete at concrete
  exact wrong concrete

theorem same_wrong_set_both_rejected (c : Context) (fixed : CaptureSnapshot)
    (first second : Retained) (left right : Observation) (wrongSet : List Nat)
    (wrongFirst : wrongSet ≠ first.metadata.concrete)
    (wrongSecond : wrongSet ≠ second.metadata.concrete) :
    (expected c fixed 0 first ≠
      some {left with metadata := {left.metadata with concrete := wrongSet}}) ∧
    (expected c fixed 1 second ≠
      some {right with metadata := {right.metadata with concrete := wrongSet}}) :=
  ⟨wrong_concrete_rejected c fixed 0 first left wrongSet wrongFirst,
   wrong_concrete_rejected c fixed 1 second right wrongSet wrongSecond⟩

end
end YulangClosure.FormalPermissionExportWitnessNative
