import Yulang.GuardedAffineRows

/-!
# Preserve original row problems through fixed-key guarded normalization

Every route compiled from the existing row-expression AST is normalized at a
fixed operation key. The resulting guarded translation graph agrees with the
original graph at that key. Both directions retain the key at each individual
step, including the head that starts the path; normalization is never used at
a different key from the one for which its displacement was calculated.

This adapter preserves the original `RecursiveRows.Derives` judgment, rather
than proving a theorem only about the row problem obtained by re-encoding a
separately supplied guarded graph.

The executable entry point then checks the supplied coordinate/potential
certificate and returns an exact finite semilinear presentation when it
succeeds. It accepts the original row AST and does not require an external slot
enumeration, even when slot identifiers form an infinite type. `none` means
that this certificate family gives no answer; it does not reject the source
program. Certificate search and general guarded reachability remain outside
the theorem.
-/

namespace Yulang.CertifiedRowSummaries

open Directed (Occurrence raw)
open RecursiveRowGraph (Program Graph Reachable)
open FinitePointGuards (GuardedEdge GuardedGraph GuardedReachable)
open RowTransportNormalForm (normalize NormalForm)
open SemilinearWeights (Weight Semi Meaning)

variable {n : Nat} {Key Slot : Type}

def normalizeEdge [DecidableEq Key] (key : Key) (edge : RecursiveRowGraph.Edge n Key Slot) :
    GuardedEdge n Key Slot := ⟨edge.source, normalize key edge.program, edge.target⟩

def normalizeGraph [DecidableEq Key] (key : Key) (graph : Graph n Key Slot) : GuardedGraph n Key Slot :=
  graph.map (normalizeEdge key)

def normalizedProblem [DecidableEq Key] (key : Key) (problem : RecursiveRows.Problem n Key Slot) :
    GuardedGraph n Key Slot := normalizeGraph key (RecursiveRowGraph.compile problem)

theorem normalized_run [DecidableEq Key] (key : Key) (program : Program n Key)
    (input : Occurrence n Key) (sameKey : input.key = key) :
    (normalize key program).run input = Program.run program input := by
  rw [← sameKey]
  exact RowTransportNormalForm.normalize_run program input

theorem normal_preserves_key [DecidableEq Key] (normal : NormalForm n Key)
    (input output : Occurrence n Key) (execution : normal.run input = some output) :
    output.key = input.key :=
  Program.run_key (FinitePointGuards.encode normal) input output
    (by simpa only [FinitePointGuards.encode_run] using execution)

theorem reachable_normalizes [DecidableEq Key] (key : Key) (graph : Graph n Key Slot)
    {slot : Slot} {output : Occurrence n Key} (reached : Reachable graph slot output)
    (sameKey : output.key = key) : GuardedReachable (normalizeGraph key graph) slot output := by
  induction reached with
  | @head output original program target declared execution =>
      have headKey : original = key := (Program.run_key program (raw original) output execution).symm.trans sameKey
      exact .head (List.mem_map.mpr ⟨⟨.head original, program, target⟩, declared, rfl⟩)
        (by rw [normalized_run key program (raw original) headKey]; exact execution)
  | @step input output source target program declared reached execution ih =>
      have inputKey : input.key = key := (Program.run_key program input output execution).symm.trans sameKey
      exact .step (List.mem_map.mpr ⟨⟨.slot source, program, target⟩, declared, rfl⟩) (ih inputKey)
        (by rw [normalized_run key program input inputKey]; exact execution)

theorem normalized_reaches [DecidableEq Key] (key : Key) (graph : Graph n Key Slot)
    {slot : Slot} {output : Occurrence n Key}
    (reached : GuardedReachable (normalizeGraph key graph) slot output)
    (sameKey : output.key = key) : Reachable graph slot output := by
  induction reached with
  | @head output original normal target declared execution =>
      have headKey : original = key := (normal_preserves_key normal (raw original) output execution).symm.trans sameKey
      obtain ⟨edge, member, equality⟩ := List.mem_map.mp declared
      rcases edge with ⟨source, program, destination⟩
      cases equality
      exact .head member (by rw [← normalized_run key program (raw original) headKey]; exact execution)
  | @step input output source target normal declared reached execution ih =>
      have inputKey : input.key = key := (normal_preserves_key normal input output execution).symm.trans sameKey
      obtain ⟨edge, member, equality⟩ := List.mem_map.mp declared
      rcases edge with ⟨origin, program, destination⟩
      cases equality
      exact .step member (ih inputKey)
        (by rw [← normalized_run key program input inputKey]; exact execution)

/-- Exactness is pointwise at the selected key; no global equality between
normalizations for different operation keys is assumed. -/
theorem normalized_reachable_exact [DecidableEq Key] (key : Key) (graph : Graph n Key Slot)
    (slot : Slot) (output : Occurrence n Key) (sameKey : output.key = key) :
    GuardedReachable (normalizeGraph key graph) slot output ↔ Reachable graph slot output :=
  ⟨fun reached => normalized_reaches key graph reached sameKey,
    fun reached => reachable_normalizes key graph reached sameKey⟩

theorem normalized_derives_exact [DecidableEq Key] (key : Key)
    (problem : RecursiveRows.Problem n Key Slot) (slot : Slot)
    (output : Occurrence n Key) (sameKey : output.key = key) :
    GuardedReachable (normalizedProblem key problem) slot output ↔ RecursiveRows.Derives problem slot output :=
  (normalized_reachable_exact key _ slot output sameKey).trans
    (RecursiveRowGraph.reachable_iff_derives problem slot output)

/-- Re-encoding the normalized graph does not change the original problem's
least solution at the selected key, despite changing its surface syntax. -/
theorem encoded_derives_exact [DecidableEq Key] (key : Key)
    (problem : RecursiveRows.Problem n Key Slot) (slot : Slot)
    (output : Occurrence n Key) (sameKey : output.key = key) :
    RecursiveRows.Derives (FinitePointGuards.rowProblem (normalizedProblem key problem)) slot output ↔
      RecursiveRows.Derives problem slot output :=
  (FinitePointGuards.guarded_graph_exact _ slot output).symm.trans
    (normalized_derives_exact key problem slot output sameKey)

def summary [DecidableEq Key] [DecidableEq Slot] (problem : RecursiveRows.Problem n Key Slot)
    (key : Key) (slot : Slot) : Semi n :=
  GuardedAffineRows.summary (normalizedProblem key problem) key slot

theorem summary_exact [DecidableEq Key] [DecidableEq Slot]
    (problem : RecursiveRows.Problem n Key Slot) (key : Key) (coordinate : Fin n)
    (potential : Slot → Int)
    (certified : GuardedAffineRows.Certified (normalizedProblem key problem) key coordinate potential)
    (slot : Slot) (weights : Weight n) :
    Meaning (summary problem key slot) weights ↔ RecursiveRows.Derives problem slot ⟨key, weights⟩ :=
  (GuardedAffineRows.summary_exact (normalizedProblem key problem) key coordinate potential certified slot weights).trans
    (encoded_derives_exact key problem slot ⟨key, weights⟩ rfl)

def checkedSummary [DecidableEq Key] [DecidableEq Slot] (problem : RecursiveRows.Problem n Key Slot)
    (key : Key) (coordinate : Fin n) (potential : Slot → Int) (slot : Slot) : Option (Semi n) :=
  match GuardedAffineRows.checkedSummary (normalizedProblem key problem) key coordinate potential slot with
  | .unsupported => none
  | .summarized semi => some semi

theorem checkedSummary_result [DecidableEq Key] [DecidableEq Slot]
    (problem : RecursiveRows.Problem n Key Slot) (key : Key) (coordinate : Fin n)
    (potential : Slot → Int) (slot : Slot) (semi : Semi n) :
    checkedSummary problem key coordinate potential slot = some semi ↔
      GuardedAffineRows.check (normalizedProblem key problem) key coordinate potential = true ∧
        summary problem key slot = semi := by
  have conversion : checkedSummary problem key coordinate potential slot = some semi ↔
      GuardedAffineRows.checkedSummary (normalizedProblem key problem) key coordinate potential slot =
        .summarized semi := by
    unfold checkedSummary
    cases GuardedAffineRows.checkedSummary (normalizedProblem key problem) key coordinate potential slot <;> simp
  exact conversion.trans (GuardedAffineRows.checkedSummary_exact
    (normalizedProblem key problem) key coordinate potential slot semi)

theorem checkedSummary_supported_iff [DecidableEq Key] [DecidableEq Slot]
    (problem : RecursiveRows.Problem n Key Slot) (key : Key) (coordinate : Fin n)
    (potential : Slot → Int) (slot : Slot) :
    (∃ semi, checkedSummary problem key coordinate potential slot = some semi) ↔
      GuardedAffineRows.Certified (normalizedProblem key problem) key coordinate potential := by
  constructor
  · rintro ⟨semi, accepted⟩
    exact (GuardedAffineRows.check_exact _ _ _ _).mp
      ((checkedSummary_result problem key coordinate potential slot semi).mp accepted).1
  · intro certified
    exact ⟨summary problem key slot,
      (checkedSummary_result problem key coordinate potential slot _).mpr
        ⟨(GuardedAffineRows.check_exact _ _ _ _).mpr certified, rfl⟩⟩

/-- The original row problem, finite normalization, certificate check and
semilinear compiler are connected without an external guard-safety hypothesis
or an enumeration of all slot names. Every integer vector is covered. -/
theorem checkedSummary_derives [DecidableEq Key] [DecidableEq Slot]
    (problem : RecursiveRows.Problem n Key Slot) (key : Key) (coordinate : Fin n)
    (potential : Slot → Int) (slot : Slot) (semi : Semi n)
    (accepted : checkedSummary problem key coordinate potential slot = some semi) (weights : Weight n) :
    Meaning semi weights ↔ RecursiveRows.Derives problem slot ⟨key, weights⟩ := by
  obtain ⟨checked, same⟩ := (checkedSummary_result problem key coordinate potential slot semi).mp accepted
  rw [← same]
  exact summary_exact problem key coordinate potential
    ((GuardedAffineRows.check_exact _ _ _ _).mp checked) slot weights

namespace Examples

/-- This is a direct row-AST input, with an infinite type of slot identifiers.
Both cycles contain ordinary residuals, and the seed protects another boundary. -/
def source : RecursiveRows.Problem 2 Nat Nat :=
  [⟨40, .protect 0 Directed.allowNone (.head 0)⟩,
   ⟨40, .protect 1 Directed.allowNone (.residual [0] (.var 40))⟩,
   ⟨40, .release 1 Directed.allowNone (.residual [0] (.var 40))⟩]

def potential : Nat → Int := fun _ => 1

theorem source_certificate_passes :
    GuardedAffineRows.check (normalizedProblem 0 source) 0 0 potential = true := by decide

theorem source_guards_remain_nonempty :
    ((normalizedProblem 0 source).drop 1).all (fun edge => !edge.transport.excluded.isEmpty) = true := by decide

theorem source_summary_returned :
    checkedSummary source 0 0 potential 40 = some (summary source 0 40) :=
  (checkedSummary_result source 0 0 potential 40 _).mpr ⟨source_certificate_passes, rfl⟩

theorem source_summary_exact (weights : Weight 2) :
    Meaning (summary source 0 40) weights ↔ RecursiveRows.Derives source 40 ⟨0, weights⟩ :=
  checkedSummary_derives source 0 0 potential 40 _ source_summary_returned weights

theorem source_seed_present :
    Meaning (summary source 0 40) (Directed.protect 0 Directed.allowNone (raw 0)).weights := by
  apply (source_summary_exact _).mpr
  exact .rule (rule := ⟨40, .protect 0 Directed.allowNone (.head 0)⟩)
    (by simp [source]) (.protect (.head 0))

end Examples

end Yulang.CertifiedRowSummaries
