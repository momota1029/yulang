import Yulang.CommonRoleFiniteAssociatedStable
import Yulang.CommonRoleSourceDescent

/-! Allocate every occurrence of a finite named associated-source graph.
This replaces caller-supplied slot maps for this carrier only. It does not
construct an unbounded where graph from arbitrary source syntax. -/
namespace Yulang.CommonRoleNamedAssociatedGraph
open CommonRoleFiniteAssociatedClosure
open CommonRoleSettledConstraints (State)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)

structure NamedOccurrence where
  receiver : Nat
  output : Nat
  name : Nat
  template : Inference.Base → Roles.Goal

abbrev Program := List NamedOccurrence

def identity (p : Program) (slot : Fin (2 * p.length)) : Nat :=
  let i : Fin p.length := ⟨slot.val / 2, by omega⟩
  if slot.val % 2 = 0 then p[i.val].receiver else p[i.val].output

def table (p : Program) : List Nat := List.ofFn (identity p)

theorem table_length (p : Program) : (table p).length = 2 * p.length := by simp [table]

def receiver (p : Program) (i : Fin p.length) : Fin (2 * p.length) := ⟨2 * i.val, by omega⟩
def output (p : Program) (i : Fin p.length) : Fin (2 * p.length) := ⟨2 * i.val + 1, by omega⟩

theorem receiver_identity (p : Program) (i : Fin p.length) :
    identity p (receiver p i) = p[i.val].receiver := by
  simp [identity, receiver, Nat.mul_div_right]

theorem output_identity (p : Program) (i : Fin p.length) :
    identity p (output p i) = p[i.val].output := by
  have div : (2 * i.val + 1) / 2 = i.val := by omega
  have rem : (2 * i.val + 1) % 2 = 1 := by omega
  simp [identity, output, div, rem]

def lowerOccurrence (p : Program) (i : Fin p.length) : Occurrence (2 * p.length) :=
  ⟨receiver p i, output p i, p[i.val].name, p[i.val].template⟩

def lower (p : Program) : Source (2 * p.length) :=
  ⟨identity p, (List.finRange p.length).map (lowerOccurrence p)⟩

/-- Completeness: every source occurrence is present; no allocation oracle. -/
theorem occurrence_present (p : Program) (i : Fin p.length) :
    lowerOccurrence p i ∈ (lower p).occurrences := by
  exact List.mem_map.mpr ⟨i, by simp, rfl⟩

/-- Soundness/provenance: every compiled occurrence comes from a source position. -/
theorem occurrence_origin (p : Program) (q : Occurrence (2 * p.length))
    (member : q ∈ (lower p).occurrences) :
    ∃ i : Fin p.length, q = lowerOccurrence p i := by
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp member
  exact ⟨i, rfl⟩

/-- The finite domain contains exactly the two original positions of every
source occurrence; this is not general dynamic-where closure. -/
theorem slot_origin (p : Program) (slot : Fin (2 * p.length)) :
    ∃ i : Fin p.length, slot = receiver p i ∨ slot = output p i := by
  let i : Fin p.length := ⟨slot.val / 2, by omega⟩
  refine ⟨i, ?_⟩
  by_cases even : slot.val % 2 = 0
  · left; apply Fin.ext; dsimp [receiver, i]; omega
  · right; apply Fin.ext; dsimp [output, i]; omega

/-- Literal source-table identity; cast only adjusts the proved table length. -/
def tableSlot (p : Program) (slot : Fin (2 * p.length)) : Fin (table p).length :=
  ⟨slot.val, by rw [table_length]; exact slot.isLt⟩

theorem table_source (p : Program) (slot : Fin (2 * p.length)) :
    CommonRoleSourceIdentity.source (table p) (tableSlot p slot) = identity p slot := by
  simp [CommonRoleSourceIdentity.source, table, tableSlot]

/-- All facts in the actual saturation have an original source slot position. -/
theorem generated_fact_origin (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (p : Program) (s : State (2 * p.length))
    (fact : Fact (2 * p.length)) (_member : fact ∈ saturate env roles wf (lower p) s) :
    ∃ i : Fin p.length, fact.1 = receiver p i ∨ fact.1 = output p i :=
  slot_origin p fact.1

/-- General named-graph exactness: arbitrary size, branching, cycles and old state. -/
theorem named_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (p : Program) (s : State (2 * p.length))
    (fact : Fact (2 * p.length)) :
    fact ∈ saturate env roles wf (lower p) s ↔ Derives env roles wf (lower p) s fact :=
  saturate_exact ..

/-- Computed finite capacity, not an external universe or path-length cutoff. -/
theorem named_capacity (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (p : Program) (s : State (2 * p.length)) :
    (saturate env roles wf (lower p) s).length ≤ 8 * p.length := by
  have h := saturate_capacity env roles wf (lower p) s
  omega

end Yulang.CommonRoleNamedAssociatedGraph
