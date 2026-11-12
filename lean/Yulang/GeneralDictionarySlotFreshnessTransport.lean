import Yulang.GeneralDictionaryNominalSlotTransport
import Yulang.GeneralNominalAllocation

/-!
# Allocation freshness across certified coordinate-bounded slot transport

A separate bound limits every target type and row coordinate to an old mixed
source or an ID below the persistent seed. This suffices to preserve allocation
freshness, since generated identities are above that seed. It does not authorize
new type coordinates, construct an allocator, or relate normalized views.
-/
namespace Yulang.GeneralDictionarySlotFreshnessTransport
open GeneralDictionaryNominalSlotTransport (Transport)
open GeneralNominalState (sources)
open GeneralNominalAllocation (source Fresh Origin)
open GeneralDeclarations (Registry)
variable {before after : GeneralNominalState.State}

/-- Mixed-source membership is only a collision bound, not type-slot authority.
Type and row coordinates each have their own obligation. -/
def CoordinatesBound (before after : GeneralNominalState.State) : Prop :=
  (∀ slot, after.base.source slot ∈ sources before ∨ after.base.source slot ≤ before.seed) ∧
  (∀ slot, after.base.rowSource slot ∈ sources before ∨ after.base.rowSource slot ≤ before.seed)

/-- Every old mixed source remains present, including ordinary mentions. -/
theorem sources_preserved (transport : Transport before after) (identity : Nat)
    (member : identity ∈ sources before) : identity ∈ sources after := by
  simp only [sources, List.mem_append, List.mem_ofFn] at member ⊢
  rcases member with ((⟨slot, rfl⟩ | ⟨slot, rfl⟩) | reserved) | ordinary
  · exact Or.inl (Or.inl (Or.inl ⟨transport.embed slot, transport.source slot⟩))
  · exact Or.inl (Or.inl (Or.inr ⟨transport.embed slot, transport.rowSource slot⟩))
  · exact Or.inl (Or.inr (transport.reserved ▸ reserved))
  · exact Or.inr (transport.ordinary ▸ ordinary)

/-- No new above-seed mixed source appears outside the old source list. -/
theorem sources_bounded (transport : Transport before after) (bound : CoordinatesBound before after)
    (identity : Nat) (member : identity ∈ sources after) :
    identity ∈ sources before ∨ identity ≤ before.seed := by
  simp only [sources, List.mem_append, List.mem_ofFn] at member
  rcases member with ((⟨slot, rfl⟩ | ⟨slot, rfl⟩) | reserved) | ordinary
  · exact bound.1 slot
  · exact bound.2 slot
  · apply Or.inl
    simp only [sources, List.mem_append]
    exact Or.inl (Or.inr (transport.reserved ▸ reserved))
  · apply Or.inl
    simp only [sources, List.mem_append]
    exact Or.inr (transport.ordinary ▸ ordinary)

/-- Seed retention preserves every generated origin identity exactly. -/
theorem allocation_source (transport : Transport before after) (registry : Registry) (root : Nat) (key : Origin) :
    source after registry root key = source before registry root key := by
  simp only [source, transport.seed]

/-- Above-seed generated identities have precisely the same collision status. -/
theorem generated_member_iff (transport : Transport before after) (bound : CoordinatesBound before after)
    (registry : Registry) (root : Nat) (key : Origin) :
    source after registry root key ∈ sources after ↔ source before registry root key ∈ sources before := by
  rw [allocation_source transport]
  constructor
  · intro member
    rcases sources_bounded transport bound _ member with old | below
    · exact old
    · exact False.elim (GeneralNominalAllocation.source_initial_fresh before registry root key _ below rfl)
  · exact sources_preserved transport _

/-- Both directions preserve the same origins and ownership list. -/
theorem fresh_iff (transport : Transport before after) (bound : CoordinatesBound before after)
    (registry : Registry) (root : Nat) : Fresh after registry root ↔ Fresh before registry root := by
  constructor
  · intro fresh key member collision
    have owned := fresh key member ((generated_member_iff transport bound registry root key).mpr collision)
    simpa only [transport.allocated] using owned
  · intro fresh key member collision
    have owned := fresh key member ((generated_member_iff transport bound registry root key).mp collision)
    simpa only [transport.allocated] using owned

/-- An unowned listed origin cannot acquire a collision under this transport. -/
theorem unowned_generated_absent (transport : Transport before after) (bound : CoordinatesBound before after)
    (registry : Registry) (root : Nat) (fresh : Fresh before registry root)
    (key : Origin) (listed : key ∈ GeneralNominalAllocation.keys registry root)
    (unowned : key ∉ before.allocated) : source after registry root key ∉ sources after := by
  apply GeneralNominalAllocation.source_fresh after registry root
    ((fresh_iff transport bound registry root).mpr fresh) key listed
  simpa only [transport.allocated] using unowned

end Yulang.GeneralDictionarySlotFreshnessTransport
