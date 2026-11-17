import Yulang.GeneralPresenceOrderedBlock247

/-! Generic support certificates for actual ordered definition lists. A list
with distinct targets, none read by any RHS, is safe in its supplied order.
These helpers do not produce actual allocator freshness or endpoint coverage. -/
namespace Yulang.GeneralPresenceOrderedSupport247
open Core.PresenceGeneration
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOrderedBlock247
open GeneralPresenceUsedSupport245 (typedReads)

theorem safe_independent (entries : List (Entry Name))
    (distinct : (entries.map Prod.fst).Nodup)
    (unread : ∀ target ∈ entries, ∀ rhs ∈ entries, target.1 ∉ typedReads rhs.2) :
    SafeOrder entries := by
  induction entries with
  | nil => trivial
  | cons entry rest ih =>
    have split := List.nodup_cons.mp distinct
    refine ⟨unread entry (by simp) entry (by simp),?_,?_,?_⟩
    · intro later member same
      exact split.1 (List.mem_map.mpr ⟨later,member,same⟩)
    · intro later member
      exact unread later (List.mem_cons_of_mem _ member) entry (by simp)
    · exact ih split.2
        (fun target targetMem rhs rhsMem => unread target (List.mem_cons_of_mem _ targetMem)
          rhs (List.mem_cons_of_mem _ rhsMem))

theorem safe_pool (entries : List (Entry Name)) (pool : List Name)
    (distinct : (entries.map Prod.fst).Nodup)
    (protectedTargets : ∀ target ∈ entries, target.1 ∉ pool)
    (coveredReads : ∀ rhs ∈ entries, ∀ name ∈ typedReads rhs.2, name ∈ pool) :
    SafeOrder entries := by
  apply safe_independent entries distinct
  intro target targetMem rhs rhsMem read
  exact protectedTargets target targetMem (coveredReads rhs rhsMem target.1 read)

/-- Full typeSources coverage is sufficient but unnecessarily includes rows.
The typed-only version above still permits reads of private row coordinates. -/
theorem safe_full_sources_pool (entries : List (Entry Name)) (pool : List Name)
    (distinct : (entries.map Prod.fst).Nodup)
    (protectedTargets : ∀ target ∈ entries, target.1 ∉ pool)
    (coveredSources : ∀ rhs ∈ entries, ∀ name ∈ GeneralPresenceSubstitutionSupport244.typeSources rhs.2,
      name ∈ pool) : SafeOrder entries := by
  apply safe_pool entries pool distinct protectedTargets
  intro rhs member name read
  exact coveredSources rhs member name
    ((GeneralPresenceUsedSupport245.sources_split rhs.2 name).mpr (Or.inl read))

end Yulang.GeneralPresenceOrderedSupport247
