import Yulang.GeneralNominalVersionedAllocation231

/-! A finite allocation cover relative to an explicitly supplied finite list
of capture-binding candidates. This is an allocation-layer auxiliary theorem:
it does NOT prove that all versions on an actual reachable trace have one
finite cover, and does NOT transport the old termination theorem. -/
namespace Yulang.GeneralNominalVersionedPool231
open GeneralDeclarations
open GeneralNominalAllocation (Bindings occurrences)
open GeneralNominalVersionedAllocation231

def keyPool (registry : Registry) (root : Nat) (candidates : List Bindings) :
    List GeneralNominalIdentities.Origin :=
  candidates.flatMap (keys registry root)

def sourcePool (state : GeneralNominalState.State) (registry : Registry) (root : Nat)
    (candidates : List Bindings) : List Nat :=
  (keyPool registry root candidates).map (GeneralNominalIdentities.source state.seed)

theorem keys_included (present : bindings ∈ candidates) :
    keys registry root bindings ⊆ keyPool registry root candidates := by
  intro key member
  exact List.mem_flatMap.mpr ⟨bindings,present,member⟩

theorem reserved_included (present : bindings ∈ candidates) :
    reserved state registry root bindings ⊆ sourcePool state registry root candidates := by
  intro name member
  obtain ⟨key,within,rfl⟩ := List.mem_map.mp member
  exact List.mem_map.mpr ⟨key,keys_included present within,rfl⟩

theorem keyPool_mono (included : first ⊆ last) :
    keyPool registry root first ⊆ keyPool registry root last := by
  intro key member
  obtain ⟨bindings,present,within⟩ := List.mem_flatMap.mp member
  exact List.mem_flatMap.mpr ⟨bindings,included present,within⟩

theorem sourcePool_mono (included : first ⊆ last) :
    sourcePool state registry root first ⊆ sourcePool state registry root last := by
  intro name member
  obtain ⟨key,present,rfl⟩ := List.mem_map.mp member
  exact List.mem_map.mpr ⟨key,keyPool_mono included present,rfl⟩

private theorem flatMap_congr (items : List α) (first last : α → List β)
    (same : ∀ item ∈ items, first item = last item) : items.flatMap first = items.flatMap last := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.flatMap_cons,same head (List.mem_cons_self ..)]
    rw [ih (fun item member => same item (List.mem_cons_of_mem _ member))]

theorem declarationKeys_revisit (same : ∀ name ∈ declaration.inputNames,
    occurrences first name = occurrences last name) :
    declarationKeys root declaration first = declarationKeys root declaration last := by
  unfold declarationKeys
  congr 2
  apply flatMap_congr
  intro name member
  rw [(GeneralNominalAggregateVersion231.key_eq_iff root declaration.id 0 name).mpr (same name member),
    (GeneralNominalAggregateVersion231.key_eq_iff root declaration.id 1 name).mpr (same name member)]

theorem keys_revisit (same : ∀ declaration ∈ registry.declarations, ∀ name ∈ declaration.inputNames,
    occurrences first name = occurrences last name) :
    keys registry root first = keys registry root last := by
  apply flatMap_congr
  intro declaration member
  exact declarationKeys_revisit (same declaration member)

theorem reserved_revisit (same : ∀ declaration ∈ registry.declarations, ∀ name ∈ declaration.inputNames,
    occurrences first name = occurrences last name) :
    reserved state registry root first = reserved state registry root last := by
  unfold reserved
  rw [keys_revisit same]

theorem sourcePool_seed (same : first.seed = last.seed) :
    sourcePool first registry root candidates = sourcePool last registry root candidates := by
  unfold sourcePool
  rw [same]

theorem sourcePool_propagate :
    sourcePool (propagate state registry root declaration bindings) registry root candidates =
      sourcePool state registry root candidates := rfl

/-- Membership in the stated finite candidate cover is a necessary explicit
premise here; deriving such a cover for the successor's traces is still open. -/
theorem reserved_covered (observed : Bindings → Prop) (cover : ∀ bindings, observed bindings → bindings ∈ candidates) :
    ∀ bindings, observed bindings → reserved state registry root bindings ⊆ sourcePool state registry root candidates :=
  fun bindings present => reserved_included (cover bindings present)

end Yulang.GeneralNominalVersionedPool231
