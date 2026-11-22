import Yulang.GeneralDeclarativeNestedSeek332

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeAlternativeView333
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeLowerKnown321 (Alias alias_refl)
open GeneralNominalCenteredHeadMatExpressions (Expr)

structure Offer (s : State) (name : Nat) where
  owner : Nat
  rhs : Expr
  linked : Alias s name owner
  stored : (⟨owner,rhs⟩ : Equation) ∈ s.equations

abbrev Index (s : State) := ∀ n : Nat, List (Offer s n)

structure Link (s : State) where
  readAt : Nat
  owner : Nat
  given : Alias s readAt owner

def directLinks (s : State) (name : Nat) : Link s :=
  ⟨name,name,alias_refl name⟩

def offersFrom {s : State} (rows : List Equation) (supported : rows ⊆ s.equations)
    (name : Nat) (route : Link s) : List (Offer s name) :=
  if listed : route.readAt = name then
    rows.attach.filterMap fun entry =>
      if stored : entry.val.left = route.owner then
        some ⟨entry.val.left,entry.val.right,listed ▸ stored ▸ route.given,supported entry.property⟩
      else none
  else []

def ofTable {s : State} (rows : List Equation) (supported : rows ⊆ s.equations)
    (aliases : List (Link s)) : Index s :=
  fun n => (directLinks s n :: aliases).flatMap (offersFrom rows supported n)

theorem source_row {s : State} {valid : rows ⊆ s.equations} {route : Link s}
    (present : (⟨owner,rhs⟩ : Equation) ∈ rows) (atName : route.readAt = name)
    (stored : owner = route.owner) :
    ∃ entry ∈ offersFrom rows valid name route, entry.owner = owner ∧ entry.rhs = rhs := by
  refine ⟨⟨owner,rhs,atName ▸ stored ▸ route.given,valid present⟩,?_,rfl,rfl⟩
  simp only [offersFrom, dite_eq_left atName,List.mem_filterMap]
  refine ⟨⟨⟨owner,rhs⟩,present⟩, List.mem_attach ..,?_⟩
  simp [stored]

/-- Relative coverage of an independently available row, not
decidability of alias or completeness of the entire language. -/
def CoversRow (src : Index s) (name owner : Nat) (rhs : Expr) : Prop :=
  ∃ entry ∈ src name, entry.owner = owner ∧ entry.rhs = rhs

theorem covers_self {s : State} {valid : rows ⊆ s.equations} {aliases : List (Link s)}
    (present : (⟨n,rhs⟩ : Equation) ∈ rows) : CoversRow (ofTable rows valid aliases) n n rhs := by
  obtain ⟨offer,found,owner,body⟩ := source_row (valid := valid)
    (route := directLinks s n) present rfl rfl
  exact ⟨offer,List.mem_flatMap.mpr ⟨directLinks s n,List.mem_cons_self,found⟩,owner,body⟩

theorem covers_alias {s : State} {valid : rows ⊆ s.equations} {aliases : List (Link s)} {route : Link s}
    (listed : route ∈ aliases) (atName : route.readAt = n) (atOwner : owner = route.owner)
    (present : (⟨owner,rhs⟩ : Equation) ∈ rows) : CoversRow (ofTable rows valid aliases) n owner rhs := by
  obtain ⟨offer,found,origin,body⟩ := source_row (valid := valid) present atName atOwner
  exact ⟨offer,List.mem_flatMap.mpr ⟨route,List.mem_cons_of_mem _ listed,found⟩,origin,body⟩

def Covers (src : Index s) : Prop :=
  ∀ n owner rhs, Alias s n owner → (⟨owner,rhs⟩ : Equation) ∈ s.equations →
    CoversRow src n owner rhs

theorem exact_offer {s : State} {src : Index s} (seen : CoversRow src n owner rhs)
    (link : Alias s n owner) (stored : (⟨owner,rhs⟩ : Equation) ∈ s.equations) :
    (⟨owner,rhs,link,stored⟩ : Offer s n) ∈ src n := by
  obtain ⟨entry,inList,same,spells⟩ := seen
  rcases entry with ⟨place,raw,_,_⟩
  dsimp at same spells
  subst place raw
  exact inList

end Yulang.GeneralDeclarativeAlternativeView333
