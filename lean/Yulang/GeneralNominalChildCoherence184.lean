import Yulang.GeneralNominalCenterCoherence184

/-! Allocation injectivity identifies the producer of two equal child sites.
This is a syntactic coherence lemma, not a global reachable-site invariant. -/
namespace Yulang.GeneralNominalChildCoherence184
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters

private theorem unique_key (key : α → Nat) (xs : List α)
    (unique : (xs.map key).Nodup) (a b : α) (left : a ∈ xs) (right : b ∈ xs)
    (same : key a = key b) : a = b := by
  induction xs with
  | nil => cases left
  | cons head rest ih =>
    have pair := List.nodup_cons.mp unique
    rcases List.mem_cons.mp left with equalA | tailA
    · subst a
      rcases List.mem_cons.mp right with equalB | tailB
      · subst b; rfl
      · exact False.elim (pair.1 (List.mem_map.mpr ⟨b,tailB,same.symm⟩))
    · rcases List.mem_cons.mp right with equalB | tailB
      · subst b
        exact False.elim (pair.1 (List.mem_map.mpr ⟨a,tailA,same⟩))
      · exact ih pair.2 tailA tailB

variable {roles : Roles.RoleDecls}

theorem producer_ids (first last : Plan roles)
    (seed : first.packet.context.state.seed = last.packet.context.state.seed)
    (one two : Clause) (oneSignature : one.Signature roles) (twoSignature : two.Signature roles)
    (same : (first.childSite one oneSignature).occurrence.identity =
      (last.childSite two twoSignature).occurrence.identity) :
    first.packet.site.occurrence.identity = last.packet.site.occurrence.identity ∧
    first.packet.declaration.id = last.packet.declaration.id ∧ one.id = two.id := by
  change fresh first.packet.context.state.seed first.packet.site.occurrence.identity
    first.packet.declaration.id 6 one.id 0 =
    fresh last.packet.context.state.seed last.packet.site.occurrence.identity
      last.packet.declaration.id 6 two.id 0 at same
  rw [seed] at same
  have identity := (GeneralNominalIdentities.source_identity last.packet.context.state.seed _ _).mp same
  exact ⟨congrArg Prod.fst identity,
    congrArg (fun key : GeneralNominalIdentities.Origin => key.2.1) identity,
    congrArg (fun key : GeneralNominalIdentities.Origin => key.2.2.2.1) identity⟩

theorem producer_declarations (registry : Registry) (checked : Checked registry)
    (first last : Plan roles)
    (seed : first.packet.context.state.seed = last.packet.context.state.seed)
    (firstVisible : first.packet.declaration ∈ registry.declarations)
    (lastVisible : last.packet.declaration ∈ registry.declarations)
    (one two : Clause) (oneMember : one ∈ first.packet.declaration.requirements)
    (twoMember : two ∈ last.packet.declaration.requirements)
    (oneSignature : one.Signature roles) (twoSignature : two.Signature roles)
    (same : (first.childSite one oneSignature).occurrence.identity =
      (last.childSite two twoSignature).occurrence.identity) :
    first.packet.site.occurrence.identity = last.packet.site.occurrence.identity ∧
    first.packet.declaration = last.packet.declaration ∧ one = two := by
  obtain ⟨invocation,declId,clauseId⟩ := producer_ids first last seed one two oneSignature twoSignature same
  have declaration := GeneralDictionaryEmissionPlans.declaration_key_unique registry checked
    first.packet.declaration last.packet.declaration firstVisible lastVisible declId
  refine ⟨invocation,declaration,?_⟩
  apply unique_key Clause.id first.packet.declaration.requirements first.packet.checked.identified.1
    one two oneMember
  · simpa only [declaration] using twoMember
  · exact clauseId

theorem site_eq_of_centers (first last : Site roles) (same : first.occurrence = last.occurrence)
    (centers : List.ofFn first.center = List.ofFn last.center) : first = last := by
  cases first with
  | mk occurrence center =>
    cases last with
    | mk other next =>
      dsimp only at same centers
      cases same
      have sameCenters : center = next := by
        funext index
        have atIndex := congrArg (fun values : List Nat => values[index.val]?) centers
        simpa only [List.getElem?_ofFn, dite_true, index.isLt, Option.some.injEq] using atIndex
      cases sameCenters
      rfl


theorem same_clause_site_equal (first last : Plan roles)
    (seed : first.packet.context.state.seed = last.packet.context.state.seed)
    (invocation : first.packet.site.occurrence.identity = last.packet.site.occurrence.identity)
    (declaration : first.packet.declaration = last.packet.declaration)
    (clause : Clause) (signature : clause.Signature roles)
    (same : (first.childSite clause signature).occurrence = (last.childSite clause signature).occurrence) :
    first.childSite clause signature = last.childSite clause signature := by
  apply site_eq_of_centers _ _ same
  apply congrArg List.ofFn
  funext index
  apply GeneralNominalCenterCoherence184.child_center_equal first last seed invocation declaration
  have args := congrArg (fun occurrence : Occurrence roles => List.ofFn occurrence.demand.arguments) same
  have atIndex := congrArg (fun values : List GeneralSourceState.Interval => values[index.val]?) args
  have lastBound : index.val < (roles (last.childSite clause signature).occurrence.demand.role).arity := index.isLt
  simp only [List.getElem?_ofFn, dite_eq_left index.isLt, dite_eq_left lastBound, Option.some.injEq] at atIndex
  have leftIndex : (⟨index.val,index.isLt⟩ : Fin (roles (first.childSite clause signature).occurrence.demand.role).arity) = index := Fin.ext rfl
  have rightIndex : (⟨index.val,lastBound⟩ : Fin (roles (last.childSite clause signature).occurrence.demand.role).arity) = index := Fin.ext rfl
  rw [leftIndex,rightIndex] at atIndex
  exact atIndex

theorem child_site_equal (registry : Registry) (checked : Checked registry)
    (first last : Plan roles)
    (seed : first.packet.context.state.seed = last.packet.context.state.seed)
    (firstVisible : first.packet.declaration ∈ registry.declarations)
    (lastVisible : last.packet.declaration ∈ registry.declarations)
    (one two : Clause) (oneMember : one ∈ first.packet.declaration.requirements)
    (twoMember : two ∈ last.packet.declaration.requirements)
    (oneSignature : one.Signature roles) (twoSignature : two.Signature roles)
    (same : (first.childSite one oneSignature).occurrence =
      (last.childSite two twoSignature).occurrence) :
    first.childSite one oneSignature = last.childSite two twoSignature := by
  obtain ⟨invocation,declaration,clauses⟩ := producer_declarations registry checked first last seed
    firstVisible lastVisible one two oneMember twoMember oneSignature twoSignature
    (congrArg Occurrence.identity same)
  subst two
  exact same_clause_site_equal first last seed invocation declaration one oneSignature same

end Yulang.GeneralNominalChildCoherence184
