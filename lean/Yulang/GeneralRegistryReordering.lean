import Yulang.GeneralDeclarationDemands

/-!
# General visible and where enumeration reordering

Only list positions change. Declaration IDs, clause IDs, every named equation,
output binder, head and role signature are retained. Multiplicity is retained.
This is the concrete registry relation for I-18 item 5, independent of resolver
results, candidate inspection, and model evidence.
-/
namespace Yulang.GeneralRegistryReordering
open GeneralDeclarations

/-- A visible declaration may move, and its source where clauses may move.
No fields, named equations, binders or source identities may change. -/
structure DeclarationReorders (first last : Declaration) : Prop where
  id : first.id = last.id
  role : first.role = last.role
  head : first.head = last.head
  requirements : first.requirements.Perm last.requirements
  associated : first.associated = last.associated
  outputBinders : first.outputBinders = last.outputBinders

theorem declarationReorders_refl (declaration : Declaration) :
    DeclarationReorders declaration declaration := ⟨rfl, rfl, rfl, List.Perm.refl _, rfl, rfl⟩

theorem declarationReorders_symm (order : DeclarationReorders first last) :
    DeclarationReorders last first :=
  ⟨order.id.symm, order.role.symm, order.head.symm, order.requirements.symm,
    order.associated.symm, order.outputBinders.symm⟩

theorem declarationReorders_trans (ab : DeclarationReorders first middle)
    (bc : DeclarationReorders middle last) : DeclarationReorders first last :=
  ⟨ab.id.trans bc.id, ab.role.trans bc.role, ab.head.trans bc.head,
    ab.requirements.trans bc.requirements, ab.associated.trans bc.associated,
    ab.outputBinders.trans bc.outputBinders⟩

/-- Visible enumeration and where enumeration only. Constructors and role
signatures are identical. The intermediate list retains multiplicity. -/
def Reorders (first last : Registry) : Prop :=
  first.constructors = last.constructors ∧ first.roles = last.roles ∧
    ∃ middle, first.declarations.Perm middle ∧
      CommonRoleOutermostResolver.All₂ DeclarationReorders middle last.declarations

theorem reorders_refl (registry : Registry) : Reorders registry registry := by
  refine ⟨rfl, rfl, registry.declarations, List.Perm.refl _, ?_⟩
  induction registry.declarations with
  | nil => exact .nil
  | cons declaration rest ih => exact .cons (declarationReorders_refl declaration) ih


/-- Moving source clauses does not change any independent declaration check. -/
theorem checked_permute_requirements (declaration : Declaration) (requirements : List Clause)
    (order : declaration.requirements.Perm requirements)
    (checked : DeclarationChecked constructors roles declaration) :
    DeclarationChecked constructors roles { declaration with requirements := requirements } := by
  constructor
  · exact ⟨checked.signature.1, checked.signature.2.1, checked.signature.2.2.1,
      fun clause member => checked.signature.2.2.2 clause (order.mem_iff.mpr member)⟩
  · exact ⟨(order.map Clause.id).nodup checked.identified.1,
      checked.identified.2.1, checked.identified.2.2.1, checked.identified.2.2.2.1,
      fun clause member => checked.identified.2.2.2.2 clause (order.mem_iff.mpr member)⟩
  · intro binder member
    obtain ⟨clause, present, same, equation, output, identity, rhs⟩ := checked.produced binder member
    exact ⟨clause, order.mem_iff.mp present, same, equation, output, identity, rhs⟩
  · exact ⟨checked.outputOnly.1,
      fun clause member => checked.outputOnly.2 clause (order.mem_iff.mpr member)⟩
  · exact ⟨fun clause member => checked.scope.1 clause (order.mem_iff.mpr member),
      checked.scope.2.1, fun clause member => checked.scope.2.2 clause (order.mem_iff.mpr member)⟩
  · exact ⟨checked.constructorScoped.1,
      (fun clause member => checked.constructorScoped.2.1 clause (order.mem_iff.mpr member)),
      checked.constructorScoped.2.2⟩
  · exact fun clause member => checked.countsCovered clause (order.mem_iff.mpr member)
  · exact fun clause member => checked.paterson clause (order.mem_iff.mpr member)
  · exact fun clause member => checked.conservative clause (order.mem_iff.mpr member)
  · exact fun clause member => checked.captureStable clause (order.mem_iff.mpr member)


/-- All unchanged declaration fields are literal equalities, not just keys. -/
theorem declarationReorders_update (order : DeclarationReorders first last) :
    last = { first with requirements := last.requirements } := by
  cases first with
  | mk id role head requirements associated outputBinders =>
    cases last with
    | mk id' role' head' requirements' associated' outputBinders' =>
      rcases order with ⟨idEq, roleEq, headEq, _, associatedEq, outputEq⟩
      cases idEq; cases roleEq; cases headEq; cases associatedEq; cases outputEq
      rfl

theorem declarationReorders_checked (order : DeclarationReorders first last) :
    DeclarationChecked constructors roles first ↔ DeclarationChecked constructors roles last := by
  constructor
  · intro checked
    have moved := checked_permute_requirements first last.requirements order.requirements checked
    simpa only [← declarationReorders_update order] using moved
  · intro checked
    have moved := checked_permute_requirements last first.requirements order.requirements.symm checked
    simpa only [← declarationReorders_update (declarationReorders_symm order)] using moved

private theorem related_member {relation : α → β → Prop}
    (related : CommonRoleOutermostResolver.All₂ relation first last) (member : value ∈ first) :
    ∃ other ∈ last, relation value other := by
  induction related with
  | nil => cases member
  | cons pair rest ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_, List.mem_cons_self, pair⟩
    · obtain ⟨other, present, related⟩ := ih member
      exact ⟨other, List.mem_cons_of_mem _ present, related⟩

private theorem related_ids (related : CommonRoleOutermostResolver.All₂ DeclarationReorders first last) :
    first.map Declaration.id = last.map Declaration.id := by
  induction related with
  | nil => rfl
  | cons pair rest ih => simp only [List.map_cons, pair.id, ih]

theorem reorders_visible (order : Reorders first last)
    (declaration : Declaration) (present : declaration ∈ first.declarations) :
    ∃ other ∈ last.declarations, DeclarationReorders declaration other := by
  obtain ⟨_, _, middle, permuted, related⟩ := order
  exact related_member related (permuted.mem_iff.mp present)

theorem reorders_declaration_ids (order : Reorders first last) :
    (first.declarations.map Declaration.id).Perm (last.declarations.map Declaration.id) := by
  obtain ⟨_, _, middle, permuted, related⟩ := order
  rw [← related_ids related]
  exact permuted.map Declaration.id

private theorem reverse_related {relation : α → β → Prop}
    (related : CommonRoleOutermostResolver.All₂ relation xs ys) :
    CommonRoleOutermostResolver.All₂ (fun b a => relation a b) ys xs := by
  induction related with
  | nil => exact .nil
  | cons pair rest ih => exact .cons pair ih

/-- A backward visible membership witness, not merely equal set of keys. -/
theorem reorders_visible_back (order : Reorders first last)
    (declaration : Declaration) (present : declaration ∈ last.declarations) :
    ∃ other ∈ first.declarations, DeclarationReorders other declaration := by
  obtain ⟨_, _, middle, permuted, related⟩ := order
  have reverse : CommonRoleOutermostResolver.All₂ (fun a b => DeclarationReorders b a) last.declarations middle := by
    exact reverse_related related
  obtain ⟨other, member, pair⟩ := related_member reverse present
  exact ⟨other, permuted.mem_iff.mpr member, pair⟩

/-- Every constructor/signature/scope/Paterson/capture-stability obligation is
preserved. This is not resolver order independence. -/
theorem reorders_checked (order : Reorders first last) (checked : Checked first) : Checked last := by
  constructor
  · exact (reorders_declaration_ids order).nodup checked.1
  · intro declaration present
    obtain ⟨other, member, pair⟩ := reorders_visible_back order declaration present
    have moved := (declarationReorders_checked pair).mp (checked.2 other member)
    rw [order.1, order.2.1] at moved
    exact moved

end Yulang.GeneralRegistryReordering
