import Yulang.GeneralDeclarativeI65I74StructuralWhereSiblingReceipts433

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.WhereAssociated432
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration Clause DeclarationChecked)
open GeneralDeclarativeFrameReadback325 (placeById sourceNames)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeSourceEmission322 (demand)
open GeneralDeclarativeEmissionForest322 (Placement children)

/-- The active declaration check's unique source clause IDs are the
reason an ID lookup is invariant under reordering, rather than lookup
accidentally picking a different first occurrence. -/
private theorem lookupId_injective433 {clauses : List Clause}
    (unique : (clauses.map Clause.id).Nodup)
    {a b : Clause} (ha : a ∈ clauses) (hb : b ∈ clauses) (key : a.id = b.id) : a = b := by
  induction clauses with
  | nil => simp at ha
  | cons hd tail ih =>
    obtain ⟨outside,inside⟩ := List.nodup_cons.mp unique
    rcases List.mem_cons.mp ha with rfl|aTail
    · rcases List.mem_cons.mp hb with rfl|bTail
      · rfl
      · exact False.elim (outside (List.mem_map.mpr ⟨b,bTail,key.symm⟩))
    · rcases List.mem_cons.mp hb with rfl|bTail
      · exact False.elim (outside (List.mem_map.mpr ⟨a,aTail,key⟩))
      · exact ih inside aTail bTail

private theorem same_looked_up_clause_under_permutation433 {first later : List Clause}
    (permuted : first.Perm later) (unique : (first.map Clause.id).Nodup) (id : Nat) :
    first.find? (fun cl => cl.id == id) = later.find? (fun cl => cl.id == id) := by
  cases hf : first.find? (fun cl => cl.id == id) with
  | none =>
    exact (List.find?_eq_none.mpr
      (fun a inLater => (List.find?_eq_none.mp hf) a (permuted.mem_iff.mpr inLater))).symm
  | some a =>
    have aIn := List.mem_of_find?_eq_some hf
    have aId : a.id = id := beq_iff_eq.mp (List.find?_some (p := fun c : Clause => c.id == id) (a := a) hf)
    cases hl : later.find? (fun cl => cl.id == id) with
    | none =>
      exact False.elim ((List.find?_eq_none.mp hl) a (permuted.mem_iff.mp aIn) (beq_iff_eq.mpr aId))
    | some b =>
      have bIn := permuted.mem_iff.mpr (List.mem_of_find?_eq_some hl)
      have bId : b.id = id := beq_iff_eq.mp (List.find?_some (p := fun c : Clause => c.id == id) (a := b) hl)
      exact congrArg some (lookupId_injective433 unique aIn bIn (aId.trans bId.symm))

/-- Reordering genuine where clauses does not reallocate old named
output binder targets when source clause IDs are unique and the
per-clause placement/input rules stay fixed. This is lexical/source
readback, not solver execution or a stability claim. -/
theorem checked_where_permutation_keeps_lexical_binder_targets433
    {constructors roles} {decl : Declaration}
    (checked : DeclarationChecked constructors roles decl)
    (next : List Clause) (permuted : decl.requirements.Perm next)
    (placement : Placement) (base : Nat → Capture) :
    sourceNames {decl with requirements := next} placement base =
      sourceNames decl placement base := by
  have addresses : placeById {decl with requirements := next} placement = placeById decl placement := by
    funext key eq
    unfold placeById
    rw [same_looked_up_clause_under_permutation433 permuted checked.identified.1 key]
  unfold sourceNames
  rw [addresses]
  rfl

/-- Pure original-demand transport. The role, inputs and named fixed
targets stay identical for the same authored clause; the occurrence
path follows the new original ordinal. No synthetic child is read. -/
theorem same_source_where_clause_keeps_demand_under_permutation433
    {s s' : GeneralDeclarativeI65.State} {q : Request}
    (before : AuthoredBodyFrame393 s q) (after : AuthoredBodyFrame393 s' q)
    {constructors roles} (checked : DeclarationChecked constructors roles before.decl)
    (sameDeclaration : after.decl = {before.decl with requirements := after.decl.requirements})
    (permuted : before.decl.requirements.Perm after.decl.requirements)
    (samePlacement : after.placement = before.placement) (sameInput : after.input = before.input)
    {clause : Clause} {i j : Nat}
    (original : before.decl.requirements[i]? = some clause)
    (moved : after.decl.requirements[j]? = some clause) :
    (frameWhereKids400 before)[i]? = some ⟨q.occurrence ++ [i],(before.whereFor clause).demand⟩ ∧
    (frameWhereKids400 after)[j]? = some ⟨q.occurrence ++ [j],(before.whereFor clause).demand⟩ := by
  have beforeHere : (before.clauses.map LiteralWhereEntry.demand)[i]? = some (before.whereFor clause).demand := by
    simp [AuthoredBodyFrame393.clauses,original]
  have afterHere : (after.clauses.map LiteralWhereEntry.demand)[j]? = some (after.whereFor clause).demand := by
    simp [AuthoredBodyFrame393.clauses,moved]
  have names : after.names = before.names := by
    unfold AuthoredBodyFrame393.names
    rw [samePlacement,sameInput]
    exact (congrArg (fun d => sourceNames d before.placement before.input) sameDeclaration).trans
      (checked_where_permutation_keeps_lexical_binder_targets433 checked _ permuted _ _)
  have dEq : (after.whereFor clause).demand = (before.whereFor clause).demand := by
    unfold AuthoredBodyFrame393.whereFor
    simp only [names,samePlacement]
    rw [sameDeclaration]
    have commonOutputs :
        GeneralDeclarativeSourceEmission322.useOutput
          {before.decl with requirements := after.decl.requirements} before.names (before.placement.targets clause) =
        GeneralDeclarativeSourceEmission322.useOutput
          before.decl before.names (before.placement.targets clause) := by
      funext eq
      unfold GeneralDeclarativeSourceEmission322.useOutput GeneralDeclarationDemands.outputTarget
      cases GeneralDeclarationPatterns.normalize eq.rhs <;> rfl
    simp only [demand,commonOutputs]
  unfold frameWhereKids400 children
  constructor
  · rw [List.getElem?_map,List.getElem?_zipIdx]; simp [beforeHere]
  · rw [List.getElem?_map,List.getElem?_zipIdx]; simp [afterHere,dEq]

end Yulang.GeneralDeclarativeI65.I72.WhereAssociated432
