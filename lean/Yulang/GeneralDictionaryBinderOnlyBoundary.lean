import Yulang.GeneralDictionaryComputedTransactions

/-!
# Binder-only output interpretation cannot close a finite output-bearing tree

Every interpreted output is an output-only binder of the selected checked
visible declaration. Its required producer is an actual canonical child with
an output obligation. Induction on a complete Built tree therefore forces
empty output obligations at every root. This is a limitation of the present
partial interpreter, not a rejection theorem about the language.
-/
namespace Yulang.GeneralDictionaryBinderOnlyBoundary
open GeneralDeclarations GeneralDeclarationDemands GeneralSourceDictionaries
open GeneralDictionaryEmissionPlans GeneralDictionaryStateEquations
open GeneralDictionaryComputedOutputPlans GeneralDictionaryComputedTransactions
open GeneralDictionaryTransactions (Prepared Frames)
open GeneralDictionaryOutputBinderTerms (Interpreted)
open GeneralSourceState (State)

variable {roles : Roles.RoleDecls} {state : State}

/-- The producer child is in the actual canonical list, not an invented edge. -/
theorem output_requires_nonempty_child
    (declaration : Declaration) (checked : DeclarationChecked constructors roles declaration)
    (frame : Frame roles) (root : Occurrence roles) (located : Located state root.demand)
    (interpreted : Interpreted declaration (frame.capture declaration.id) located)
    (index : Fin root.demand.outputs.length) :
    ∃ child ∈ children frame root declaration checked, child.demand.outputs ≠ [] := by
  have denoted := (GeneralDictionaryOutputBinderTerms.lookup_exact roles declaration
    (frame.capture declaration.id) checked.identified.2.2.1 _ _).mp (interpreted index)
  obtain ⟨clause, present, equation, _, _, output⟩ :=
    GeneralDictionaryOutputBinderTerms.denotes_has_producer checked
      (frame.capture declaration.id) _ _ denoted (frame.allocation declaration.id)
  let emission := emit root.identity declaration clause (checked.signature.2.2.2 clause present)
    (frame.capture declaration.id) (frame.allocation declaration.id clause)
  have emitted : emission ∈ emitAll root.identity declaration checked.signature
      (frame.capture declaration.id) (frame.allocation declaration.id) := by
    apply List.mem_map.mpr
    exact ⟨⟨clause, present⟩, by simp, rfl⟩
  have canonical := (GeneralCanonicalChildOrder.canonicalEmit_perm root.identity declaration checked
    (frame.capture declaration.id) (frame.allocation declaration.id)).mem_iff.mp emitted
  refine ⟨occurrence frame emission, List.mem_map.mpr ⟨emission, canonical, rfl⟩, ?_⟩
  intro empty
  change (childDemand declaration clause (checked.signature.2.2.2 clause present)
    (frame.capture declaration.id) (frame.allocation declaration.id clause)).outputs = [] at empty
  rw [empty] at output
  exact List.not_mem_nil output

/-- No finite complete tree built by this binder-only interpreter can have an
output-bearing root, regardless of supplied head predicates or source frames. -/
theorem built_root_outputs_empty (registry : Registry) (checked : Checked registry)
    (frames : Frames registry.roles) (heads : HeadInstances registry.roles state)
    (tree : Prepared registry.roles state) (built : Built registry checked frames heads tree) :
    tree.root.demand.outputs = [] := by
  induction built with
  | @node root key inputs result children found head complete childrenBuilt ih =>
      change root.demand.outputs = []
      apply Classical.byContradiction
      intro nonempty
      have positive : 0 < root.demand.outputs.length := List.length_pos_iff.mpr nonempty
      obtain ⟨declaration, present, _, _, built, generated⟩ :=
        (lookup_exact registry checked (frames root) root key inputs result).mp found
      have interpreted := GeneralDictionaryBinderLocations.build_interpreted declaration
        ((frames root).capture declaration.id) inputs result.located built
      obtain ⟨child, member, hasOutput⟩ := output_requires_nonempty_child declaration
        (checked.2 declaration present) (frames root) root result.located interpreted ⟨0, positive⟩
      rw [← generated, ← complete] at member
      obtain ⟨subtree, subtreePresent, same⟩ := List.mem_map.mp member
      exact hasOutput (same ▸ ih subtree subtreePresent)

end Yulang.GeneralDictionaryBinderOnlyBoundary
