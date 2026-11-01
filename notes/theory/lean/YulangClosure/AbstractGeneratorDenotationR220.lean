import YulangClosure.OriginalSourceSyntax
import YulangClosure.SimpleSubRegularPublication

/-!
R220's frozen structural literal fragment. The code records the literal's
constructor, not its payload or a native identifier. The original raw literal
remains an input, with all eight payload carriers unchanged.

This is a local graph theorem, not an original-source interpretation. In
particular it supplies no endpoint allocation, Descriptor/Value/Root/Event
embedding, LiteralAtom, Return, or shared source witness. The original L1
bridge and SourceProblem.InferenceSoundness remain open: SourceAssignment.row
reads finalRoot, whereas synthesis and writtenTarget are distinct endpoints.
RegularPublication.decodeTerm also rejects unions and intersections; this
fragment does not restrict the source language or replace its full semantics.
-/
namespace YulangClosure.AbstractGeneratorDenotationR220

open SimpleSub SimpleSub.Regular SimpleSub.RegularPublication

def literalCode : OriginalSource.Literal → Nat
  | .unit => 0
  | .bool _ => 1
  | .int _ => 2
  | .floatBits _ => 3
  | .string _ => 4
  | .bytes _ => 5
  | .path _ => 6
  | .character _ => 7

def literalStructuralFragment (valueVar effectVar : Nat)
    (literal : OriginalSource.Literal) : Store :=
  [⟨.value, .atom (literalCode literal), .var valueVar⟩,
   ⟨.value, .var valueVar, .atom (literalCode literal)⟩,
   ⟨.effect, .var effectVar, .bottom⟩]

theorem node_atom_of_mutual_expansion {k : Kind} {node : Node k} {code : Nat}
    {forwardChildren reverseChildren : List Comparison}
    (forward : expandNodes (.atom code) node = some forwardChildren)
    (reverse : expandNodes node (.atom code) = some reverseChildren) :
    node = .atom code := by
  cases node with
  | atom other =>
      by_cases same : code = other
      · subst other
        rfl
      · simp [expandNodes, same] at forward
  | bottom => simp [expandNodes] at forward
  | top => simp [expandNodes] at reverse
  | function a ae re r => simp [expandNodes] at forward
  | record fields => simp [expandNodes] at forward
  | tuple elements => simp [expandNodes] at forward
  | variant alternatives => simp [expandNodes] at forward

/-- Mutual regular comparison with an atom fixes the target node, not its
reference index. Duplicate equal nodes in the graph remain permitted. -/
theorem atom_rigidity {graph : Graph} {k : Kind} {anchor target code : Nat}
    (anchorFound : graph.lookup k anchor = some (.atom code))
    (forward : RegularSub graph ⟨k, anchor, target⟩)
    (reverse : RegularSub graph ⟨k, target, anchor⟩) :
    graph.lookup k target = some (.atom code) := by
  rcases regular_unfold.mp forward with ⟨forwardChildren, forwardExpanded, _⟩
  rcases regular_unfold.mp reverse with ⟨reverseChildren, reverseExpanded, _⟩
  rcases (expand_endpoints_exist forwardExpanded).2 with ⟨node, nodeFound⟩
  have forwardNodes : expandNodes (.atom code) node = some forwardChildren := by
    simpa only [expand, anchorFound, nodeFound] using forwardExpanded
  have reverseNodes : expandNodes node (.atom code) = some reverseChildren := by
    simpa only [expand, nodeFound, anchorFound] using reverseExpanded
  have same := node_atom_of_mutual_expansion forwardNodes reverseNodes
  exact nodeFound.trans (congrArg some same)

/-- The upper bound bottom forces the referenced Effect node to bottom.
No opposite, vacuous lower bound is used. -/
theorem effect_bottom_rigidity {graph : Graph} {target empty : Nat}
    (emptyFound : graph.lookup .effect empty = some .bottom)
    (related : RegularSub graph ⟨.effect, target, empty⟩) :
    graph.lookup .effect target = some .bottom := by
  rcases regular_unfold.mp related with ⟨children, expanded, _⟩
  rcases (expand_endpoints_exist expanded).1 with ⟨node, nodeFound⟩
  have nodes : expandNodes node .bottom = some children := by
    simpa only [expand, nodeFound, emptyFound] using expanded
  cases node with
  | atom code => simp [expandNodes] at nodes
  | bottom => exact nodeFound
  | top => simp [expandNodes] at nodes

theorem clause_satisfied_decoded {graph : Graph} {refs : References}
    {clause : Constraint} (satisfied : ClauseSatisfied graph refs clause) :
    ∃ lower upper,
      decodeTerm graph refs clause.lower = some lower ∧
      decodeTerm graph refs clause.upper = some upper ∧
      RegularSub graph ⟨clause.kind, lower, upper⟩ := by
  rcases satisfied with ⟨pair, decoded, related⟩
  rcases bind_some decoded with ⟨lower, lowerDecoded, rest⟩
  rcases bind_some rest with ⟨upper, upperDecoded, assembled⟩
  have same : (⟨clause.kind, lower, upper⟩ : Comparison) = pair :=
    Option.some.inj assembled
  subst pair
  exact ⟨lower, upper, lowerDecoded, upperDecoded, related⟩

theorem decoded_var_index {graph : Graph} {refs : References} {k : Kind}
    {identity index : Nat}
    (decoded : decodeTerm graph refs (Term.var (k := k) identity) = some index) :
    index = refs k identity := by
  change checkedReference graph k (refs k identity) = some index at decoded
  cases found : graph.lookup k (refs k identity) with
  | none => simp [checkedReference, found] at decoded
  | some node =>
      have same : refs k identity = index := by
        simpa only [checkedReference, found, Option.some.injEq] using decoded
      exact same.symm

/-- Every satisfying assignment reads the exact coded atom and bottom at the
same two references supplied to the fragment. No graph-index equality or
original-source junction premise is assumed. -/
theorem literal_structural_readout (graph : Graph) (refs : References)
    (valueVar effectVar : Nat) (literal : OriginalSource.Literal)
    (satisfied : StoreSatisfied graph refs
      (literalStructuralFragment valueVar effectVar literal)) :
    graph.lookup .value (refs .value valueVar) =
        some (.atom (literalCode literal)) ∧
    graph.lookup .effect (refs .effect effectVar) = some .bottom := by
  have lowerSatisfied : ClauseSatisfied graph refs
      ⟨.value, .atom (literalCode literal), .var valueVar⟩ :=
    satisfied _ (by simp [literalStructuralFragment])
  have upperSatisfied : ClauseSatisfied graph refs
      ⟨.value, .var valueVar, .atom (literalCode literal)⟩ :=
    satisfied _ (by simp [literalStructuralFragment])
  have effectSatisfied : ClauseSatisfied graph refs
      ⟨.effect, .var effectVar, .bottom⟩ :=
    satisfied _ (by simp [literalStructuralFragment])
  rcases clause_satisfied_decoded lowerSatisfied with
    ⟨anchor, valueTarget, atomDecoded, valueDecoded, forward⟩
  rcases clause_satisfied_decoded upperSatisfied with
    ⟨valueTarget', anchor', valueDecoded', atomDecoded', reverse⟩
  rcases clause_satisfied_decoded effectSatisfied with
    ⟨effectTarget, empty, effectDecoded, emptyDecoded, effectRelated⟩
  have valueIndex : valueTarget = refs .value valueVar := decoded_var_index valueDecoded
  have valueIndex' : valueTarget' = refs .value valueVar := decoded_var_index valueDecoded'
  have effectIndex : effectTarget = refs .effect effectVar := decoded_var_index effectDecoded
  have atomIndex : anchor' = anchor := Option.some.inj (atomDecoded'.symm.trans atomDecoded)
  rw [valueIndex] at forward
  rw [valueIndex', atomIndex] at reverse
  rw [effectIndex] at effectRelated
  exact ⟨atom_rigidity (findNode_sound atomDecoded) forward reverse,
    effect_bottom_rigidity (findNode_sound emptyDecoded) effectRelated⟩

end YulangClosure.AbstractGeneratorDenotationR220
