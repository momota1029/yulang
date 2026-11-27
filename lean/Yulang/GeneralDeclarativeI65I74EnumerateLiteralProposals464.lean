import Yulang.GeneralDeclarativeI65I74ExactSourceProposal464

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.NamedProjection464
open GeneralDeclarativeHead320 (Equation)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open Derivation (EqWire checkEq)
private abbrev RawState := GeneralDeclarativeHead320.State

/-- Search only the physically present old ordinary equations at a supplied
constructor context. Stable order is ordinal order. Two matching old payload
rows, even with the same logical name, are two source choices, not a display
or solver decision. This enumerator allocates no names. -/
def allLiteralProposals (s : RawState) (owner : Nat) (frames : List SelectedFrame) :
    List (Nat × Equation) :=
  (List.range s.equations.length).filterMap fun j =>
    (readSourceProposal s ⟨owner,j,frames⟩).map (fun e => (j,e))

theorem ordered_literal_proposals_iff_exact_actual_original_equations
    (s : RawState) (owner : Nat) (frames : List SelectedFrame) (i : Nat) (out : Equation) :
    (i,out) ∈ allLiteralProposals s owner frames ↔
      ExactSourceProposal s ⟨owner,i,frames⟩ out := by
  rw [← checked_proposal_is_exact_original_syntax_and_ordinals]
  constructor
  · intro mem
    obtain ⟨j,_,h⟩ := List.mem_filterMap.mp mem
    obtain ⟨e,r,equal⟩ := Option.map_eq_some_iff.mp h
    cases equal
    exact r
  · intro found
    obtain ⟨parent,payload,ro,rp,text,result⟩ :=
      (checked_proposal_is_exact_original_syntax_and_ordinals ..).mp found
    have lt := List.getElem?_eq_some_iff.mp rp |>.choose
    exact List.mem_filterMap.mpr ⟨i,List.mem_range.mpr lt,by simp [found]⟩

theorem any_enumerated_proposal_already_carries_finite_equational_evidence
    {s : RawState} {owner i : Nat} {frames : List SelectedFrame} {out : Equation}
    (found : (i,out) ∈ allLiteralProposals s owner frames) :
    checkEq s (.variable out.left) out.right (literalSourceProofData ⟨owner,i,frames⟩) = true := by
  have picked := (ordered_literal_proposals_iff_exact_actual_original_equations ..).mp found
  exact source_proposal_emits_its_exact_finite_ordinary_proof
    ((checked_proposal_is_exact_original_syntax_and_ordinals ..).mpr picked)

theorem enumeration_preserves_all_passed_old_ordinals_in_order
    (s : RawState) (owner : Nat) (frames : List SelectedFrame) :
    (allLiteralProposals s owner frames).map Prod.fst =
      (List.range s.equations.length).filter
        (fun i => (readSourceProposal s ⟨owner,i,frames⟩).isSome) := by
  have go (indices : List Nat) :
      (indices.filterMap fun j => (readSourceProposal s ⟨owner,j,frames⟩).map (fun e => (j,e))).map Prod.fst =
      indices.filter (fun i => (readSourceProposal s ⟨owner,i,frames⟩).isSome) := by
    induction indices with
    | nil => rfl
    | cons i rest ih =>
      cases eq : readSourceProposal s ⟨owner,i,frames⟩ <;>
        simp [List.filterMap,eq,ih]
  exact go _

end Yulang.GeneralDeclarativeI65.I72.NamedProjection464
