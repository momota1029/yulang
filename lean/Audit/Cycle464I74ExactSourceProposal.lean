import Yulang.GeneralDeclarativeI65I74ExactSourceProposal464

namespace Yulang.GeneralDeclarativeI65.I72.NamedProjection464
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeWitnessLiteral349 (eqExpr)
open GeneralDeclarativeK2Graph321.AddAtOneSource
open List410 (ExactEscapeWire)
#print axioms derive_at_selected_frame
#print axioms every_finite_selected_context_preserves_ordinary_derivation
#print axioms checked_proposal_is_exact_original_syntax_and_ordinals
#print axioms exact_literal_source_proposal_has_an_old_derivation
#print axioms proposal_has_finite_original_equational_proof
#print axioms actual_source_proposal_and_safe_cut_give_exact_scoped_projection
#print axioms data_for_one_frame_replays_the_same_two_subterms
#print axioms data_for_every_finite_frame_list_replays_exactly
#print axioms source_proposal_emits_its_exact_finite_ordinary_proof

private def emptyRec : Expr := .primitive .emptyRecord []
private def childExpr : Expr := .record 40 (.variable 5) emptyRec
private def source : GeneralDeclarativeHead320.State :=
  ⟨⟨[],[]⟩,[⟨4,.record 30 childExpr emptyRec⟩,⟨5,childExpr⟩]⟩
private def selection : SourceRowSelection := ⟨0,1,[.recordPayload 30 emptyRec]⟩
private def proposedExpr : Expr := .record 30 (.variable 5) emptyRec
private def cut : ExactEscapeWire :=
  ⟨List.range 7,[2,2,2,2,0,1,2]⟩

#guard (readSourceProposal source selection).any (fun e => e.left == 4 && eqExpr e.right proposedExpr)
#guard (readSourceProposal source ⟨0,0,[.recordPayload 30 emptyRec]⟩).isNone
#guard (readSourceProposal source ⟨0,1,[.recordPayload 31 emptyRec]⟩).isNone
#guard (readSourceProposal source ⟨3,1,[.recordPayload 30 emptyRec]⟩).isNone
#guard checksNamedProjectionCut source 4 proposedExpr cut
#guard (readSourceProposal source selection).any (fun e =>
  Derivation.checkEq source (.variable e.left) e.right (literalSourceProofData selection))
end Yulang.GeneralDeclarativeI65.I72.NamedProjection464
