import Yulang.GeneralNominalSourceTemplateMenu255
namespace Yulang.GeneralNominalNormalizedDepth255
open Core.PresenceGeneration (TyTerm)
open GeneralNominalExprDepth253 (typeDepth materializedDepth rawDepth)
open GeneralPresenceCheckedNormal252 (Side)
open GeneralNominalMaterialization (Mode)
open GeneralNominalTemplateChoices255 (Raw)

def atomDepth (basis : List (TyTerm Nat)) : Nat :=
 GeneralNominalProducerOrder254.ceiling (basis.map typeDepth)

def leafBound (basis : List (TyTerm Nat)) : Nat := 1 + basis.length + atomDepth basis

theorem atom_bounded (basis : List (TyTerm Nat)) (term : TyTerm Nat) (member : term ∈ basis) :
 typeDepth term ≤ atomDepth basis := GeneralNominalProducerOrder254.below_ceiling (List.mem_map.mpr ⟨term,member,rfl⟩)

theorem union_fold_depth (terms : List (TyTerm Nat)) (bound : Nat)
 (bounded : ∀ term ∈ terms, typeDepth term ≤ bound) :
 typeDepth (GeneralPresenceUnionNormal252.fold terms) ≤ 1 + terms.length + bound := by
 induction terms with
 | nil => simp [GeneralPresenceUnionNormal252.fold,typeDepth]
 | cons first rest ih =>
   have one := bounded first (List.mem_cons_self ..)
   cases rest with
   | nil => simpa only [GeneralPresenceUnionNormal252.fold] using Nat.le_trans one (by omega)
   | cons next tail =>
     have two := ih (fun term member => bounded term (List.mem_cons_of_mem _ member))
     change 1 + max (typeDepth first) (typeDepth (GeneralPresenceUnionNormal252.fold (next :: tail))) ≤ _
     simp only [List.length_cons] at *
     omega

theorem inter_fold_depth (terms : List (TyTerm Nat)) (bound : Nat)
 (bounded : ∀ term ∈ terms, typeDepth term ≤ bound) :
 typeDepth (GeneralPresenceInterNormal252.fold terms) ≤ 1 + terms.length + bound := by
 induction terms with
 | nil => simp [GeneralPresenceInterNormal252.fold,typeDepth]
 | cons first rest ih =>
   have one := bounded first (List.mem_cons_self ..)
   cases rest with
   | nil => simpa only [GeneralPresenceInterNormal252.fold] using Nat.le_trans one (by omega)
   | cons next tail =>
     have two := ih (fun term member => bounded term (List.mem_cons_of_mem _ member))
     change 1 + max (typeDepth first) (typeDepth (GeneralPresenceInterNormal252.fold (next :: tail))) ≤ _
     simp only [List.length_cons] at *
     omega

/-- Bound on stored normalized source syntax, not ground semantic readback.
The bound is valid even when support fails, so it alone gives no correctness. -/
theorem normalized_depth (side : Side) (basis : List (TyTerm Nat)) (term : TyTerm Nat) :
 typeDepth (GeneralPresenceCheckedNormal252.normalize side basis term) ≤ leafBound basis := by
 cases side
 · have bounded := union_fold_depth (GeneralPresenceUnionNormal252.canonical basis (GeneralPresenceUnionNormal252.atoms term))
     (atomDepth basis) (fun atom member => atom_bounded basis atom ((GeneralPresenceUnionNormal252.canonical_mem ..).mp member).1)
   have length := List.length_filter_le (fun atom => decide (atom ∈ GeneralPresenceUnionNormal252.atoms term)) basis
   change typeDepth (GeneralPresenceUnionNormal252.fold _) ≤ _
   unfold GeneralPresenceUnionNormal252.canonical at bounded ⊢
   unfold leafBound
   omega
 · have bounded := inter_fold_depth (GeneralPresenceInterNormal252.canonical basis (GeneralPresenceInterNormal252.atoms term))
     (atomDepth basis) (fun atom member => atom_bounded basis atom ((GeneralPresenceInterNormal252.canonical_mem ..).mp member).1)
   have length := List.length_filter_le (fun atom => decide (atom ∈ GeneralPresenceInterNormal252.atoms term)) basis
   change typeDepth (GeneralPresenceInterNormal252.fold _) ≤ _
   unfold GeneralPresenceInterNormal252.canonical at bounded ⊢
   unfold leafBound
   omega

theorem rewritten_depth (policy : Mode → Side) (basis : List (TyTerm Nat))
 (variables : GeneralNominalTemplateNormal255.Variables) (mode : Mode) (term : Raw) :
 materializedDepth (GeneralNominalTemplateNormal255.rewrite policy basis variables mode term) ≤ rawDepth term + leafBound basis :=
 GeneralNominalExprDepth253.compile_depth _ (leafBound basis) (fun mode name => normalized_depth (policy mode) basis (variables mode name)) mode term
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 GeneralNominalVersionedMixedKernel234
open GeneralDictionaryAssociatedProvenance (Supplies)
variable {roles : Roles.RoleDecls} {state : State roles}

theorem source_rewrite_depth
 (path : B4Target.Steps (Step registry root) (initial context root) state)
 (frame : GeneralNominalVersionedEvidence231.Frame registry state.core focus key plan)
 (requested : output ∈ focus.demand.outputs)
 (supplied : Supplies roles plan.packet.declaration output.name body)
 (compiled : GeneralNominalCenteredHeadMatEffects.compileBody plan body = some expression)
 (policy : Mode → Side) (basis : List (TyTerm Nat))
 (variables : GeneralNominalTemplateNormal255.Variables) (mode : Mode) :
 materializedDepth (GeneralNominalTemplateNormal255.rewrite policy basis variables mode expression) ≤
 GeneralNominalRawOutputBudget254.budget registry context root + leafBound basis :=
 Nat.le_trans (rewritten_depth policy basis variables mode expression)
   (Nat.add_le_add_right (GeneralNominalRawOutputBudget254.source_depth path frame requested supplied compiled) _)
end Yulang.GeneralNominalNormalizedDepth255
