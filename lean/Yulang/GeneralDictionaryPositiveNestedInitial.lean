import Yulang.GeneralDictionaryPositiveNestedBranch

/-! The nonpoint nested candidate embedded in legitimate initial source data.
An explicit ordinary root interval is part of the input, not inferred from one
positive model. This proves a reachable initial state and prepared candidate,
not saturation, selection or an installation/refresh transition. -/
set_option linter.unusedSimpArgs false
namespace Yulang.GeneralDictionaryPositiveNestedInitial
open GeneralDictionaryPositiveNestedBranch
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralDictionaryNestedRefinement GeneralDictionaryNestedRefinementReplay
open CommonNominalFullCarrier
abbrev intervalAtom : PresenceNormalForm.Atom Nat := .tyLe (.var 0) (.var 3)
abbrev state := GeneralNominalState.extend source [] [intervalAtom]
abbrev current : Context := ⟨state,context.interpretation⟩
abbrev refinement := GeneralNominalRefinements.extended source [] [intervalAtom]
abbrev start := GeneralNominalSupport.initial current root

theorem source_models : GeneralNominalState.Models state assignment := by
 apply (GeneralNominalState.extend_models ..).mpr
 refine ⟨GeneralNominalProvenanceSource.source_models _ _ _,?_⟩
 intro atom member
 cases List.mem_singleton.mp member
 exact subtype_refl _

theorem source_formed : GeneralNominalSourceFormation.InitialSource registry current root := by
 refine ⟨rfl,GeneralNominalProvenanceSource.metadata,?_,?_,?_,rfl⟩
 · constructor
   · intro index
     exact ⟨GeneralNominalRefinements.sources refinement 0 (GeneralNominalProvenanceSource.source_member 0),
       GeneralNominalRefinements.sources refinement 3 (GeneralNominalProvenanceSource.source_member 3)⟩
   · intro output member; cases member
 · intro m valid index
   exact valid.2.2 intervalAtom (by simp [state,GeneralNominalState.extend,source,
     GeneralNominalProvenanceSource.state])
 · intro identity member
   have bounded := GeneralNominalAllocation.member_le_max _ identity member
   have maximum : (GeneralNominalState.sources state).foldr max 0 = state.seed := by decide +kernel
   rw [maximum] at bounded
   exact bounded

theorem initial_reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles)
 registry root start := ⟨start,⟨current,source_formed,rfl⟩,.refl⟩

theorem initial_models : GeneralNominalSaturationState.Models start.current assignment :=
 (GeneralNominalSaturationState.initial_models current root assignment).mpr source_models

private theorem scope : NominalOnlyMany (GeneralNominalInspection.queries source context.interpretation declaration) := by
 simp [GeneralNominalInspection.queries,GeneralDeclarations.Declaration.normalHead,declaration,
   GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
   GeneralNominalInspection.translate,context,GeneralNominalProvenanceSource.interpretation,source,
   GeneralNominalProvenanceSource.state,GeneralNominalProvenanceDeclarations.constructors,
   GeneralDeclarationExamples.constructors,NominalOnlyMany,NominalOnly]

private theorem finished : Finished (report context declaration bounds) := by
 rw [report_exact]
 exact GeneralDictionaryNestedRefinementExamples.nested_finished

private theorem mapped_bounds : bounds.map (mapBounds refinement.base.embed) = bounds := rfl

theorem report_transport : report current declaration bounds =
 mapReport refinement.base.embed (report context declaration bounds) := by
 have h := report_refined context current refinement rfl declaration bounds scope finished
 rw [mapped_bounds] at h
 exact h

theorem generated_empty_current : generated registry current root declaration checked bounds = {} := by
 have emitted := GeneralCanonicalChildOrder.canonicalEmit_perm root.identity declaration checked
   (GeneralNominalAllocation.capture state registry root.identity declaration.id
     (bindings state (report current declaration bounds)))
   (GeneralNominalAllocation.allocation state registry root.identity declaration.id)
 have empty : GeneralDeclarationDemands.emitAll root.identity declaration checked.signature
   (GeneralNominalAllocation.capture state registry root.identity declaration.id
     (bindings state (report current declaration bounds)))
   (GeneralNominalAllocation.allocation state registry root.identity declaration.id) = [] := rfl
 rw [empty] at emitted
 unfold generated GeneralNominalMaterialization.requests
 rw [← List.Perm.nil_eq emitted]
 rfl

theorem branch_models : BranchModels registry current root declaration checked bounds assignment := by
 refine ⟨?_,?_,?_⟩
 · have h := GeneralDictionaryNestedBranchTransport.private_refined context current refinement rfl registry root
     declaration bounds scope finished assignment source_models private_models
   rw [mapped_bounds] at h
   exact h
 · rw [report_transport]
   exact (GeneralDictionaryNestedBranchTransport.projection_map refinement _ assignment).mpr
     GeneralDictionaryPositiveNestedBranch.branch_models.2.1
 · rw [generated_empty_current]
   exact GeneralNominalMaterialization.empty_models _ _ _ _ _

theorem prepared_current : Prepared registry current root declaration checked := by
 refine ⟨source_formed.metadata,source_formed.linked,?_,bounds,?_,?_,?_,assignment,branch_models⟩
 · intro key member collision
   exact False.elim ((GeneralNominalAllocation.source_initial_fresh state registry root.identity key _
     (source_formed.below_seed _ collision)) rfl)
 · decide +kernel
 · rw [report_transport]
   exact (finished_map _ _).mpr finished
 · constructor
   · intro output member; cases member
   · rw [generated_empty_current]

end Yulang.GeneralDictionaryPositiveNestedInitial
