import Yulang.GeneralNominalSourceViewSupport255
import Yulang.GeneralNominalPublicBasis253
import Yulang.GeneralNominalViewNormal255
namespace Yulang.GeneralNominalSourceBasis255
open GeneralDeclarations GeneralSourceDictionaries
open Core.PresenceGeneration
open GeneralPresenceCheckedNormal252 (Side)
open GeneralNominalRebaseRawView243
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

/-- Candidate finite basis for the initial View. This is not a theorem that
all later consumer terms of a sourceStep trace lie in this fixed basis. -/
def basis (registry : Registry) (context : GeneralNominalCandidates.Context)
 (keys : List (Nat × Nat)) : List (TyTerm Nat) :=
 GeneralNominalViewTypeTerms255.pool (compile context.state CompTerm.var) ++
 GeneralNominalPublicBasis253.basis registry context keys

theorem source_separated
 (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
 (invocation key purpose binder position : Nat) (term : TyTerm Nat)
 (member : term ∈ GeneralNominalViewTypeTerms255.pool (compile context.state CompTerm.var)) :
 GeneralNominalPublicBasis253.privateName context.state.seed invocation key purpose binder position ∉
 GeneralPresenceSubstitutionSupport244.typeSources term := by
 rw [GeneralPresenceSourceSupport255.type_collectors]
 intro occurs
 have held := GeneralNominalSourceViewSupport255.compiled_pool context.state term member occurs
 have low := source.below_seed _ held
 have high := GeneralNominalIdentities.source_above_seed context.state.seed
   (GeneralNominalAllocation.origin invocation key purpose binder position)
 change GeneralNominalIdentities.source context.state.seed (GeneralNominalAllocation.origin invocation key purpose binder position) ≤ context.state.seed at low
 omega

theorem separated
 (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
 (keys : List (Nat × Nat)) (invocation key purpose binder position : Nat) (privatePurpose : purpose ≤ 1)
 (term : TyTerm Nat) (member : term ∈ basis registry context keys) :
 GeneralNominalPublicBasis253.privateName context.state.seed invocation key purpose binder position ∉
 GeneralPresenceSubstitutionSupport244.typeSources term := by
 rcases List.mem_append.mp member with original | publicAtom
 · exact source_separated source invocation key purpose binder position term original
 · exact GeneralNominalPublicBasis253.basis_separated source keys invocation key purpose binder position privatePurpose term publicAtom

theorem source_supported (registry : Registry) (context : GeneralNominalCandidates.Context)
 (keys : List (Nat × Nat)) (side : Side) :
 GeneralNominalViewNormal255.Supported side (basis registry context keys) (compile context.state CompTerm.var) := by
 apply GeneralNominalViewNormal255.supported_mono
 · intro _ member; exact List.mem_append_left _ member
 · exact GeneralNominalViewTypeTerms255.supported _ side

theorem source_success (registry : Registry) (context : GeneralNominalCandidates.Context)
 (keys : List (Nat × Nat)) (side : Side) :
 GeneralNominalViewNormal255.prepare side (basis registry context keys) (compile context.state CompTerm.var) =
 some (GeneralNominalViewNormal255.rewrite side (basis registry context keys) (compile context.state CompTerm.var)) :=
 (GeneralNominalViewNormal255.prepare_exact ..).mpr ⟨source_supported registry context keys side,rfl⟩

theorem source_models (registry : Registry) (context : GeneralNominalCandidates.Context)
 (keys : List (Nat × Nat)) (side : Side) (assignment : Assignment) :
 (GeneralNominalViewNormal255.rewrite side (basis registry context keys) (compile context.state CompTerm.var)).Models assignment ↔
 GeneralNominalState.Models context.state assignment :=
 (GeneralNominalViewNormal255.prepare_models side _ _ _ (source_success registry context keys side) assignment).trans
 ((compile_exact context.state CompTerm.var assignment).trans (by rfl))

theorem consumer_safe
 (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
 (keys : List (Nat × Nat)) (side : Side) (term : TyTerm Nat)
 (member : term ∈ GeneralNominalViewTypeTerms255.terms (compile context.state CompTerm.var))
 (assignment : Assignment) :
 Equivalent ((GeneralPresenceCheckedNormal252.normalize side (basis registry context keys) term).eval model assignment) (term.eval model assignment) ∧
 ∀ invocation key purpose binder position, purpose ≤ 1 →
 GeneralNominalPublicBasis253.privateName context.state.seed invocation key purpose binder position ∉
 GeneralPresenceSubstitutionSupport244.typeSources (GeneralPresenceCheckedNormal252.normalize side (basis registry context keys) term) := by
 have success := (GeneralPresenceCheckedNormal252.prepare_exact side (basis registry context keys) term _).mpr
   ⟨source_supported registry context keys side term member,rfl⟩
 exact ⟨GeneralPresenceCheckedNormal252.equivalent _ _ _ _ success assignment,
   fun invocation key purpose binder position privatePurpose => GeneralPresenceCheckedNormal252.no_private_reads _ _ _ _ success _
     (separated source keys invocation key purpose binder position privatePurpose)⟩
end Yulang.GeneralNominalSourceBasis255
