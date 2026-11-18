import Yulang.GeneralNominalPublicPorts253
import Yulang.GeneralPresenceNormalFinite252
namespace Yulang.GeneralNominalPublicBasis253
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalPublicPorts253
open Core.PresenceGeneration (TyTerm)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

abbrev privateName (seed root declaration purpose binder position : Nat) :=
 GeneralNominalIdentities.source seed (GeneralNominalAllocation.origin root declaration purpose binder position)

theorem private_not_ports (seed parent : Nat) (declaration : Declaration)
 (root key purpose binder position : Nat) (privatePurpose : purpose ≤ 1) :
 privateName seed root key purpose binder position ∉ ports seed parent declaration := by
 intro member
 obtain ⟨p,owner,offset,lower,_,equal⟩ := port_purpose seed parent declaration _ member
 have same := (GeneralNominalIdentities.source_identity seed _ _).mp equal
 have purposes := congrArg (fun origin : GeneralNominalIdentities.Origin => origin.2.2.1) same
 change purpose = p at purposes
 omega

theorem private_not_names (registry : Registry) (seed : Nat) (keys : List (Nat × Nat))
 (root key purpose binder position : Nat) (privatePurpose : purpose ≤ 1) :
 privateName seed root key purpose binder position ∉ names registry seed keys := by
 intro member
 obtain ⟨owner,_,found⟩ := List.mem_flatMap.mp member
 obtain ⟨declaration,_,found⟩ := List.mem_flatMap.mp found
 split at found
 · exact private_not_ports seed owner.1 declaration root key purpose binder position privatePurpose found
 · cases found

def basis (registry : Registry) (context : GeneralNominalCandidates.Context)
 (keys : List (Nat × Nat)) : List (TyTerm Nat) :=
 (GeneralNominalState.sources context.state ++ names registry context.state.seed keys).map TyTerm.var

/-- Includes fixed rebase slots (position 0) and versioned slots (any positive
position), without treating the latter as a finite set. -/
theorem basis_separated
 (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
 (keys : List (Nat × Nat)) (invocation key purpose binder position : Nat) (privatePurpose : purpose ≤ 1)
 (atom : TyTerm Nat) (member : atom ∈ basis registry context keys) :
 privateName context.state.seed invocation key purpose binder position ∉
 GeneralPresenceSubstitutionSupport244.typeSources atom := by
 obtain ⟨name,present,rfl⟩ := List.mem_map.mp member
 intro occurs
 have same : privateName context.state.seed invocation key purpose binder position = name := List.mem_singleton.mp occurs
 subst name
 rcases List.mem_append.mp present with original | produced
 · have low := source.below_seed _ original
   change GeneralNominalIdentities.source context.state.seed (GeneralNominalAllocation.origin invocation key purpose binder position) ≤ context.state.seed at low
   have high := GeneralNominalIdentities.source_above_seed context.state.seed
     (GeneralNominalAllocation.origin invocation key purpose binder position)
   omega
 · exact private_not_names registry context.state.seed keys invocation key purpose binder position privatePurpose produced

/-- Normalization alone is private-free even if it drops unsupported atoms.
The next theorem adds the support premise required for semantic preservation. -/
theorem lower_private_free
 (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
 (keys : List (Nat × Nat)) (term : TyTerm Nat) (invocation key purpose binder position : Nat)
 (privatePurpose : purpose ≤ 1) :
 privateName context.state.seed invocation key purpose binder position ∉
 GeneralPresenceSubstitutionSupport244.typeSources (GeneralPresenceUnionNormal252.normalize (basis registry context keys) term) :=
 GeneralPresenceUnionNormal252.no_private_all_reads _ term _ (basis_separated source keys invocation key purpose binder position privatePurpose)

theorem upper_private_free
 (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
 (keys : List (Nat × Nat)) (term : TyTerm Nat) (invocation key purpose binder position : Nat)
 (privatePurpose : purpose ≤ 1) :
 privateName context.state.seed invocation key purpose binder position ∉
 GeneralPresenceSubstitutionSupport244.typeSources (GeneralPresenceInterNormal252.normalize (basis registry context keys) term) :=
 GeneralPresenceInterNormal252.no_private_all_reads _ term _ (basis_separated source keys invocation key purpose binder position privatePurpose)

theorem lower_safe
 (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
 (keys : List (Nat × Nat)) (term : TyTerm Nat)
 (supported : GeneralPresenceUnionNormal252.atoms term ⊆ basis registry context keys) (assignment : Assignment) :
 Equivalent ((GeneralPresenceUnionNormal252.normalize (basis registry context keys) term).eval model assignment) (term.eval model assignment) ∧
 GeneralPresenceUnionNormal252.normalize (basis registry context keys) term ∈ GeneralPresenceNormalFinite252.lowerCandidates (basis registry context keys) ∧
 ∀ invocation key purpose binder position, purpose ≤ 1 →
 privateName context.state.seed invocation key purpose binder position ∉
 GeneralPresenceSubstitutionSupport244.typeSources (GeneralPresenceUnionNormal252.normalize (basis registry context keys) term) :=
 ⟨GeneralPresenceUnionNormal252.equivalent _ term supported assignment,GeneralPresenceNormalFinite252.lower_enumerated _ term,
   fun invocation key purpose binder position privatePurpose => lower_private_free source keys term invocation key purpose binder position privatePurpose⟩

theorem upper_safe
 (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
 (keys : List (Nat × Nat)) (term : TyTerm Nat)
 (supported : GeneralPresenceInterNormal252.atoms term ⊆ basis registry context keys) (assignment : Assignment) :
 Equivalent ((GeneralPresenceInterNormal252.normalize (basis registry context keys) term).eval model assignment) (term.eval model assignment) ∧
 GeneralPresenceInterNormal252.normalize (basis registry context keys) term ∈ GeneralPresenceNormalFinite252.upperCandidates (basis registry context keys) ∧
 ∀ invocation key purpose binder position, purpose ≤ 1 →
 privateName context.state.seed invocation key purpose binder position ∉
 GeneralPresenceSubstitutionSupport244.typeSources (GeneralPresenceInterNormal252.normalize (basis registry context keys) term) :=
 ⟨GeneralPresenceInterNormal252.equivalent _ term supported assignment,GeneralPresenceNormalFinite252.upper_enumerated _ term,
   fun invocation key purpose binder position privatePurpose => upper_private_free source keys term invocation key purpose binder position privatePurpose⟩
end Yulang.GeneralNominalPublicBasis253
