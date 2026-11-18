import Yulang.GeneralNominalViewNormal255
import Yulang.GeneralNominalViewTypeImage255
import Yulang.GeneralPresenceNormalFinite252
namespace Yulang.GeneralNominalViewFixed255
open Core.PresenceGeneration
open GeneralNominalRebaseRawView243
open GeneralPresenceCheckedNormal252 (Side)
open GeneralNominalViewNormal255

def candidates (side : Side) (basis : List (TyTerm Nat)) : List (TyTerm Nat) :=
 match side with
 | .lower => GeneralPresenceNormalFinite252.lowerCandidates basis
 | .upper => GeneralPresenceNormalFinite252.upperCandidates basis

theorem candidate_count (side : Side) (basis : List (TyTerm Nat)) :
 (candidates side basis).length = 2 ^ basis.length := by
 cases side
 · exact GeneralPresenceNormalFinite252.lower_count basis
 · exact GeneralPresenceNormalFinite252.upper_count basis

theorem normalized_candidate (side : Side) (basis : List (TyTerm Nat)) (term : TyTerm Nat) :
 GeneralPresenceCheckedNormal252.normalize side basis term ∈ candidates side basis := by
 cases side
 · exact GeneralPresenceNormalFinite252.lower_enumerated basis term
 · exact GeneralPresenceNormalFinite252.upper_enumerated basis term

theorem field_candidates (side : Side) (basis : List (TyTerm Nat)) (view : View) (term : TyTerm Nat)
 (member : term ∈ GeneralNominalViewTypeTerms255.terms (rewrite side basis view)) :
 term ∈ candidates side basis := by
 obtain ⟨original,_,rfl⟩ := GeneralNominalViewTypeImage255.term_origin _ view term member
 exact normalized_candidate side basis original

theorem rewritten_supported (side : Side) (basis : List (TyTerm Nat)) (view : View)
 (supported : Supported side basis view) : Supported side basis (rewrite side basis view) := by
 intro term member
 obtain ⟨original,present,rfl⟩ := GeneralNominalViewTypeImage255.term_origin _ view term member
 exact GeneralPresenceCheckedNormal252.normalized_supported side basis original (supported original present)

theorem rewrite_idempotent (side : Side) (basis : List (TyTerm Nat)) (view : View)
 (supported : Supported side basis view) : rewrite side basis (rewrite side basis view) = rewrite side basis view := by
 unfold rewrite
 rw [GeneralNominalViewTypeImage255.map_comp]
 apply GeneralNominalViewTypeImage255.map_congr
 intro term member
 have success := (GeneralPresenceCheckedNormal252.prepare_exact side basis term _).mpr ⟨supported term member,rfl⟩
 have fixed := GeneralPresenceCheckedNormal252.prepare_idempotent side basis term _ success
 exact ((GeneralPresenceCheckedNormal252.prepare_exact ..).mp fixed).2.symm

theorem prepare_idempotent (side : Side) (basis : List (TyTerm Nat)) (view result : View)
 (success : prepare side basis view = some result) : prepare side basis result = some result := by
 obtain ⟨supported,rfl⟩ := (prepare_exact ..).mp success
 exact (prepare_exact ..).mpr ⟨rewritten_supported side basis view supported,(rewrite_idempotent side basis view supported).symm⟩

theorem field_private_free (side : Side) (basis : List (TyTerm Nat)) (view : View)
 (privateName : Nat)
 (separated : ∀ atom ∈ basis, privateName ∉ GeneralPresenceSubstitutionSupport244.typeSources atom)
 (term : TyTerm Nat) (member : term ∈ GeneralNominalViewTypeTerms255.terms (rewrite side basis view)) :
 privateName ∉ GeneralPresenceSubstitutionSupport244.typeSources term := by
 obtain ⟨original,_,rfl⟩ := GeneralNominalViewTypeImage255.term_origin _ view term member
 cases side
 · exact GeneralPresenceUnionNormal252.no_private_all_reads basis original privateName separated
 · exact GeneralPresenceInterNormal252.no_private_all_reads basis original privateName separated
end Yulang.GeneralNominalViewFixed255
