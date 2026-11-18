import Yulang.GeneralNominalTemplateNormal255
namespace Yulang.GeneralNominalTemplateSupport255
open Core.PresenceGeneration (TyTerm)
open GeneralNominalTemplateChoices255 (Raw Materialized choices choicesMany)

mutual
 def sourceTerms : Materialized → List (TyTerm Nat)
 | .source term => [term]
 | .primitive _ arguments | .nominal _ arguments => sourceTermsMany arguments
 | .record _ first last | .join first last => sourceTerms first ++ sourceTerms last
 | .variant _ term => sourceTerms term
 def sourceTermsMany : List Materialized → List (TyTerm Nat)
 | [] => []
 | first :: rest => sourceTerms first ++ sourceTermsMany rest
end

mutual
 theorem choices_sources (pool : List (TyTerm Nat)) (template : Raw) (result : Materialized)
 (present : result ∈ choices pool template) : sourceTerms result ⊆ pool := by
 cases template with
 | «variable» name =>
   obtain ⟨term,member,rfl⟩ := List.mem_map.mp present
   exact fun _ occurs => List.mem_singleton.mp occurs ▸ member
 | primitive constructor arguments =>
   obtain ⟨results,member,rfl⟩ := List.mem_map.mp present
   exact choicesMany_sources pool arguments results member
 | nominal name arguments =>
   obtain ⟨results,member,rfl⟩ := List.mem_map.mp present
   exact choicesMany_sources pool arguments results member
 | record label first last =>
   obtain ⟨a,member,rest⟩ := List.mem_flatMap.mp present
   obtain ⟨b,found,rfl⟩ := List.mem_map.mp rest
   intro term occurs
   exact (List.mem_append.mp occurs).elim (fun h => choices_sources pool first a member h) (fun h => choices_sources pool last b found h)
 | variant tag child =>
   obtain ⟨a,member,rfl⟩ := List.mem_map.mp present
   exact choices_sources pool child a member
 | join first last =>
   obtain ⟨a,member,rest⟩ := List.mem_flatMap.mp present
   obtain ⟨b,found,rfl⟩ := List.mem_map.mp rest
   intro term occurs
   exact (List.mem_append.mp occurs).elim (fun h => choices_sources pool first a member h) (fun h => choices_sources pool last b found h)
 theorem choicesMany_sources (pool : List (TyTerm Nat)) (templates : List Raw) (results : List Materialized)
 (present : results ∈ choicesMany pool templates) : sourceTermsMany results ⊆ pool := by
 cases templates with
 | nil => cases List.mem_singleton.mp present; exact fun _ member => False.elim (List.not_mem_nil member)
 | cons first rest =>
   obtain ⟨head,member,tail⟩ := List.mem_flatMap.mp present
   obtain ⟨remaining,found,rfl⟩ := List.mem_map.mp tail
   intro term occurs
   exact (List.mem_append.mp occurs).elim (fun h => choices_sources pool first head member h) (fun h => choicesMany_sources pool rest remaining found h)
end

/-- All type and arrow-row reads occurring inside source leaves. -/
def reads (expression : Materialized) : List Nat :=
 (sourceTerms expression).flatMap GeneralPresenceSubstitutionSupport244.typeSources

theorem choice_private_free (pool : List (TyTerm Nat)) (template : Raw) (result : Materialized)
 (present : result ∈ choices pool template) (privateName : Nat)
 (separated : ∀ term ∈ pool, privateName ∉ GeneralPresenceSubstitutionSupport244.typeSources term) :
 privateName ∉ reads result := by
 intro occurs
 obtain ⟨term,member,read⟩ := List.mem_flatMap.mp occurs
 exact separated term (choices_sources pool template result present member) read

theorem selected_subset (pool selected : List α)
 (member : selected ∈ GeneralPresenceNormalFinite252.subsets pool) : selected ⊆ pool := by
 induction pool generalizing selected with
 | nil => cases List.mem_singleton.mp member; exact List.Subset.refl _
 | cons first rest ih =>
   rcases List.mem_append.mp member with old | added
   · exact fun _ h => List.mem_cons_of_mem _ (ih _ old h)
   · obtain ⟨tail,known,rfl⟩ := List.mem_map.mp added
     intro name h
     exact (List.mem_cons.mp h).elim (fun equal => equal ▸ List.mem_cons_self ..)
       (fun later => List.mem_cons_of_mem _ (ih _ known later))

theorem candidate_private_free (basis : List (TyTerm Nat)) (privateName : Nat)
 (separated : ∀ atom ∈ basis, privateName ∉ GeneralPresenceSubstitutionSupport244.typeSources atom)
 (term : TyTerm Nat) (present : term ∈ GeneralNominalTemplateNormal255.leafCandidates basis) :
 privateName ∉ GeneralPresenceSubstitutionSupport244.typeSources term := by
 rcases List.mem_append.mp present with lower | upper
 · obtain ⟨selected,member,rfl⟩ := List.mem_map.mp lower
   intro occurs
   obtain ⟨atom,found,read⟩ := GeneralPresenceUnionNormal252.fold_all_reads selected privateName occurs
   exact separated atom (selected_subset basis selected member found) read
 · obtain ⟨selected,member,rfl⟩ := List.mem_map.mp upper
   intro occurs
   obtain ⟨atom,found,read⟩ := GeneralPresenceInterNormal252.fold_all_reads selected privateName occurs
   exact separated atom (selected_subset basis selected member found) read

theorem rewritten_private_free (policy : GeneralNominalMaterialization.Mode → GeneralPresenceCheckedNormal252.Side)
 (basis : List (TyTerm Nat)) (variables : GeneralNominalTemplateNormal255.Variables)
 (mode : GeneralNominalMaterialization.Mode) (template : Raw) (privateName : Nat)
 (separated : ∀ atom ∈ basis, privateName ∉ GeneralPresenceSubstitutionSupport244.typeSources atom) :
 privateName ∉ reads (GeneralNominalTemplateNormal255.rewrite policy basis variables mode template) :=
 choice_private_free _ template _ (GeneralNominalTemplateNormal255.rewrite_finite policy basis variables mode template) privateName
   (candidate_private_free basis privateName separated)
end Yulang.GeneralNominalTemplateSupport255
