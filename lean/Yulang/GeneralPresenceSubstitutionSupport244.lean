import Yulang.GeneralPresenceDefinitionRewrite244
import Yulang.GeneralFiniteDependencyRewrite244
namespace Yulang.GeneralPresenceSubstitutionSupport244
open Core.PresenceGeneration
open GeneralPresenceDefinitionRewrite244
open GeneralFiniteDependencyRewrite244

def rowSources : RowTerm Name → List Name
 | .var name => [name]
 | .empty => []
 | .join first last => rowSources first ++ rowSources last

def typeSources : TyTerm Name → List Name
 | .var name => [name]
 | .union first last | .inter first last | .pair first last | .record _ first last |
     .recordDefault _ first last => typeSources first ++ typeSources last
 | .required _ child | .variant _ child => typeSources child
 | .arrow first incoming last outgoing =>
     typeSources first ++ rowSources incoming ++ typeSources last ++ rowSources outgoing
 | _ => []

def mappingSources (mapping : Name → CompTerm Name) (name : Name) : List Name :=
 typeSources (mapping name).ty ++ rowSources (mapping name).row

theorem append_subset {a b c d : List Name} (left : a ⊆ b) (right : c ⊆ d) : a ++ c ⊆ b ++ d := by
 intro name member
 rcases List.mem_append.mp member with member | member
 · exact List.mem_append_left _ (left member)
 · exact List.mem_append_right _ (right member)

theorem row_sources_subst (mapping : Name → CompTerm Name) (term : RowTerm Name) :
 rowSources (term.subst mapping) ⊆ (rowSources term).flatMap (mappingSources mapping) := by
 induction term with
 | var name =>
   intro x member
   exact List.mem_flatMap.mpr ⟨name,by simp [rowSources],List.mem_append_right _ member⟩
 | empty => simp [rowSources,RowTerm.subst]
 | join first last one two =>
   simpa only [rowSources,RowTerm.subst,List.flatMap_append] using append_subset one two

theorem type_sources_subst (mapping : Name → CompTerm Name) (term : TyTerm Name) :
 typeSources (term.subst mapping) ⊆ (typeSources term).flatMap (mappingSources mapping) := by
 induction term with
 | var name =>
   intro x member
   exact List.mem_flatMap.mpr ⟨name,by simp [typeSources],List.mem_append_left _ member⟩
 | base | bottom | top | emptyRecord | exactEmpty => simp [typeSources,TyTerm.subst]
 | union first last one two =>
   simpa only [typeSources,TyTerm.subst,List.flatMap_append] using append_subset one two
 | inter first last one two =>
   simpa only [typeSources,TyTerm.subst,List.flatMap_append] using append_subset one two
 | pair first last one two =>
   simpa only [typeSources,TyTerm.subst,List.flatMap_append] using append_subset one two
 | record label first last one two =>
   simpa only [typeSources,TyTerm.subst,List.flatMap_append] using append_subset one two
 | recordDefault label first last one two =>
   simpa only [typeSources,TyTerm.subst,List.flatMap_append] using append_subset one two
 | required label child ih => exact ih
 | variant label child ih => exact ih
 | arrow first incoming last outgoing one two =>
   simpa only [typeSources,TyTerm.subst,List.flatMap_append] using
     append_subset (append_subset (append_subset one (row_sources_subst mapping incoming)) two)
       (row_sources_subst mapping outgoing)

theorem rank_preserved (mapping : Name → CompTerm Name) (term : TyTerm Name)
 (safe : RewriteBelow rank (mappingSources mapping)) (before : Below rank owner (typeSources term)) :
 Below rank owner (typeSources (term.subst mapping)) := by
 intro source member
 exact below_expand safe before source (type_sources_subst mapping term member)

def RankedEntries (rank : Name → Nat) (entries : List (Entry Name)) : Prop :=
 ∀ entry ∈ entries, Below rank entry.1 (typeSources entry.2)

theorem transformed_ranked (mapping : Name → CompTerm Name)
 (safe : RewriteBelow rank (mappingSources mapping)) (ranked : RankedEntries rank entries) :
 RankedEntries rank (transform mapping entries) := by
 intro entry member
 obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
 exact rank_preserved mapping original.2 safe (ranked original present)

theorem transformed_no_self (mapping : Name → CompTerm Name)
 (safe : RewriteBelow rank (mappingSources mapping)) (ranked : RankedEntries rank entries)
 (entry : Entry Name) (member : entry ∈ transform mapping entries) : entry.1 ∉ typeSources entry.2 :=
 no_self (transformed_ranked mapping safe ranked entry member)

/-- Equal ranks for an owner's targets turn decreasing dependencies into the
whole block's External condition, not merely absence of each self-reference. -/
theorem block_external (ranked : RankedEntries rank entries)
 (sameRank : ∀ first ∈ entries, ∀ last ∈ entries, rank first.1 = rank last.1) :
 ∀ entry ∈ entries, ∀ source ∈ typeSources entry.2, ∀ target ∈ entries, target.1 ≠ source := by
 intro entry member source present target targetMem equal
 have lower := ranked entry member source present
 have same := sameRank entry member target targetMem
 rw [← equal,← same] at lower
 exact Nat.lt_irrefl _ lower

theorem transformed_same_rank {rank : Name → Nat} (mapping : Name → CompTerm Name)
 (sameRank : ∀ first ∈ entries, ∀ last ∈ entries, rank first.1 = rank last.1) :
 ∀ first ∈ transform mapping entries, ∀ last ∈ transform mapping entries, rank first.1 = rank last.1 := by
 intro first firstMem last lastMem
 obtain ⟨a,am,rfl⟩ := List.mem_map.mp firstMem
 obtain ⟨b,bm,rfl⟩ := List.mem_map.mp lastMem
 exact sameRank a am b bm

theorem transformed_external (mapping : Name → CompTerm Name)
 (safe : RewriteBelow rank (mappingSources mapping)) (ranked : RankedEntries rank entries)
 (sameRank : ∀ first ∈ entries, ∀ last ∈ entries, rank first.1 = rank last.1) :
 ∀ entry ∈ transform mapping entries, ∀ source ∈ typeSources entry.2,
 ∀ target ∈ transform mapping entries, target.1 ≠ source :=
 block_external (transformed_ranked mapping safe ranked) (transformed_same_rank mapping sameRank)
end Yulang.GeneralPresenceSubstitutionSupport244
