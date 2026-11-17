import Yulang.GeneralPresenceSubstitutionSupport244
namespace Yulang.GeneralPresenceOwnerRewrite244
open Core.PresenceGeneration
open PresenceNormalForm
open GeneralPresenceDefinitionRewrite244
open GeneralPresenceSubstitutionSupport244
open GeneralFiniteDependencyRewrite244
variable {Name : Type} [DecidableEq Name]

def lookup (entries : List (Entry Name)) (name : Name) : Option (TyTerm Name) :=
 match entries with
 | [] => none
 | entry :: rest => if entry.1 = name then some entry.2 else lookup rest name

def substitution (entries : List (Entry Name)) (name : Name) : CompTerm Name :=
 ⟨(lookup entries name).getD (.var name),.var name⟩

variable {entries : List (Entry Name)} {name : Name} {term : TyTerm Name}

theorem lookup_member (found : lookup entries name = some term) : (name,term) ∈ entries := by
 induction entries with
 | nil => simp [lookup] at found
 | cons entry rest ih =>
   by_cases same : entry.1 = name
   · have value : entry.2 = term := by simpa [lookup,same] using found
     have pair : (name,term) = entry := Prod.ext same.symm value.symm
     exact List.mem_cons.mpr (Or.inl pair)
   · exact List.mem_cons_of_mem _ (ih (by simpa [lookup,same] using found))

theorem lookup_outside (outside : ∀ entry ∈ entries, entry.1 ≠ name) : lookup entries name = none := by
 induction entries with
 | nil => rfl
 | cons entry rest ih =>
   simp only [lookup,ite_eq_right (outside entry (by simp))]
   exact ih (fun item member => outside item (List.mem_cons_of_mem _ member))

theorem target_unchanged (outside : ∀ entry ∈ entries, entry.1 ≠ name) :
 (substitution entries name).ty = .var name := by
 simp [substitution,lookup_outside outside]

theorem substitution_below {rank : Name → Nat} (ranked : RankedEntries rank entries) :
 RewriteBelow rank (mappingSources (substitution entries)) := by
 intro name source member
 rcases List.mem_append.mp member with member | member
 · cases found : lookup entries name with
   | none =>
     have same : source = name := by simpa [substitution,found,typeSources] using member
     subst source; exact Nat.le_refl _
   | some term =>
     have present : source ∈ typeSources term := by simpa [substitution,found] using member
     exact Nat.le_of_lt (ranked (name,term) (lookup_member found) source present)
 · have same : source = name := by simpa [substitution,rowSources] using member
   subst source; exact Nat.le_refl _

def DisjointTargets (removed retained : List (Entry Name)) : Prop :=
 ∀ old ∈ removed, ∀ other ∈ retained, old.1 ≠ other.1

theorem owner_block_shape (removed retained : List (Entry Name)) (disjoint : DisjointTargets removed retained) :
 (block retained).map (atomSubst (substitution removed)) = block (transform (substitution removed) retained) := by
 apply block_subst
 intro other member
 exact target_unchanged (fun old present => disjoint old present other member)

theorem owner_block_exact (removed retained : List (Entry Name)) (disjoint : DisjointTargets removed retained)
 (model : Model) (assignment : Name → Comp model) :
 All model assignment (block (transform (substitution removed) retained)) ↔
 All model (fun name => (substitution removed name).eval model assignment) (block retained) := by
 apply block_exact
 intro other member
 exact target_unchanged (fun old present => disjoint old present other member)

theorem owner_external {rank : Name → Nat} (removed retained : List (Entry Name))
 (removedRanked : RankedEntries rank removed) (retainedRanked : RankedEntries rank retained)
 (sameRank : ∀ first ∈ retained, ∀ last ∈ retained, rank first.1 = rank last.1) :
 ∀ entry ∈ transform (substitution removed) retained, ∀ source ∈ typeSources entry.2,
 ∀ target ∈ transform (substitution removed) retained, target.1 ≠ source :=
 transformed_external _ (substitution_below removedRanked) retainedRanked sameRank

def Coherent (entries : List (Entry Name)) : Prop :=
 ∀ first ∈ entries, ∀ last ∈ entries, first.1 = last.1 → first.2 = last.2

omit [DecidableEq Name] in
theorem transform_coherent (mapping : Name → CompTerm Name) (coherent : Coherent entries) :
 Coherent (transform mapping entries) := by
 intro first firstMem last lastMem equal
 obtain ⟨a,am,rfl⟩ := List.mem_map.mp firstMem
 obtain ⟨b,bm,rfl⟩ := List.mem_map.mp lastMem
 exact congrArg (fun term => term.subst mapping) (coherent a am b bm equal)
end Yulang.GeneralPresenceOwnerRewrite244
