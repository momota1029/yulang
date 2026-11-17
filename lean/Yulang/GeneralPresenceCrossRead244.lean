import Yulang.GeneralPresenceOwnerCheck244
/-! Direct cross-read conditions for preserving another owner's definition
block. These are representation checks, not language acceptance criteria. -/
namespace Yulang.GeneralPresenceCrossRead244
open Core.PresenceGeneration
open GeneralPresenceDefinitionRewrite244
open GeneralPresenceSubstitutionSupport244
open GeneralPresenceOwnerRewrite244
variable {Name : Type} [DecidableEq Name]

def Avoid (targets : List (Entry Name)) (sources : List Name) : Prop :=
 ∀ source ∈ sources, ∀ target ∈ targets, target.1 ≠ source

def CrossRead (removed retained : List (Entry Name)) : Prop :=
 ∀ entry ∈ removed, Avoid retained (typeSources entry.2)

def External (entries : List (Entry Name)) : Prop := CrossRead entries entries

theorem substitution_avoids (removed retained : List (Entry Name))
 (cross : CrossRead removed retained) (name : Name)
 (outside : ∀ target ∈ retained, target.1 ≠ name) :
 Avoid retained (mappingSources (substitution removed) name) := by
 intro source member target targetMem
 rcases List.mem_append.mp member with typed | row
 · cases found : lookup removed name with
   | none =>
     have same : source = name := by simpa [substitution,found,typeSources] using typed
     exact same ▸ outside target targetMem
   | some term =>
     have present : source ∈ typeSources term := by simpa [substitution,found] using typed
     exact cross (name,term) (lookup_member found) source present target targetMem
 · have same : source = name := by simpa [substitution,rowSources] using row
   exact same ▸ outside target targetMem

theorem transformed_external (removed retained : List (Entry Name))
 (cross : CrossRead removed retained) (external : External retained) :
 External (transform (substitution removed) retained) := by
 intro entry member source present target targetMem
 obtain ⟨original,originalMem,rfl⟩ := List.mem_map.mp member
 obtain ⟨targetOriginal,targetOriginalMem,rfl⟩ := List.mem_map.mp targetMem
 have supported := type_sources_subst (substitution removed) original.2 present
 obtain ⟨old,oldPresent,newPresent⟩ := List.mem_flatMap.mp supported
 exact substitution_avoids removed retained cross old
   (external original originalMem old oldPresent) source newPresent targetOriginal targetOriginalMem

def crossCheck (removed retained : List (Entry Name)) : Bool :=
 removed.all fun entry => (typeSources entry.2).all fun source =>
 retained.all fun target => decide (target.1 ≠ source)

theorem crossCheck_exact (removed retained : List (Entry Name)) :
 crossCheck removed retained = true ↔ CrossRead removed retained := by
 simp [crossCheck,CrossRead,Avoid]

def retainedCheck (removed retained : List (Entry Name)) : Bool :=
 GeneralPresenceOwnerCheck244.disjointCheck removed retained &&
 crossCheck retained retained && crossCheck removed retained

theorem retainedCheck_exact (removed retained : List (Entry Name)) :
 retainedCheck removed retained = true ↔
 (DisjointTargets removed retained ∧ External retained) ∧ CrossRead removed retained := by
 simp only [retainedCheck,Bool.and_eq_true,GeneralPresenceOwnerCheck244.disjointCheck_exact,crossCheck_exact,External]

theorem checked_external (removed retained : List (Entry Name))
 (checked : retainedCheck removed retained = true) : External (transform (substitution removed) retained) := by
 obtain ⟨⟨_,external⟩,cross⟩ := (retainedCheck_exact ..).mp checked
 exact transformed_external removed retained cross external

theorem checked_shape (removed retained : List (Entry Name))
 (checked : retainedCheck removed retained = true) :
 (block retained).map (atomSubst (substitution removed)) = block (transform (substitution removed) retained) :=
 owner_block_shape removed retained ((retainedCheck_exact ..).mp checked).1.1

theorem checked_models (removed retained : List (Entry Name))
 (checked : retainedCheck removed retained = true) (model : Model) (assignment : Name → Comp model) :
 PresenceNormalForm.All model assignment (block (transform (substitution removed) retained)) ↔
 PresenceNormalForm.All model (fun name => (substitution removed name).eval model assignment) (block retained) :=
 owner_block_exact removed retained ((retainedCheck_exact ..).mp checked).1.1 model assignment

theorem no_cycle_pass : retainedCheck ([(2,.var 3)] : List (Entry Nat)) [(3,.var 2)] = false := by decide

theorem simple_pass : retainedCheck ([(2,.var 1)] : List (Entry Nat)) [(3,.var 2)] = true := by decide
end Yulang.GeneralPresenceCrossRead244
