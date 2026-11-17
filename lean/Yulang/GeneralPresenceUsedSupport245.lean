import Yulang.GeneralPresenceFixedInline244
namespace Yulang.GeneralPresenceUsedSupport245
open Core.PresenceGeneration
open GeneralPresenceDefinitionRewrite244 GeneralPresenceSubstitutionSupport244
open GeneralPresenceOwnerRewrite244 GeneralPresenceCrossRead244
variable {Name : Type} [DecidableEq Name]

def typedReads : TyTerm Name → List Name
 | .var name => [name]
 | .union a b | .inter a b | .pair a b | .record _ a b | .recordDefault _ a b => typedReads a ++ typedReads b
 | .required _ a | .variant _ a => typedReads a
 | .arrow a _ b _ => typedReads a ++ typedReads b
 | _ => []

def rowReads : TyTerm Name → List Name
 | .union a b | .inter a b | .pair a b | .record _ a b | .recordDefault _ a b => rowReads a ++ rowReads b
 | .required _ a | .variant _ a => rowReads a
 | .arrow a incoming b outgoing => rowReads a ++ rowSources incoming ++ rowReads b ++ rowSources outgoing
 | _ => []

omit [DecidableEq Name] in
theorem sources_split (term : TyTerm Name) (name : Name) :
 name ∈ typeSources term ↔ name ∈ typedReads term ∨ name ∈ rowReads term := by
 induction term <;> simp_all [typeSources,typedReads,rowReads,or_assoc,or_left_comm,or_comm]

theorem subst_sources (entries : List (Entry Name)) (term : TyTerm Name) (name : Name) :
 name ∈ typeSources (term.subst (substitution entries)) ↔
 name ∈ (typedReads term).flatMap (fun x => typeSources (substitution entries x).ty) ∨ name ∈ rowReads term := by
 induction term <;>
   simp_all [TyTerm.subst,typeSources,typedReads,rowReads,GeneralPresenceFixedInline244.row_fixed,
     List.flatMap_append,or_assoc,or_left_comm,or_comm]

def UsedSafe (removed retained : List (Entry Name)) : Prop :=
 ∀ entry ∈ retained, ∀ name ∈ typedReads entry.2,
   Avoid retained (typeSources (substitution removed name).ty)

def RowsSafe (retained : List (Entry Name)) : Prop :=
 ∀ entry ∈ retained, Avoid retained (rowReads entry.2)

/-- Exact finite-read characterization, including the unchanged row component.
No rank, acyclicity or source-boundary claim is built into this criterion. -/
theorem external_exact (removed retained : List (Entry Name)) :
 External (transform (substitution removed) retained) ↔ UsedSafe removed retained ∧ RowsSafe retained := by
 constructor
 · intro external
   constructor
   · intro entry member name read source present target targetMem
     exact external (entry.1,entry.2.subst (substitution removed)) (List.mem_map.mpr ⟨entry,member,rfl⟩)
       source ((subst_sources removed entry.2 source).mpr (Or.inl (List.mem_flatMap.mpr ⟨name,read,present⟩)))
       (target.1,target.2.subst (substitution removed)) (List.mem_map.mpr ⟨target,targetMem,rfl⟩)
   · intro entry member source present target targetMem
     exact external (entry.1,entry.2.subst (substitution removed)) (List.mem_map.mpr ⟨entry,member,rfl⟩)
       source ((subst_sources removed entry.2 source).mpr (Or.inr present))
       (target.1,target.2.subst (substitution removed)) (List.mem_map.mpr ⟨target,targetMem,rfl⟩)
 · rintro ⟨used,rows⟩ entry member source present target targetMem
   obtain ⟨original,originalMem,rfl⟩ := List.mem_map.mp member
   obtain ⟨other,otherMem,rfl⟩ := List.mem_map.mp targetMem
   rcases (subst_sources removed original.2 source).mp present with typed | row
   · obtain ⟨name,read,present⟩ := List.mem_flatMap.mp typed
     exact used original originalMem name read source present other otherMem
   · exact rows original originalMem source row other otherMem

/-- Only entries actually selected by typed lookup are relevant. -/
def ActiveCrossRead (removed retained : List (Entry Name)) : Prop :=
 ∀ entry ∈ retained, ∀ name ∈ typedReads entry.2, ∀ term,
 lookup removed name = some term → Avoid retained (typeSources term)

theorem external_active_exact (removed retained : List (Entry Name)) (external : External retained) :
 External (transform (substitution removed) retained) ↔ ActiveCrossRead removed retained := by
 rw [external_exact]
 constructor
 · rintro ⟨used,_⟩ entry member name read term found
   simpa [substitution,found] using used entry member name read
 · intro active
   constructor
   · intro entry member name read
     cases found : lookup removed name with
     | some term => simpa [substitution,found] using active entry member name read term found
     | none =>
       intro source present target targetMem
       have same : source = name := by simpa [substitution,found,typeSources] using present
       subst source
       exact external entry member name ((sources_split entry.2 name).mpr (Or.inl read)) target targetMem
   · intro entry member source present
     exact external entry member source ((sources_split entry.2 source).mpr (Or.inr present))

def avoidCheck (targets : List (Entry Name)) (sources : List Name) : Bool :=
 sources.all fun source => targets.all fun target => decide (target.1 ≠ source)

theorem avoidCheck_exact (targets : List (Entry Name)) (sources : List Name) :
 avoidCheck targets sources = true ↔ Avoid targets sources := by simp [avoidCheck,Avoid]

def activeCheck (removed retained : List (Entry Name)) : Bool :=
 retained.all fun entry => (typedReads entry.2).all fun name =>
   match lookup removed name with
   | none => true
   | some term => avoidCheck retained (typeSources term)

theorem activeCheck_exact (removed retained : List (Entry Name)) :
 activeCheck removed retained = true ↔ ActiveCrossRead removed retained := by
 simp only [activeCheck,List.all_eq_true,ActiveCrossRead]
 constructor
 · intro checked entry member name read term found
   have checked := checked entry member name read
   simpa [found,avoidCheck_exact] using checked
 · intro active entry member name read
   cases found : lookup removed name with
   | none => rfl
   | some term => exact (avoidCheck_exact ..).mpr (active entry member name read term found)

theorem checked_external_iff (removed retained : List (Entry Name)) (external : External retained) :
 activeCheck removed retained = true ↔ External (transform (substitution removed) retained) := by
 rw [activeCheck_exact,external_active_exact removed retained external]

/-- An unused replacement may mention a retained target without being inserted. -/
theorem unused_pass : activeCheck ([(2,.var 3)] : List (Entry Nat)) [(3,.var 1)] = true := by decide

theorem unused_old_rejects : crossCheck ([(2,.var 3)] : List (Entry Nat)) [(3,.var 1)] = false := by decide

theorem actual_cycle_rejects : activeCheck ([(2,.var 3)] : List (Entry Nat)) [(3,.var 2)] = false := by decide

end Yulang.GeneralPresenceUsedSupport245
