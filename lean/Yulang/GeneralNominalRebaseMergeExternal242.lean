import Yulang.GeneralNominalRebaseEscapedMerges242
import Yulang.GeneralNominalRebaseInlineSyntax241
set_option backward.isDefEq.respectTransparency false
/-! Externalizing new merge RHS terms through old definitions. The new RHS
fragment has variables, unions, intersections and constants, without row terms. -/
namespace Yulang.GeneralNominalRebaseMergeExternal242
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalFiniteEquationRealization236
open GeneralNominalRebaseEscapedProjection242
open GeneralNominalRebaseEscapedReplace242
open GeneralNominalRebaseInline241
open Core.PresenceGeneration (TyTerm)
open GeneralNominalAllocation (Bindings lower upper occurrences)

inductive MergeTerm : TyTerm Nat → Prop where
 | var (name) : MergeTerm (.var name)
 | bottom : MergeTerm .bottom
 | top : MergeTerm .top
 | union : MergeTerm a → MergeTerm b → MergeTerm (.union a b)
 | inter : MergeTerm a → MergeTerm b → MergeTerm (.inter a b)

def Outside (entries : List Entry) (term : TyTerm Nat) : Prop :=
 ∀ name ∈ GeneralNominalState.typeSources term, ∀ entry ∈ entries, entry.1 ≠ name

theorem variable_external (entries : List Entry) (coherent : Coherent entries)
 (external : External entries) (name : Nat) :
 Outside entries ((TyTerm.var name).subst (substitution entries)) := by
 classical
 by_cases found : ∃ entry ∈ entries, entry.1 = name
 · obtain ⟨entry,member,rfl⟩ := found
   simp only [TyTerm.subst,GeneralNominalRebaseInlineSyntax241.at_entry coherent member]
   exact external entry member
 · have absent : ∀ entry ∈ entries, entry.1 ≠ name :=
     fun entry member equal => found ⟨entry,member,equal⟩
   simp only [TyTerm.subst,GeneralNominalRebaseInlineSyntax241.outside absent,
     Core.PresenceGeneration.CompTerm.var]
   intro source present entry member
   cases List.mem_singleton.mp present
   exact absent entry member

theorem term_external (entries : List Entry) (coherent : Coherent entries)
 (external : External entries) {term : TyTerm Nat} (pure : MergeTerm term) :
 Outside entries (term.subst (substitution entries)) := by
 induction pure with
 | var name => exact variable_external entries coherent external name
 | bottom => intro name member; cases member
 | top => intro name member; cases member
 | union one two ihOne ihTwo =>
   intro name member entry present
   rcases List.mem_append.mp member with first | last
   · exact ihOne name first entry present
   · exact ihTwo name last entry present
 | inter one two ihOne ihTwo =>
   intro name member entry present
   rcases List.mem_append.mp member with first | last
   · exact ihOne name first entry present
   · exact ihTwo name last entry present

theorem lower_pure (bounds : List GeneralSourceState.Interval) : MergeTerm (lower bounds) := by
 induction bounds with
 | nil => exact .bottom
 | cons head tail ih =>
   cases tail with
   | nil => exact .var _
   | cons next rest => exact .union (.var _) ih

theorem upper_pure (bounds : List GeneralSourceState.Interval) : MergeTerm (upper bounds) := by
 induction bounds with
 | nil => exact .top
 | cons head tail ih =>
   cases tail with
   | nil => exact .var _
   | cons next rest => exact .inter (.var _) ih

noncomputable def rewrite (oldEntries newEntries : List Entry) : List Entry :=
 newEntries.map (fun entry => (entry.1,entry.2.subst (substitution oldEntries)))

theorem rewrite_coherent (oldEntries newEntries : List Entry) (coherent : Coherent newEntries) :
 Coherent (rewrite oldEntries newEntries) := by
 intro first member last included same
 obtain ⟨one,oneMem,rfl⟩ := List.mem_map.mp member
 obtain ⟨two,twoMem,rfl⟩ := List.mem_map.mp included
 exact congrArg (fun term : TyTerm Nat => term.subst (substitution oldEntries))
   (coherent one oneMem two twoMem same)

theorem rewrite_targets (oldEntries newEntries : List Entry)
 (within : TargetsWithin newEntries oldEntries) : TargetsWithin (rewrite oldEntries newEntries) oldEntries := by
 intro entry member
 obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
 exact within original present

theorem rewrite_external (oldEntries newEntries : List Entry)
 (coherent : Coherent oldEntries) (external : External oldEntries)
 (pure : ∀ entry ∈ newEntries, MergeTerm entry.2)
 (within : TargetsWithin newEntries oldEntries) : External (rewrite oldEntries newEntries) := by
 intro entry member name source target present
 obtain ⟨original,originalMem,rfl⟩ := List.mem_map.mp member
 obtain ⟨old,oldMem,equal⟩ := rewrite_targets oldEntries newEntries within target present
 intro collision
 exact term_external oldEntries coherent external (pure original originalMem)
   name source old oldMem (equal.trans collision)

theorem rewrite_eval (oldEntries : List Entry) (coherent : Coherent oldEntries)
 (term : TyTerm Nat) (model : Assignment) :
 (term.subst (substitution oldEntries)).eval CommonNominalFullCarrier.model model =
 term.eval CommonNominalFullCarrier.model (patch oldEntries model) := by
 rw [TyTerm.eval_subst]
 have same := funext (substitution_eval coherent model)
 rw [same]

theorem rewritten_definitions_iff (oldEntries newEntries : List Entry)
 (coherent : Coherent oldEntries) (model : Assignment) :
 Definitions (rewrite oldEntries newEntries) model ↔
 ∀ entry ∈ newEntries, CommonNominalFullCarrier.Equivalent (model entry.1).1
   (entry.2.eval CommonNominalFullCarrier.model (patch oldEntries model)) := by
 constructor
 · intro valid entry member
   have equations := valid (entry.1,entry.2.subst (substitution oldEntries))
     (List.mem_map.mpr ⟨entry,member,rfl⟩)
   have exactValue := (GeneralNominalCaptureMerges.equations_exact ..).mp equations
   rw [rewrite_eval oldEntries coherent entry.2 model] at exactValue
   exact exactValue
 · intro valid entry member
   obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
   apply (GeneralNominalCaptureMerges.equations_exact ..).mpr
   rw [rewrite_eval oldEntries coherent original.2 model]
   exact valid original present

theorem merge_entries_pure (seed root declaration : Nat) (bindings : Bindings) (names : List Nat) :
 ∀ entry ∈ GeneralNominalRebaseDefinitions241.entries seed root declaration bindings names,
 MergeTerm entry.2 := by
 intro entry member
 obtain ⟨name,_,_,rfl | rfl⟩ := (GeneralNominalRebaseDefinitions241.member_iff ..).mp member
 · exact lower_pure _
 · exact upper_pure _

theorem actual_rewrite_external (oldEntries : List Entry)
 (coherent : Coherent oldEntries) (external : External oldEntries)
 (seed root declaration : Nat) (bindings : Bindings) (names : List Nat)
 (within : TargetsWithin (GeneralNominalRebaseDefinitions241.entries seed root declaration bindings names) oldEntries) :
 External (rewrite oldEntries (GeneralNominalRebaseDefinitions241.entries seed root declaration bindings names)) :=
 rewrite_external oldEntries _ coherent external (merge_entries_pure seed root declaration bindings names) within

theorem replacement_projection (oldEntries : List Entry)
 (coherent : Coherent oldEntries) (external : External oldEntries)
 (seed root declaration : Nat) (bindings : Bindings) (names : List Nat)
 (within : TargetsWithin (GeneralNominalRebaseDefinitions241.entries seed root declaration bindings names) oldEntries)
 (atoms : List (PresenceNormalForm.Atom Nat)) (model : Assignment) :
 (∃ old, Preserves oldEntries old model ∧ Definitions oldEntries old ∧
   PresenceNormalForm.All CommonNominalFullCarrier.model old atoms) ↔
 (∃ next, Preserves oldEntries next model ∧
   Definitions (rewrite oldEntries (GeneralNominalRebaseDefinitions241.entries seed root declaration bindings names)) next ∧
   PresenceNormalForm.All CommonNominalFullCarrier.model next
     (atoms.map (atomSubst (substitution oldEntries)))) :=
 replacement_projection_iff oldEntries _ coherent external
   (rewrite_coherent oldEntries _ (GeneralNominalRebaseDefinitions241.coherent seed root declaration bindings names))
   (actual_rewrite_external oldEntries coherent external seed root declaration bindings names within)
   (rewrite_targets oldEntries _ within) atoms model
end Yulang.GeneralNominalRebaseMergeExternal242
