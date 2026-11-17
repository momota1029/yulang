import Yulang.GeneralNominalRebaseMergeExternal242
/-! Executable finite lookup implements the old substitution under its existing
coherence premise. No unbounded choice is needed to build replacement syntax. -/
namespace Yulang.GeneralNominalRebaseLookup242
open GeneralNominalFiniteEquationRealization236 (Entry)
open GeneralNominalRebaseEscapedProjection242 (Coherent)
open Core.PresenceGeneration (CompTerm TyTerm)

def lookup (entries : List Entry) (name : Nat) : Option Entry :=
 entries.find? (fun entry => entry.1 == name)

def substitution (entries : List Entry) (name : Nat) : CompTerm Nat :=
 match lookup entries name with
 | some entry => ⟨entry.2,.var name⟩
 | none => CompTerm.var name

theorem substitution_exact (entries : List Entry) (coherent : Coherent entries) (name : Nat) :
 substitution entries name = GeneralNominalRebaseInline241.substitution entries name := by
 unfold substitution
 cases found : lookup entries name with
 | none =>
   have absent : ∀ entry ∈ entries, entry.1 ≠ name := by
     intro entry member same
     have missing := List.find?_eq_none.mp found entry member
     simp [same] at missing
   exact (GeneralNominalRebaseInlineSyntax241.outside absent).symm
 | some entry =>
   have member := List.mem_of_find?_eq_some found
   have equal : entry.1 = name := by simpa using (List.find?_some found)
   subst name
   exact (GeneralNominalRebaseInlineSyntax241.at_entry coherent member).symm

def patch (entries : List Entry) (model : GeneralNominalCommonBridge.Assignment) :
 GeneralNominalCommonBridge.Assignment :=
 fun name => (substitution entries name).eval CommonNominalFullCarrier.model model

theorem patch_exact (entries : List Entry) (coherent : Coherent entries) (model : GeneralNominalCommonBridge.Assignment) :
 patch entries model = GeneralNominalFiniteEquationRealization236.patch entries model := by
 funext name
 unfold patch
 rw [substitution_exact entries coherent name]
 exact GeneralNominalRebaseInline241.substitution_eval coherent model name

def rewrite (oldEntries newEntries : List Entry) : List Entry :=
 newEntries.map (fun entry => (entry.1,entry.2.subst (substitution oldEntries)))

theorem rewrite_exact (oldEntries newEntries : List Entry) (coherent : Coherent oldEntries) :
 rewrite oldEntries newEntries = GeneralNominalRebaseMergeExternal242.rewrite oldEntries newEntries := by
 unfold rewrite GeneralNominalRebaseMergeExternal242.rewrite
 have same : substitution oldEntries = GeneralNominalRebaseInline241.substitution oldEntries :=
   funext (substitution_exact oldEntries coherent)
 rw [same]

theorem rewrite_external (oldEntries newEntries : List Entry)
 (coherent : Coherent oldEntries) (external : GeneralNominalRebaseEscapedProjection242.External oldEntries)
 (pure : ∀ entry ∈ newEntries, GeneralNominalRebaseMergeExternal242.MergeTerm entry.2)
 (within : GeneralNominalRebaseEscapedReplace242.TargetsWithin newEntries oldEntries) :
 GeneralNominalRebaseEscapedProjection242.External (rewrite oldEntries newEntries) := by
 rw [rewrite_exact oldEntries newEntries coherent]
 exact GeneralNominalRebaseMergeExternal242.rewrite_external oldEntries newEntries coherent external pure within

theorem patch_row (entries : List Entry) (model : GeneralNominalCommonBridge.Assignment) (name : Nat) :
 (patch entries model name).2 = (model name).2 := by
 unfold patch substitution
 cases lookup entries name <;> rfl

theorem self_reference_rewritten :
 rewrite [(3,.var 0)] [(3,.union (.var 3) (.var 3))] = [(3,.union (.var 0) (.var 0))] := rfl

theorem untouched_reference : substitution [(3,.var 0)] 2 = CompTerm.var 2 := rfl

end Yulang.GeneralNominalRebaseLookup242
