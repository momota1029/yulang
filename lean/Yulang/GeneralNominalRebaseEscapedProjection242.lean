import Yulang.GeneralNominalRebaseInlineModels241
set_option backward.isDefEq.respectTransparency false
/-! Exact elimination of an external-RHS definition block from arbitrary
ordinary consumers. Consumer references to target cells are permitted. -/
namespace Yulang.GeneralNominalRebaseEscapedProjection242
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalFiniteEquationRealization236
open GeneralNominalRebaseInline241
open CommonNominalFullCarrier

def Coherent (entries : List Entry) : Prop :=
 ∀ first ∈ entries, ∀ last ∈ entries, first.1 = last.1 → first.2 = last.2

def External (entries : List Entry) : Prop :=
 ∀ entry ∈ entries, ∀ name ∈ GeneralNominalState.typeSources entry.2,
   ∀ target ∈ entries, target.1 ≠ name

def Definitions (entries : List Entry) (model : Assignment) : Prop :=
 ∀ entry ∈ entries, PresenceNormalForm.All CommonNominalFullCarrier.model model
   (GeneralNominalAllocation.equations entry.1 entry.2)

def Preserves (entries : List Entry) (extension model : Assignment) : Prop :=
 (∀ name, (∀ entry ∈ entries, entry.1 ≠ name) → extension name = model name) ∧
 (∀ name, (extension name).2 = (model name).2)

def support (entries : List Entry) : List Nat :=
 entries.flatMap (fun entry => GeneralNominalState.typeSources entry.2)

theorem external_support (external : External entries) :
 ∀ entry ∈ entries, entry.1 ∉ support entries := by
 intro entry member present
 obtain ⟨other,otherMem,source⟩ := List.mem_flatMap.mp present
 exact external other otherMem entry.1 source entry member rfl

theorem patch_preserves (entries : List Entry) (model : Assignment) :
 Preserves entries (patch entries model) model :=
 ⟨fun _ absent => outside entries absent,fun name => row entries name⟩

theorem patch_definitions (entries : List Entry) (coherent : Coherent entries)
 (external : External entries) (model : Assignment) :
 Definitions entries (patch entries model) :=
 equations entries coherent (external_support external)
   (fun entry member _ present => List.mem_flatMap.mpr ⟨entry,member,present⟩)

theorem extension_same (entries : List Entry) (coherent : Coherent entries)
 (external : External entries) (extension model : Assignment)
 (kept : Preserves entries extension model) (valid : Definitions entries extension) :
 GeneralNominalAssignmentCongruence238.Same extension (patch entries model) := by
 classical
 intro name
 refine ⟨?_,(kept.2 name).trans (row entries name).symm⟩
 by_cases found : ∃ entry ∈ entries, entry.1 = name
 · obtain ⟨entry,member,rfl⟩ := found
   rw [value entries coherent entry member]
   have exactValue := (GeneralNominalCaptureMerges.equations_exact extension entry.1 entry.2).mp
     (valid entry member)
   have same := GeneralNominalCenteredModelExtension.type_eval_same
     (first := extension) (last := model) entry.2
     (fun name present => kept.1 name (external entry member name present))
   rw [same] at exactValue
   exact exactValue
 · have absent : ∀ entry ∈ entries, entry.1 ≠ name :=
     fun entry member equal => found ⟨entry,member,equal⟩
   rw [kept.1 name absent,outside entries absent]
   exact ⟨subtype_refl _,subtype_refl _⟩

theorem projected_iff (entries : List Entry) (coherent : Coherent entries)
 (external : External entries) (atoms : List (PresenceNormalForm.Atom Nat))
 (model : Assignment) :
 (∃ extension, Preserves entries extension model ∧ Definitions entries extension ∧
   PresenceNormalForm.All CommonNominalFullCarrier.model extension atoms) ↔
 PresenceNormalForm.All CommonNominalFullCarrier.model model
   (atoms.map (atomSubst (substitution entries))) := by
 constructor
 · rintro ⟨extension,kept,definitions,consumers⟩
   apply (all_inline coherent atoms model).mpr
   exact (GeneralNominalAssignmentCongruence238.all_iff
     (extension_same entries coherent external extension model kept definitions) atoms).mp consumers
 · intro consumers
   refine ⟨patch entries model,patch_preserves entries model,
     patch_definitions entries coherent external model,?_⟩
   exact (all_inline coherent atoms model).mp consumers

/-- Replacement keeps the old source constraint as an inlined consumer block.
The new definitions and old definitions are not imposed on one assignment. -/
theorem replacement_back (entries : List Entry) (coherent : Coherent entries)
 (external : External entries) (consumers newBlock : List (PresenceNormalForm.Atom Nat))
 (model : Assignment)
 (valid : PresenceNormalForm.All CommonNominalFullCarrier.model model
   (newBlock ++ consumers.map (atomSubst (substitution entries)))) :
 PresenceNormalForm.All CommonNominalFullCarrier.model model newBlock ∧
 ∃ extension, Preserves entries extension model ∧ Definitions entries extension ∧
   PresenceNormalForm.All CommonNominalFullCarrier.model extension consumers := by
 have split := (PresenceNormalForm.all_append ..).mp valid
 exact ⟨split.1,(projected_iff entries coherent external consumers model).mpr split.2⟩
end Yulang.GeneralNominalRebaseEscapedProjection242
