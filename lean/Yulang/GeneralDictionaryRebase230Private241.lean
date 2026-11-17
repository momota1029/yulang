import Yulang.GeneralDictionaryUpper230Current
import Yulang.GeneralNominalRebaseProjection241
import Yulang.GeneralDictionaryOptionalInstall229
import Yulang.GeneralDictionaryDefaultMergeRevisionProbe210
set_option backward.isDefEq.respectTransparency false
/-! Reconstructed private 230 regression, freshly verified.
The protected raw source and actual center are preserved. This is not a
replacement of the complete historical journal. -/
namespace Yulang.GeneralDictionaryRebase230Private241
open GeneralDeclarations GeneralNominalAllocation CommonNominalFullCarrier
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229
open GeneralDictionaryOptionalInstall229 (model lo hi actual)
open GeneralDictionaryDefaultMergeRevisionProbe210 (twice)
open GeneralNominalRebaseProjection241
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredFrame179 (Agree)
abbrev oldBindings := twice 0 4 2
abbrev newBindings := twice 0 2 2
def pool : List Nat := [0,1,2,3,4,actual]
noncomputable def rebased := GeneralNominalRebaseDefinitions241.patch snapshot.seed root.identity declaration.id
 newBindings declaration.inputNames model

theorem named_zero {name : Nat} (named : name ∈ declaration.inputNames) : name = 0 := by
 simpa [Declaration.inputNames,GeneralDeclarationPatterns.variablesArgs,
   GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
   GeneralDeclarationPatterns.Pattern.variables] using named

theorem raw_support (name : Nat) (member : name ∈ GeneralNominalState.sources snapshot) : name ∈ pool := by
 have small := source_bound name member
 simp only [pool,List.mem_cons]
 omega

theorem isolated : GeneralNominalRebaseDefinitions241.Fresh snapshot.seed root.identity declaration.id
 newBindings declaration.inputNames pool := by
 intro name named _
 have zero := named_zero named
 subst name
 have loLarge := GeneralDictionaryOptionalInstall229.fresh_large 0
 have hiLarge := GeneralDictionaryOptionalInstall229.fresh_large 1
 have loNe : lo ≠ actual := GeneralNominalCenteredAllocation.fresh_namespaces (by decide : (0:Nat) ≠ 8)
 have hiNe : hi ≠ actual := GeneralNominalCenteredAllocation.fresh_namespaces (by decide : (1:Nat) ≠ 8)
 change 4 < lo at loLarge
 change 4 < hi at hiLarge
 change lo ∉ pool ∧ hi ∉ pool
 simp only [pool,List.mem_cons,List.not_mem_nil,or_false]
 constructor <;> omega

theorem linked : GeneralNominalAllocationSupport.Endpoints newBindings pool := by
 intro binding member
 rcases List.mem_cons.mp member with rfl | member
 · exact ⟨by simp [pool],by simp [pool]⟩
 · cases List.mem_singleton.mp member
   exact ⟨by simp [pool],by simp [pool]⟩

theorem nonempty : ∀ name ∈ declaration.inputNames, occurrences newBindings name ≠ [] := by
 intro name named
 have zero := named_zero named
 subst name
 decide

theorem actual_protected : ∀ name ∈ declaration.inputNames, actual ∈ pool := by
 intro _ _
 simp [pool]

theorem agrees : Agree pool rebased model :=
 GeneralNominalRebaseDefinitions241.preserves _ _ _ _ _ isolated

theorem raw_models : GeneralNominalState.Models snapshot rebased :=
 (raw_supported snapshot raw_support rebased model agrees).mpr GeneralDictionaryOptionalInstall229.source_model

theorem new_merges : PresenceNormalForm.All CommonNominalFullCarrier.model rebased
 (merges snapshot registry root.identity declaration newBindings) :=
 GeneralNominalRebaseDefinitions241.merges snapshot registry root.identity declaration newBindings model isolated linked

theorem old_report_bindings : GeneralDictionaryOptionalInstall229.packet.bindings = oldBindings :=
 GeneralDictionaryOptionalInstall229.bindings_exact

theorem new_report_bindings : GeneralDictionaryUpper230Current.packet.bindings = newBindings :=
 GeneralDictionaryUpper230Current.bindings_exact

theorem old_merges : PresenceNormalForm.All CommonNominalFullCarrier.model model
 (merges snapshot registry root.identity declaration oldBindings) := by
 have old := GeneralDictionaryOptionalInstall229.packet_holds.2.1.1.2.1
 rw [old_report_bindings] at old
 exact old

theorem source_fits : SourceFits declaration newBindings (fun _ => actual) rebased := by
 intro name named bounds member
 have zero := named_zero named
 subst name
 have equal : bounds = (2,2) := by simpa [newBindings,twice,occurrences] using member
 subst bounds
 have two := agrees 2 (by simp [pool])
 have center := agrees actual (by simp [pool])
 change Subtype (rebased 2).1 (rebased actual).1 ∧ Subtype (rebased actual).1 (rebased 2).1
 rw [two,center,GeneralDictionaryOptionalInstall229.actual_value]
 change Subtype .emptyRecord .emptyRecord ∧ Subtype .emptyRecord .emptyRecord
 exact ⟨subtype_refl _,subtype_refl _⟩

theorem actual_fits : CapturedFits snapshot registry root.identity declaration newBindings (fun _ => actual) rebased :=
 (captured_iff snapshot registry root.identity declaration newBindings (fun _ => actual)
   nonempty rebased new_merges).mpr source_fits

theorem same_lower_cell :
 ((capture snapshot registry root.identity declaration.id oldBindings).inputs 0).1 =
 ((capture snapshot registry root.identity declaration.id newBindings).inputs 0).1 := rfl

theorem same_upper_cell :
 ((capture snapshot registry root.identity declaration.id oldBindings).inputs 0).2 =
 ((capture snapshot registry root.identity declaration.id newBindings).inputs 0).2 := rfl

theorem incompatible (assignment : Assignment)
 (oldValue : (assignment 4).1 = GeneralDictionaryOptionalOutput229.value)
 (newValue : (assignment 2).1 = .emptyRecord)
 (old : PresenceNormalForm.All CommonNominalFullCarrier.model assignment
   (merges snapshot registry root.identity declaration oldBindings))
 (new : PresenceNormalForm.All CommonNominalFullCarrier.model assignment
   (merges snapshot registry root.identity declaration newBindings)) : False := by
 have equal := GeneralDictionaryDefaultMergeRevisionProbe210.reused_lower_forces_equivalence
   (name := 0) (by decide : 0 ∈ declaration.inputNames) old new
 rw [oldValue,newValue] at equal
 exact GeneralDictionaryOptionalOutput229.not_width equal

theorem rejects_stale : ¬ PresenceNormalForm.All CommonNominalFullCarrier.model rebased
 (merges snapshot registry root.identity declaration oldBindings) := by
 intro old
 apply incompatible rebased _ _ old new_merges
 · rw [agrees 4 (by simp [pool])]
   rfl
 · rw [agrees 2 (by simp [pool])]
   rfl

theorem new_lower_width : Equivalent (rebased lo).1 .emptyRecord := by
 have equal := GeneralDictionaryDefaultMergeRevisionProbe210.repeated_lower_value
   (name := 0) (by decide : 0 ∈ declaration.inputNames) new_merges
 change Equivalent (rebased lo).1 (rebased 2).1 at equal
 rw [agrees 2 (by simp [pool])] at equal
 exact equal

theorem actual_width : (rebased actual).1 = .emptyRecord := by
 rw [agrees actual (by simp [pool])]
 exact GeneralDictionaryOptionalInstall229.actual_value

theorem projection_witness : ∃ extension : Assignment, Agree pool extension model ∧
 GeneralNominalState.Models snapshot extension ∧
 PresenceNormalForm.All CommonNominalFullCarrier.model extension
   (merges snapshot registry root.identity declaration newBindings) ∧
 CapturedFits snapshot registry root.identity declaration newBindings (fun _ => actual) extension :=
 ⟨rebased,agrees,raw_models,new_merges,actual_fits⟩

def publicAtoms : List (PresenceNormalForm.Atom Nat) :=
 cross oldBindings ++ GeneralNominalRecursiveInspection.selfChecks snapshot
   (GeneralNominalRecursiveCandidates.report GeneralDictionaryOptionalInstall229.packet.context declaration [(0,0)])

theorem public_support : ∀ atom ∈ publicAtoms, ∀ name ∈ GeneralNominalState.atomSources atom, name ∈ pool := by
 rw [show publicAtoms = cross oldBindings ++ GeneralNominalRecursiveInspection.selfChecks snapshot
   GeneralDictionaryOptionalInstall229.calculated by unfold publicAtoms; rw [GeneralDictionaryOptionalInstall229.report_exact]]
 decide

theorem old_public : PresenceNormalForm.All CommonNominalFullCarrier.model model publicAtoms := by
 have ordinary := GeneralDictionaryOptionalInstall229.packet_holds.2.1.1
 apply (PresenceNormalForm.all_append ..).mpr
 constructor
 · apply (cross_exact oldBindings model).mpr
   simpa only [old_report_bindings] using ordinary.1
 · exact ordinary.2.2

theorem retained_public : PresenceNormalForm.All CommonNominalFullCarrier.model rebased publicAtoms :=
 (atoms_supported publicAtoms public_support rebased model agrees).mpr old_public

theorem current_merge_formula :
 merges GeneralDictionaryUpper230Current.packet.context.state registry root.identity declaration
   GeneralDictionaryUpper230Current.packet.bindings =
 merges snapshot registry root.identity declaration newBindings := by
 rw [new_report_bindings]
 rfl
end Yulang.GeneralDictionaryRebase230Private241
