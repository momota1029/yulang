import Yulang.GeneralNominalMaterializedDomain249
import Yulang.GeneralNominalJournalCertificate249
/-! A finite owner-frame update rewrites every stored journal field and replaces
its ordered definitions. It is not yet the source scheduler's transition. -/
namespace Yulang.GeneralNominalMaterializedOwnerFrame249
open Core.PresenceGeneration PresenceNormalForm
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRebaseJournalView243 (Journal)
open GeneralNominalMaterializedDomain249
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOrderedBlock247
open GeneralPresenceOrderedSubstitution247 GeneralPresenceOrderedRebase247
open CommonNominalFullCarrier GeneralPresenceCommonLaws245

structure Frame where
 metadata : Journal
 consumers : List (Atom Nat)
 definitions : List (Entry Nat)

def Formed (frame : Frame) : Prop := Materialized frame.metadata ∧ SafeOrder frame.definitions

def Models (frame : Frame) (assignment : Assignment) : Prop :=
 frame.metadata.Models assignment ∧ All model assignment (frame.consumers ++ block frame.definitions)

def rebase (frame : Frame) (fresh : List (Entry Nat)) : Frame :=
 ⟨GeneralNominalJournalSubst249.subst (mapping frame.definitions) frame.metadata,
  rewrite frame.definitions frame.consumers,fresh⟩

def Protected (frame : Frame) (fresh : List (Entry Nat)) : Prop :=
 GeneralPresenceProtectionCheck249.Protected
   (GeneralNominalJournalSupport249.support (rebase frame fresh).metadata) fresh ∧
 GeneralPresenceOrderedExpansion249.Protected frame.definitions fresh frame.consumers

theorem rebase_formed (frame : Frame) (formed : Formed frame)
 (fresh : List (Entry Nat)) (safe : SafeOrder fresh) : Formed (rebase frame fresh) :=
 ⟨Materialized.substituted formed.1 (mapping frame.definitions),safe⟩

theorem models_forward (frame : Frame) (made : Materialized frame.metadata)
 (fresh : List (Entry Nat)) (safe : SafeOrder fresh) (protectedReads : Protected frame fresh)
 (assignment : Assignment) (valid : Models frame assignment) :
 Models (rebase frame fresh) (solve model fresh assignment) := by
 constructor
 · apply (GeneralNominalOrderedJournalExpansion249.journal_preserved
     (rebase frame fresh).metadata fresh assignment protectedReads.1).mpr
   apply (GeneralNominalJournalSubst249.ordered_exact frame.definitions assignment frame.metadata).mpr
   exact (GeneralNominalMaterializedDomain249.recovered made frame.definitions assignment
     ((all_append model assignment _ _).mp valid.2).2).mpr valid.1
 · exact GeneralPresenceOrderedExpansion249.models_forward model common_laws frame.definitions fresh safe
     frame.consumers protectedReads.2 assignment valid.2

theorem models_backward (frame : Frame) (safe : SafeOrder frame.definitions)
 (fresh : List (Entry Nat)) (assignment : Assignment) (valid : Models (rebase frame fresh) assignment) :
 Models frame (solve model frame.definitions assignment) :=
 ⟨(GeneralNominalJournalSubst249.ordered_exact frame.definitions assignment frame.metadata).mp valid.1,
  GeneralPresenceOrderedRebase247.models_backward model common_laws frame.definitions fresh safe frame.consumers assignment valid.2⟩

theorem public_models_iff (frame : Frame) (formed : Formed frame)
 (fresh : List (Entry Nat)) (safe : SafeOrder fresh) (protectedReads : Protected frame fresh)
 (sharedNames : Nat → Prop)
 (oldPrivate : ∀ name, sharedNames name → ∀ entry ∈ frame.definitions, entry.1 ≠ name)
 (freshPrivate : ∀ name, sharedNames name → ∀ entry ∈ fresh, entry.1 ≠ name)
 (boundary : Assignment) :
 (∃ assignment, Models frame assignment ∧ Agrees model sharedNames assignment boundary) ↔
 (∃ assignment, Models (rebase frame fresh) assignment ∧ Agrees model sharedNames assignment boundary) := by
 constructor
 · rintro ⟨assignment,valid,agree⟩
   refine ⟨solve model fresh assignment,models_forward frame formed.1 fresh safe protectedReads assignment valid,?_⟩
   intro name shared
   rw [solve_outside model fresh assignment name (freshPrivate name shared)]
   exact agree name shared
 · rintro ⟨assignment,valid,agree⟩
   refine ⟨solve model frame.definitions assignment,models_backward frame formed.2 fresh assignment valid,?_⟩
   intro name shared
   rw [solve_outside model frame.definitions assignment name (oldPrivate name shared)]
   exact agree name shared
end Yulang.GeneralNominalMaterializedOwnerFrame249
