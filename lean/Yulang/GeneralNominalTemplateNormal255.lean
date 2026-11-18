import Yulang.GeneralNominalTemplateCongruence255
import Yulang.GeneralNominalViewFixed255
namespace Yulang.GeneralNominalTemplateNormal255
open Core.PresenceGeneration (TyTerm)
open GeneralNominalMaterialization (Mode)
open GeneralPresenceCheckedNormal252 (Side)
open GeneralNominalTemplateChoices255 (Raw Materialized reads choices)
open CommonNominalFullCarrier
abbrev Variables := Mode → Nat → TyTerm Nat

def leafCandidates (basis : List (TyTerm Nat)) : List (TyTerm Nat) :=
 GeneralNominalViewFixed255.candidates .lower basis ++ GeneralNominalViewFixed255.candidates .upper basis

def normalized (policy : Mode → Side) (basis : List (TyTerm Nat)) (variables : Variables) : Variables :=
 fun mode name => GeneralPresenceCheckedNormal252.normalize (policy mode) basis (variables mode name)

def Supported (policy : Mode → Side) (basis : List (TyTerm Nat)) (variables : Variables) (mode : Mode) (term : Raw) : Prop :=
 ∀ entry ∈ reads mode term, GeneralPresenceCheckedNormal252.atoms (policy entry.1) (variables entry.1 entry.2) ⊆ basis

def check (policy : Mode → Side) (basis : List (TyTerm Nat)) (variables : Variables) (mode : Mode) (term : Raw) : Bool :=
 (reads mode term).all fun entry => GeneralPresenceCheckedNormal252.check (policy entry.1) basis (variables entry.1 entry.2)

def rewrite (policy : Mode → Side) (basis : List (TyTerm Nat)) (variables : Variables) (mode : Mode) (term : Raw) : Materialized :=
 GeneralNominalRebaseEffectView243.compile (normalized policy basis variables) mode term

def prepare (policy : Mode → Side) (basis : List (TyTerm Nat)) (variables : Variables) (mode : Mode) (term : Raw) : Option Materialized :=
 if check policy basis variables mode term then some (rewrite policy basis variables mode term) else none

theorem check_exact (policy : Mode → Side) (basis : List (TyTerm Nat)) (variables : Variables) (mode : Mode) (term : Raw) :
 check policy basis variables mode term = true ↔ Supported policy basis variables mode term := by
 simp only [check,Supported,List.all_eq_true,GeneralPresenceCheckedNormal252.check_exact]

theorem prepare_exact (policy : Mode → Side) (basis : List (TyTerm Nat)) (variables : Variables) (mode : Mode) (term : Raw) (result : Materialized) :
 prepare policy basis variables mode term = some result ↔ Supported policy basis variables mode term ∧ result = rewrite policy basis variables mode term := by
 unfold prepare
 split
 · rename_i accepted
   simp only [Option.some.injEq]
   exact ⟨fun same => ⟨(check_exact ..).mp accepted,same.symm⟩,fun h => h.2.symm⟩
 · rename_i rejected
   constructor
   · intro impossible; cases impossible
   · intro h; exact False.elim (rejected ((check_exact ..).mpr h.1))

theorem normalized_candidate (policy : Mode → Side) (basis : List (TyTerm Nat)) (variables : Variables) (mode : Mode) (name : Nat) :
 normalized policy basis variables mode name ∈ leafCandidates basis := by
 have present := GeneralNominalViewFixed255.normalized_candidate (policy mode) basis (variables mode name)
 unfold normalized
 cases h : policy mode
 · exact List.mem_append_left _ (h ▸ present)
 · exact List.mem_append_right _ (h ▸ present)

theorem rewrite_finite (policy : Mode → Side) (basis : List (TyTerm Nat)) (variables : Variables) (mode : Mode) (term : Raw) :
 rewrite policy basis variables mode term ∈ choices (leafCandidates basis) term :=
 GeneralNominalTemplateChoices255.compiled_mem _ _ mode term (fun entry _ => normalized_candidate policy basis variables entry.1 entry.2)

theorem rewrite_equivalent (policy : Mode → Side) (basis : List (TyTerm Nat)) (variables : Variables) (mode : Mode) (term : Raw)
 (supported : Supported policy basis variables mode term) (assignment : GeneralNominalCommonBridge.Assignment) :
 Equivalent (GeneralNominalRebaseEffectView243.eval assignment (rewrite policy basis variables mode term))
 (GeneralNominalRebaseEffectView243.eval assignment (GeneralNominalRebaseEffectView243.compile variables mode term)) := by
 apply GeneralNominalTemplateCongruence255.compiled_equivalent
 intro entry member
 exact GeneralPresenceCheckedNormal252.equivalent _ _ _ _
   ((GeneralPresenceCheckedNormal252.prepare_exact ..).mpr ⟨supported entry member,rfl⟩) assignment

theorem prepare_safe (policy : Mode → Side) (basis : List (TyTerm Nat)) (variables : Variables) (mode : Mode) (term : Raw) (result : Materialized)
 (success : prepare policy basis variables mode term = some result) (assignment : GeneralNominalCommonBridge.Assignment) :
 result ∈ choices (leafCandidates basis) term ∧
 Equivalent (GeneralNominalRebaseEffectView243.eval assignment result)
 (GeneralNominalRebaseEffectView243.eval assignment (GeneralNominalRebaseEffectView243.compile variables mode term)) := by
 obtain ⟨supported,rfl⟩ := (prepare_exact ..).mp success
 exact ⟨rewrite_finite policy basis variables mode term,rewrite_equivalent policy basis variables mode term supported assignment⟩
end Yulang.GeneralNominalTemplateNormal255
