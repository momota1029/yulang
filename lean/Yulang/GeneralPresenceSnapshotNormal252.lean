import Yulang.GeneralPresenceNormalFinite252
namespace Yulang.GeneralPresenceSnapshotNormal252
open Core.PresenceGeneration
open GeneralPresenceOrderedBlock247 GeneralPresenceOrderedSubstitution247
open GeneralPresenceDefinitionRewrite244
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

theorem union_subst_atoms (term : TyTerm Nat) (replacement : Nat → CompTerm Nat) :
 GeneralPresenceUnionNormal252.atoms (term.subst replacement) =
 (GeneralPresenceUnionNormal252.atoms term).flatMap
   (fun atom => GeneralPresenceUnionNormal252.atoms (atom.subst replacement)) := by
 induction term <;> simp_all [GeneralPresenceUnionNormal252.atoms,TyTerm.subst,List.flatMap_append]

theorem inter_subst_atoms (term : TyTerm Nat) (replacement : Nat → CompTerm Nat) :
 GeneralPresenceInterNormal252.atoms (term.subst replacement) =
 (GeneralPresenceInterNormal252.atoms term).flatMap
   (fun atom => GeneralPresenceInterNormal252.atoms (atom.subst replacement)) := by
 induction term <;> simp_all [GeneralPresenceInterNormal252.atoms,TyTerm.subst,List.flatMap_append]

theorem union_subst_supported (pool : List (TyTerm Nat)) (term : TyTerm Nat) (replacement : Nat → CompTerm Nat)
 (closed : ∀ atom ∈ GeneralPresenceUnionNormal252.atoms term,
   GeneralPresenceUnionNormal252.atoms (atom.subst replacement) ⊆ pool) :
 GeneralPresenceUnionNormal252.atoms (term.subst replacement) ⊆ pool := by
 intro atom member
 rw [union_subst_atoms] at member
 obtain ⟨original,present,found⟩ := List.mem_flatMap.mp member
 exact closed original present found

theorem inter_subst_supported (pool : List (TyTerm Nat)) (term : TyTerm Nat) (replacement : Nat → CompTerm Nat)
 (closed : ∀ atom ∈ GeneralPresenceInterNormal252.atoms term,
   GeneralPresenceInterNormal252.atoms (atom.subst replacement) ⊆ pool) :
 GeneralPresenceInterNormal252.atoms (term.subst replacement) ⊆ pool := by
 intro atom member
 rw [inter_subst_atoms] at member
 obtain ⟨original,present,found⟩ := List.mem_flatMap.mp member
 exact closed original present found

def lower (pool : List (TyTerm Nat)) (old : List (Entry Nat)) (raw : TyTerm Nat) : TyTerm Nat :=
 GeneralPresenceUnionNormal252.normalize pool (raw.subst (mapping old))

def upper (pool : List (TyTerm Nat)) (old : List (Entry Nat)) (raw : TyTerm Nat) : TyTerm Nat :=
 GeneralPresenceInterNormal252.normalize pool (raw.subst (mapping old))

theorem lower_exact (pool : List (TyTerm Nat)) (old : List (Entry Nat)) (raw : TyTerm Nat)
 (closed : ∀ atom ∈ GeneralPresenceUnionNormal252.atoms raw,
   GeneralPresenceUnionNormal252.atoms (atom.subst (mapping old)) ⊆ pool) (assignment : Assignment) :
 Equivalent ((lower pool old raw).eval model assignment) (raw.eval model (solve model old assignment)) := by
 have same := GeneralPresenceUnionNormal252.equivalent pool _ (union_subst_supported pool raw _ closed) assignment
 rw [TyTerm.eval_subst] at same
 have environment : (fun name => (mapping old name).eval model assignment) = solve model old assignment :=
   funext (mapping_eval old model assignment)
 rw [environment] at same
 exact same

theorem upper_exact (pool : List (TyTerm Nat)) (old : List (Entry Nat)) (raw : TyTerm Nat)
 (closed : ∀ atom ∈ GeneralPresenceInterNormal252.atoms raw,
   GeneralPresenceInterNormal252.atoms (atom.subst (mapping old)) ⊆ pool) (assignment : Assignment) :
 Equivalent ((upper pool old raw).eval model assignment) (raw.eval model (solve model old assignment)) := by
 have same := GeneralPresenceInterNormal252.equivalent pool _ (inter_subst_supported pool raw _ closed) assignment
 rw [TyTerm.eval_subst] at same
 have environment : (fun name => (mapping old name).eval model assignment) = solve model old assignment :=
   funext (mapping_eval old model assignment)
 rw [environment] at same
 exact same

theorem lower_finite (pool : List (TyTerm Nat)) (old : List (Entry Nat)) (raw : TyTerm Nat) :
 lower pool old raw ∈ GeneralPresenceNormalFinite252.lowerCandidates pool :=
 GeneralPresenceNormalFinite252.lower_enumerated pool _

theorem upper_finite (pool : List (TyTerm Nat)) (old : List (Entry Nat)) (raw : TyTerm Nat) :
 upper pool old raw ∈ GeneralPresenceNormalFinite252.upperCandidates pool :=
 GeneralPresenceNormalFinite252.upper_enumerated pool _
end Yulang.GeneralPresenceSnapshotNormal252
