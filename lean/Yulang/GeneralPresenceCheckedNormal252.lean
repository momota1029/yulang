import Yulang.GeneralPresenceSnapshotNormal252
namespace Yulang.GeneralPresenceCheckedNormal252
open Core.PresenceGeneration
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

inductive Side where | lower | upper
 deriving DecidableEq

def atoms : Side → TyTerm Nat → List (TyTerm Nat)
 | .lower => GeneralPresenceUnionNormal252.atoms
 | .upper => GeneralPresenceInterNormal252.atoms

def normalize : Side → List (TyTerm Nat) → TyTerm Nat → TyTerm Nat
 | .lower => GeneralPresenceUnionNormal252.normalize
 | .upper => GeneralPresenceInterNormal252.normalize

def check (side : Side) (pool : List (TyTerm Nat)) (term : TyTerm Nat) : Bool :=
 (atoms side term).all (fun atom => atom ∈ pool)

def prepare (side : Side) (pool : List (TyTerm Nat)) (term : TyTerm Nat) : Option (TyTerm Nat) :=
 if check side pool term then some (normalize side pool term) else none

theorem check_exact (side : Side) (pool : List (TyTerm Nat)) (term : TyTerm Nat) :
 check side pool term = true ↔ atoms side term ⊆ pool := by
 simp only [check,List.all_eq_true,decide_eq_true_eq]
 exact ⟨fun h _ m => h _ m,fun h _ m => h m⟩

theorem prepare_exact (side : Side) (pool : List (TyTerm Nat)) (term result : TyTerm Nat) :
 prepare side pool term = some result ↔ atoms side term ⊆ pool ∧ result = normalize side pool term := by
 unfold prepare
 by_cases supported : check side pool term = true
 · simp [supported,(check_exact ..).mp supported,eq_comm]
 · have absent : ¬ atoms side term ⊆ pool := fun h => supported ((check_exact ..).mpr h)
   simp [supported,absent]

theorem equivalent (side : Side) (pool : List (TyTerm Nat)) (term result : TyTerm Nat)
 (success : prepare side pool term = some result) (assignment : Assignment) :
 Equivalent (result.eval model assignment) (term.eval model assignment) := by
 obtain ⟨supported,rfl⟩ := (prepare_exact ..).mp success
 cases side
 · exact GeneralPresenceUnionNormal252.equivalent pool term supported assignment
 · exact GeneralPresenceInterNormal252.equivalent pool term supported assignment

theorem normalized_supported (side : Side) (pool : List (TyTerm Nat)) (term : TyTerm Nat)
 (supported : atoms side term ⊆ pool) : atoms side (normalize side pool term) ⊆ pool := by
 cases side
 · change GeneralPresenceUnionNormal252.atoms (GeneralPresenceUnionNormal252.normalize pool term) ⊆ pool
   change GeneralPresenceUnionNormal252.atoms term ⊆ pool at supported
   unfold GeneralPresenceUnionNormal252.normalize
   rw [GeneralPresenceUnionNormal252.atoms_fold _
     (GeneralPresenceUnionNormal252.canonical_nonempty _ _ supported (GeneralPresenceUnionNormal252.atoms_nonempty term))
     (fun atom present => GeneralPresenceUnionNormal252.atoms_flat term atom
       ((GeneralPresenceUnionNormal252.canonical_mem ..).mp present).2)]
   exact fun _ present => ((GeneralPresenceUnionNormal252.canonical_mem ..).mp present).1
 · change GeneralPresenceInterNormal252.atoms (GeneralPresenceInterNormal252.normalize pool term) ⊆ pool
   change GeneralPresenceInterNormal252.atoms term ⊆ pool at supported
   unfold GeneralPresenceInterNormal252.normalize
   rw [GeneralPresenceInterNormal252.atoms_fold _
     (GeneralPresenceInterNormal252.canonical_nonempty _ _ supported (GeneralPresenceInterNormal252.atoms_nonempty term))
     (fun atom present => GeneralPresenceInterNormal252.atoms_flat term atom
       ((GeneralPresenceInterNormal252.canonical_mem ..).mp present).2)]
   exact fun _ present => ((GeneralPresenceInterNormal252.canonical_mem ..).mp present).1

theorem prepare_idempotent (side : Side) (pool : List (TyTerm Nat)) (term result : TyTerm Nat)
 (success : prepare side pool term = some result) : prepare side pool result = some result := by
 obtain ⟨supported,rfl⟩ := (prepare_exact ..).mp success
 apply (prepare_exact ..).mpr
 refine ⟨normalized_supported side pool term supported,?_⟩
 cases side
 · exact (GeneralPresenceUnionNormal252.idempotent pool term supported).symm
 · exact (GeneralPresenceInterNormal252.idempotent pool term supported).symm

theorem no_private_reads (side : Side) (pool : List (TyTerm Nat)) (term result : TyTerm Nat)
 (success : prepare side pool term = some result) (privateName : Nat)
 (separated : ∀ atom ∈ pool, privateName ∉ GeneralPresenceSubstitutionSupport244.typeSources atom) :
 privateName ∉ GeneralPresenceSubstitutionSupport244.typeSources result := by
 obtain ⟨_,rfl⟩ := (prepare_exact ..).mp success
 cases side
 · exact GeneralPresenceUnionNormal252.no_private_all_reads pool term privateName separated
 · exact GeneralPresenceInterNormal252.no_private_all_reads pool term privateName separated

theorem unsupported_mixed : prepare .lower [.var 0,.var 1] (.inter (.var 0) (.var 1)) = none := by decide

theorem duplicate_supported : prepare .lower [.var 0] (.union (.var 0) (.var 0)) = some (.var 0) := by decide
end Yulang.GeneralPresenceCheckedNormal252
