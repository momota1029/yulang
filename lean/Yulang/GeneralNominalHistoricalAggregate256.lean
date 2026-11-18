import Yulang.GeneralNominalAggregateAtoms256
import Yulang.GeneralPresenceSnapshotBlock250
import Yulang.GeneralNominalRebaseProjectionView243
import Yulang.GeneralPresenceNormalFinite252
namespace Yulang.GeneralNominalHistoricalAggregate256
open Core.PresenceGeneration
open GeneralNominalAllocation (lower upper)
open GeneralSourceState (Interval)
open GeneralPresenceDefinitionRewrite244 (Entry)
open GeneralPresenceOrderedSubstitution247 (mapping)
open GeneralPresenceOrderedBlock247 (solve)
open GeneralPresenceCheckedNormal252
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

/-- The check is over the actual old-snapshot values of the occurrence
endpoints, with their lower/upper roles kept distinct. -/
def EndpointSupported (pool : List (TyTerm Nat)) (old : List (Entry Nat)) (pairs : List Interval) : Prop :=
 (∀ pair ∈ pairs, atoms .lower (mapping old pair.1).ty ⊆ pool) ∧
 (∀ pair ∈ pairs, atoms .upper (mapping old pair.2).ty ⊆ pool)

def rewrite (pool : List (TyTerm Nat)) (old : List (Entry Nat)) (pairs : List Interval) :
 GeneralNominalRebaseProjectionView243.Bounds :=
 ⟨normalize .lower pool ((lower pairs).subst (mapping old)),
  normalize .upper pool ((upper pairs).subst (mapping old))⟩

def check (pool : List (TyTerm Nat)) (old : List (Entry Nat)) (pairs : List Interval) : Bool :=
 pairs.all (fun pair => GeneralPresenceCheckedNormal252.check .lower pool (mapping old pair.1).ty &&
   GeneralPresenceCheckedNormal252.check .upper pool (mapping old pair.2).ty)

def prepare (pool : List (TyTerm Nat)) (old : List (Entry Nat)) (pairs : List Interval) :
 Option GeneralNominalRebaseProjectionView243.Bounds :=
 if pairs.isEmpty then none else if check pool old pairs then some (rewrite pool old pairs) else none

theorem check_exact (pool : List (TyTerm Nat)) (old : List (Entry Nat)) (pairs : List Interval) :
 check pool old pairs = true ↔ EndpointSupported pool old pairs := by
 simp only [check,List.all_eq_true,Bool.and_eq_true,GeneralPresenceCheckedNormal252.check_exact,EndpointSupported]
 exact ⟨fun h => ⟨fun p m => (h p m).1,fun p m => (h p m).2⟩,
   fun h p m => ⟨h.1 p m,h.2 p m⟩⟩

theorem supported_iff (pool : List (TyTerm Nat)) (old : List (Entry Nat)) (pairs : List Interval)
 (nonempty : pairs ≠ []) :
 EndpointSupported pool old pairs ↔
 atoms .lower ((lower pairs).subst (mapping old)) ⊆ pool ∧
 atoms .upper ((upper pairs).subst (mapping old)) ⊆ pool := by
 rw [GeneralNominalAggregateAtoms256.lower_supported_iff pairs nonempty,
   GeneralNominalAggregateAtoms256.upper_supported_iff pairs nonempty]
 rfl

theorem prepare_exact (pool : List (TyTerm Nat)) (old : List (Entry Nat)) (pairs : List Interval)
 (result : GeneralNominalRebaseProjectionView243.Bounds) :
 prepare pool old pairs = some result ↔ pairs ≠ [] ∧ EndpointSupported pool old pairs ∧ result = rewrite pool old pairs := by
 unfold prepare
 cases pairs with
 | nil => simp
 | cons first rest =>
   simp only [List.isEmpty_cons,Bool.false_eq_true,ite_false,ne_eq]
   by_cases yes : check pool old (first::rest) = true
   · simp [yes,(check_exact ..).mp yes,eq_comm]
   · have no : ¬ EndpointSupported pool old (first::rest) := fun h => yes ((check_exact ..).mpr h)
     simp [yes,no]

theorem values (pool : List (TyTerm Nat)) (old : List (Entry Nat)) (pairs : List Interval)
 (nonempty : pairs ≠ []) (supported : EndpointSupported pool old pairs) (assignment : Assignment) :
 Equivalent ((rewrite pool old pairs).lower.eval model assignment) ((lower pairs).eval model (solve model old assignment)) ∧
 Equivalent ((rewrite pool old pairs).upper.eval model assignment) ((upper pairs).eval model (solve model old assignment)) := by
 have both := (supported_iff pool old pairs nonempty).mp supported
 constructor
 · have same := GeneralPresenceCheckedNormal252.equivalent .lower pool _ _
     ((GeneralPresenceCheckedNormal252.prepare_exact ..).mpr ⟨both.1,rfl⟩) assignment
   rw [GeneralPresenceSnapshotBlock250.rhs_snapshot] at same
   exact same
 · have same := GeneralPresenceCheckedNormal252.equivalent .upper pool _ _
     ((GeneralPresenceCheckedNormal252.prepare_exact ..).mpr ⟨both.2,rfl⟩) assignment
   rw [GeneralPresenceSnapshotBlock250.rhs_snapshot] at same
   exact same

theorem fits_exact (pool : List (TyTerm Nat)) (old : List (Entry Nat)) (pairs : List Interval)
 (result : GeneralNominalRebaseProjectionView243.Bounds) (success : prepare pool old pairs = some result)
 (assignment : Assignment) (actual : Ty) :
 result.Fits assignment actual ↔ ∀ pair ∈ pairs, GeneralNominalCaptureMerges.Fits (solve model old assignment) pair actual := by
 obtain ⟨nonempty,supported,rfl⟩ := (prepare_exact ..).mp success
 have both := values pool old pairs nonempty supported assignment
 have low := GeneralNominalCaptureMerges.lower_exact (solve model old assignment) pairs nonempty actual
 have high := GeneralNominalCaptureMerges.upper_exact (solve model old assignment) pairs nonempty actual
 constructor
 · intro fits pair member
   exact ⟨low.mp (subtype_trans both.1.2 fits.1) pair member,
     high.mp (subtype_trans fits.2 both.2.1) pair member⟩
 · intro fits
   exact ⟨subtype_trans both.1.1 (low.mpr (fun p m => (fits p m).1)),
     subtype_trans (high.mpr (fun p m => (fits p m).2)) both.2.2⟩

theorem finite (pool : List (TyTerm Nat)) (old : List (Entry Nat)) (pairs : List Interval) :
 (rewrite pool old pairs).lower ∈ GeneralPresenceNormalFinite252.lowerCandidates pool ∧
 (rewrite pool old pairs).upper ∈ GeneralPresenceNormalFinite252.upperCandidates pool :=
 ⟨GeneralPresenceNormalFinite252.lower_enumerated ..,GeneralPresenceNormalFinite252.upper_enumerated ..⟩
end Yulang.GeneralNominalHistoricalAggregate256
