import Yulang.GeneralPresenceOrderedCoherentAdapter247
import Yulang.GeneralPresenceOrderedSort247
/-! A checked finite preparation pipeline: coherent duplicate removal followed
by topological ordering. Successful preparation preserves the original equation
conjunction exactly and constructs its models. Failure is not a language error.
Actual source callers must supply coherence and establish successful coverage. -/
namespace Yulang.GeneralPresenceOrderedPrepared247
open Core.PresenceGeneration PresenceNormalForm
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOwnerRewrite244
open GeneralPresenceOrderedBlock247 GeneralPresenceOrderedDedup247
open GeneralPresenceOrderedSort247 GeneralPresenceOrderedRebase247
open GeneralPresenceOrderedSubstitution247 GeneralPresenceOrderedDependence247
open GeneralPresenceModelCongruence245
variable {Name : Type} [DecidableEq Name]

def prepare (entries : List (Entry Name)) : Option (List (Entry Name)) := sort (dedup entries)

omit [DecidableEq Name] in
theorem block_perm (model : Model) (assignment : Name → Comp model)
 (first last : List (Entry Name)) (perm : List.Perm first last) :
 All model assignment (block first) ↔ All model assignment (block last) := by
 constructor
 · intro valid atom member
   obtain ⟨entry,present,contained⟩ := List.mem_flatMap.mp member
   exact valid atom (List.mem_flatMap.mpr ⟨entry,perm.mem_iff.mpr present,contained⟩)
 · intro valid atom member
   obtain ⟨entry,present,contained⟩ := List.mem_flatMap.mp member
   exact valid atom (List.mem_flatMap.mpr ⟨entry,perm.mem_iff.mp present,contained⟩)

theorem prepared_safe (entries sorted : List (Entry Name)) (success : prepare entries = some sorted) :
 SafeOrder sorted := (sort_sound (dedup entries) sorted (targets_nodup entries) success).2

theorem prepared_subset (entries sorted : List (Entry Name)) (success : prepare entries = some sorted) :
 sorted ⊆ entries := by
 intro entry member
 exact dedup_subset entries ((sort_sound (dedup entries) sorted (targets_nodup entries) success).1.mem_iff.mpr member)

theorem prepared_members (entries sorted : List (Entry Name)) (coherent : Coherent entries)
 (success : prepare entries = some sorted) (entry : Entry Name) : entry ∈ entries ↔ entry ∈ sorted := by
 constructor
 · intro member
   exact (sort_sound (dedup entries) sorted (targets_nodup entries) success).1.mem_iff.mp
     (member_preserved entries coherent entry member)
 · intro member
   exact prepared_subset entries sorted success member

theorem prepared_models (model : Model) (assignment : Name → Comp model)
 (entries sorted : List (Entry Name)) (coherent : Coherent entries)
 (success : prepare entries = some sorted) :
 All model assignment (block sorted) ↔ All model assignment (block entries) :=
 (block_perm model assignment (dedup entries) sorted
   (sort_sound (dedup entries) sorted (targets_nodup entries) success).1).symm.trans
   (block_all_iff model assignment entries coherent)

theorem prepared_extension (model : Model) (reflModel : ∀ value, model.subTy value value)
 (entries sorted : List (Entry Name)) (coherent : Coherent entries)
 (success : prepare entries = some sorted) (assignment : Name → Comp model) :
 All model (solve model sorted assignment) (block entries) ∧
 (∀ name, (∀ entry ∈ entries, entry.1 ≠ name) → solve model sorted assignment name = assignment name) ∧
 (∀ name, (solve model sorted assignment name).2 = (assignment name).2) := by
 refine ⟨(prepared_models model _ entries sorted coherent success).mp
   (block_satisfied model reflModel sorted (prepared_safe entries sorted success) assignment),?_,solve_rows model sorted assignment⟩
 intro name outside
 exact solve_outside model sorted assignment name (fun entry member => outside entry (prepared_subset entries sorted success member))

theorem duplicate_reverse_example :
 prepare ([(3,.var 2),(2,.var 0),(3,.var 2)] : List (Entry Nat)) = some [(2,.var 0),(3,.var 2)] := by
 simp [prepare,dedup,remainder,sort,sortFuel,select,readyCheck,GeneralPresenceUsedSupport245.typedReads]
theorem prepared_public_models_iff (model : Model) (laws : Laws model)
 (old fresh oldSorted freshSorted : List (Entry Name))
 (oldCoherent : Coherent old) (freshCoherent : Coherent fresh)
 (oldSuccess : prepare old = some oldSorted) (freshSuccess : prepare fresh = some freshSorted)
 (within : TargetsWithin fresh old) (consumers : List (Atom Name)) (sharedNames : Name → Prop)
 (privateTargets : ∀ name, sharedNames name → ∀ entry ∈ old, entry.1 ≠ name)
 (boundary : Name → Comp model) :
 (∃ assignment, All model assignment (consumers ++ block old) ∧ Agrees model sharedNames assignment boundary) ↔
 (∃ assignment, All model assignment (rewrite oldSorted consumers ++ block fresh) ∧
   Agrees model sharedNames assignment boundary) := by
 have orderedWithin : TargetsWithin freshSorted oldSorted := by
   intro entry member
   obtain ⟨original,present,equal⟩ := within entry (prepared_subset fresh freshSorted freshSuccess member)
   exact ⟨original,(prepared_members old oldSorted oldCoherent oldSuccess original).mp present,equal⟩
 have result := public_models_iff model laws oldSorted freshSorted
   (prepared_safe old oldSorted oldSuccess) (prepared_safe fresh freshSorted freshSuccess)
   orderedWithin consumers sharedNames
   (fun name shared entry member => privateTargets name shared entry (prepared_subset old oldSorted oldSuccess member)) boundary
 simpa only [all_append,prepared_models model _ old oldSorted oldCoherent oldSuccess,
   prepared_models model _ fresh freshSorted freshCoherent freshSuccess] using result

theorem prepare_complete (rank : Name → Nat) (entries : List (Entry Name))
 (ranked : Ranked rank entries) : ∃ sorted, prepare entries = some sorted ∧ SafeOrder sorted := by
 have dedupRanked : Ranked rank (dedup entries) :=
   fun entry member dependency present read =>
     ranked entry (dedup_subset entries member) dependency (dedup_subset entries present) read
 obtain ⟨sorted,success⟩ := sort_complete rank (dedup entries) dedupRanked
 exact ⟨sorted,success,prepared_safe entries sorted success⟩

end Yulang.GeneralPresenceOrderedPrepared247
