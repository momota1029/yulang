import Yulang.GeneralRebaseDepthReads285
import Yulang.GeneralRebaseCoordinateProfile285

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 22000
set_option maxHeartbeats 9000000
namespace Yulang.GeneralRebaseDepthPublic285
open GeneralDictionaryOutputDepth252 (plan root registry initial snapshot P model)
open GeneralDictionaryOutputDepthInstall252 (installed step)
open GeneralDictionaryOutputFrame258 (complete source_iff outside)
open GeneralRebaseDepthReads285 (actualEquation explicit equation_emitted)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (Models)
open GeneralOutputRebaseInstalled260 (same_assignment)
open CommonNominalFullCarrier (Ty Equivalent nominal)
open Core.PresenceGeneration (CompTerm)

abbrev SourceTypes := Ty × Ty × Ty

def project (m : Assignment) : SourceTypes := ((m 0).1,(m 1).1,(m 2).1)

def basic (types : SourceTypes) (rows : Nat → Common.Row) : Assignment :=
 fun n => (if n = 0 then types.1 else if n = 1 then types.2.1 else if n = 2 then types.2.2 else .bottom,rows n)

def inflate (types : SourceTypes) (rows : Nat → Common.Row) := complete (basic types rows)

theorem matching (m : Assignment) (n : Nat) (small : n ≤ 2) :
    basic (project m) (fun i => (m i).2) n = m n := by
  have each : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases each with rfl | rfl | rfl <;> rfl

theorem source_models (m : Assignment) :
    GeneralNominalState.Models snapshot (basic (project m) (fun i => (m i).2)) ↔
    GeneralNominalState.Models snapshot m := by
  exact source_iff _ _ (fun _ => rfl) (fun n small => congrArg Prod.fst (matching m n small))

theorem canonical_models (m : Assignment) :
    Models installed (inflate (project m) (fun i => (m i).2)) ↔
    GeneralNominalState.Models snapshot m :=
  (GeneralDictionaryOutputPublic258.installed_exact _).trans (source_models m)

theorem preserve_literal_source (types : SourceTypes) (rows : Nat → Common.Row) :
    project (inflate types rows) = types := by
  unfold project inflate
  rw [outside _ 0 (by decide),outside _ 1 (by decide),outside _ 2 (by decide)]
  cases types
  rfl

theorem row_preservation (types : SourceTypes) (rows : Nat → Common.Row) (n : Nat) :
    (inflate types rows n).2 = rows n := GeneralDictionaryOutputFrame258.rows _ n

theorem compile_output (types : SourceTypes) (rows : Nat → Common.Row) :
    (inflate types rows 3).1 = nominal 0 [.inl (nominal 0 [.inl types.2.2])] := by
  rfl

theorem exact_same_assignment (m : Assignment) :
    Models installed m ↔ GeneralNominalState.Models snapshot m ∧ actualEquation.Holds m := by
  refine (same_assignment m).symm.trans ?_
  rw [GeneralOutputRebaseModels260.final_exact,GeneralDictionaryOutputCompletion258.outputs_exact]
  rfl

theorem finite_typed_frame (a b : Assignment) (types : ∀ n ≤ 3, (a n).1 = (b n).1)
    (rows : ∀ n, (a n).2 = (b n).2) : Models installed a ↔ Models installed b := by
  rw [exact_same_assignment,exact_same_assignment]
  apply and_congr (source_iff a b rows (fun n h => types n (by omega)))
  have profile : GeneralRebaseCoordinateProfile285.ofEquation plan CompTerm.var 3 explicit = some ⟨[3,2],[]⟩ := by
    have h := GeneralRebaseCoordinateProfile285.ofEquation_exact plan CompTerm.var 3 explicit
    rw [equation_emitted] at h
    exact h
  refine GeneralRebaseCoordinateProfile285.exact_observation plan CompTerm.var 3 explicit equation_emitted profile a b ⟨?_,?_⟩
  · intro n h
    change n ∈ ([3,2] : List Nat) at h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl <;> exact types _ (by decide)
  · intro _ h
    cases h

theorem no_raw_substitute :
    project model = project GeneralDictionaryOutputDepthInstall252.smallModel ∧
    (∀ n, (model n).2 = (GeneralDictionaryOutputDepthInstall252.smallModel n).2) ∧
    Models installed model ∧ ¬ Models installed GeneralDictionaryOutputDepthInstall252.smallModel := by
  refine ⟨rfl,fun _ => rfl,GeneralDictionaryOutputDepthInstall252.installed_model,?_⟩
  intro h
  have equal := GeneralDictionaryOutputDepthInstall252.output_forced _ h
  change Equivalent (.base .int) P at equal
  have tags := GeneralDictionaryInspectionHeads215.tag_subtype
    (GeneralDictionaryInspectionHeads215.tagged_scalar .int)
    (GeneralDictionaryInspectionHeads215.tagged_nominal 0 [.inl (nominal 0 [.inl GeneralDictionaryOutputDepth252.F])]) equal.1
  cases tags

end Yulang.GeneralRebaseDepthPublic285
