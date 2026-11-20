import Yulang.GeneralGeneratedSemanticAcc299
import Yulang.GeneralGeneratedDictionaryCoherent299

namespace Yulang.GeneralGeneratedSelectedExact299
open B4Target (Vocabulary)
open B4TargetV8
open CommonRoleOutermostResolver (All₂ Child Dictionary Frontier)
open GeneralGeneratedDictionaryRun299
open GeneralGeneratedDictionaryScope299
open GeneralGeneratedSemanticAcc299
open GeneralGeneratedDictionaryRankCheck299 (Known)
open GeneralGeneratedDictionaryCoherent299 (selected_unique)
variable {v : Vocabulary} {b : SourceBoundary v} {r : v.Registry} {s : v.State}

mutual
theorem derivation_accessible (d : Dictionary) (focus : v.Demand)
    (derived : Classify b r s focus (.selected d)) :
    Acc (Child (Local b r s)) focus := by
  cases d with
  | node k ds =>
    cases derived with
    | selected root all =>
      apply Acc.intro
      rintro c ⟨key,childs,other,member⟩
      obtain ⟨_,rfl⟩ := Frontier.selected.inj (local_functional other root)
      exact children_accessible ds _ all c member
termination_by sizeOf d

theorem children_accessible (ds : List Dictionary) (cs : List v.Demand)
    (derived : All₂ (fun c d => Classify b r s c (.selected d)) cs ds)
    (child : v.Demand) (mem : child ∈ cs) :
    Acc (Child (Local b r s)) child := by
  cases derived with
  | nil => cases mem
  | cons head tail =>
    rcases List.mem_cons.mp mem with rfl|rest
    · exact derivation_accessible _ _ head
    · exact children_accessible _ _ tail child rest
termination_by sizeOf ds
end

theorem bounded_exact (read : Read) (decode : Nat → v.Demand)
    (faith : Faithful (b:=b) (r:=r) (s:=s) read decode)
    (closed : Closed read) (domain : List Nat) (known : Known read domain)
    (i : Nat) {row : Entry} (hit : read i = some row) (d : Dictionary) :
    run read domain.length i = some d ↔ Classify b r s (decode i) (.selected d) := by
  constructor
  · exact classifies read decode faith _ i d
  · intro classified
    have acc := derivation_accessible d (decode i) classified
    obtain ⟨other,result⟩ := (bounded_semantic_iff read decode faith closed domain known i hit).mpr acc
    have eq := selected_unique other d (decode i) (classifies read decode faith _ i other result) classified
    exact eq ▸ result

theorem no_result_iff (read : Read) (decode : Nat → v.Demand)
    (faith : Faithful (b:=b) (r:=r) (s:=s) read decode)
    (closed : Closed read) (domain : List Nat) (known : Known read domain)
    (i : Nat) {row : Entry} (hit : read i = some row) :
    run read domain.length i = none ↔
      ¬ ∃ d, Classify b r s (decode i) (.selected d) := by
  constructor
  · intro none
    rintro ⟨d,picked⟩
    have some := (bounded_exact read decode faith closed domain known i hit d).mpr picked
    rw [none] at some
    cases some
  · intro notPicked
    cases tested : run read domain.length i with
    | none => rfl
    | some d => exact False.elim (notPicked ⟨d,classifies read decode faith _ i d tested⟩)

end Yulang.GeneralGeneratedSelectedExact299
