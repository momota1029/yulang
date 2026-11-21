import Yulang.GeneralDeclarativeFreshCapture323
import Yulang.GeneralDeclarativeOutputSplit323

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeRigidBatch323
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeRigidSource323 (Ordered head_fact_exact)
open GeneralDeclarativeRigidOccurrences323 (exact_occurrences)
open GeneralDeclarativeRepeatedActual323 (BindsAt split_binds eqAt)
open GeneralDeclarativeFreshCapture323 (definitions capture fresh_shared avoid model_projection)
open GeneralDeclarativeSemanticSharing323 (SameBinder SharedAt necessary)
open GeneralDeclarativeTermWalk322 (Occurrence)
open GeneralDeclarativeFootprint321 (value_same)
open GeneralDeclarativeArgumentFacts320 (headFact)
open GeneralDeclarativeSubstitution320 (logical)
open GeneralDeclarativeBatch320 (zipFacts)
open GeneralDeclarativeCompileLists321 (Result)
open GeneralDeclarativeEntailment320 (Holds Entails appendFacts model_append)
open GeneralNominalCommonBridge (Assignment)

/-- The actual ordered compiler has exactly the same fixed-capture
content as the real occurrence walk, at every model of the observed state. -/
theorem batch_exact {s : State} (views : Ordered s c interp args pats seen)
    (cap : Nat → Capture) :
    ∃ rows, zipFacts (headFact c interp cap) args pats = some rows ∧
      ∀ m, Models s m → ((∀ row ∈ rows, Holds m row) ↔ BindsAt m cap seen) := by
  induction views with
  | nil =>
    refine ⟨[],rfl,fun _ _ => ?_⟩
    simp [BindsAt]
  | @cons arg p one args ps rest a b ih =>
    obtain ⟨_,raw,_,_,compiled,_,_⟩ := a.exact
    obtain ⟨rows,emit,testing⟩ := ih
    refine ⟨⟨arg.center,logical cap .actual raw⟩ :: rows,
      by simp [zipFacts,headFact,compiled,emit],?_⟩
    intro m valid
    simp only [List.forall_mem_cons]
    exact (and_congr (head_fact_exact a m valid compiled) (testing m valid)).trans
      (split_binds ..).symm

/-- No restrictions on additional facts except preservation of the
ordinary model projection used by the already verified source reads. -/
theorem result_in_extension {s t : State} (views : Ordered s c interp args pats seen)
    (hasSource : ∀ m, Models t m → Models s m)
    (share : SharedAt t seen cap) :
    Result t (zipFacts (headFact c interp cap) args pats) := by
  obtain ⟨rows,compiled,exactly⟩ := batch_exact views cap
  exact ⟨rows,compiled,fun row present m valid =>
    ((exactly m (hasSource m valid)).mpr (share m valid)) row present⟩

theorem value_comparison_old {s : State} {seen : List Occurrence}
    {old new : Assignment} (agrees : ∀ n ∈ avoid s protect seen, new n = old n)
    {x y : Occurrence} (one : x ∈ seen) (two : y ∈ seen) :
    eqAt new x.term y.term ↔ eqAt old x.term y.term := by
  unfold eqAt
  rw [value_same new old .actual _ (fun n h =>
    agrees n (List.mem_append_right _ (List.mem_flatMap.mpr ⟨x,one,h⟩))),
      value_same new old .actual _ (fun n h =>
    agrees n (List.mem_append_right _ (List.mem_flatMap.mpr ⟨y,two,h⟩)))]

/-- True iff: a conservative fresh representative can make the exact
head batch hold in all extensions precisely when same-binder actual
occurrences already agree in all old models. Fresh names cannot hide
a disagreement, even when the state has more than one model. -/
theorem fresh_head_iff {s : State} (views : Ordered s c interp args pats seen)
    (keepNames : List Nat) (endpoints : Nat → Capture) :
    Result (appendFacts s (definitions s keepNames seen))
      (zipFacts (headFact c interp (capture s keepNames seen endpoints)) args pats) ↔
    SameBinder s seen := by
  have mode := (exact_occurrences views).2
  constructor
  · rintro ⟨rows,emit,closed⟩
    obtain ⟨other,known,exactly⟩ := batch_exact views (capture s keepNames seen endpoints)
    have same : other = rows := Option.some.inj (known.symm.trans emit)
    subst other
    have shared : SharedAt (appendFacts s (definitions s keepNames seen)) seen
        (capture s keepNames seen endpoints) := by
      intro m valid
      exact (exactly m ((model_append m).mp valid).1).mp (fun row present => closed row present m valid)
    have consequence := necessary mode shared
    intro x hx y hy binder m valid
    obtain ⟨new,current,unchanged⟩ := (model_projection (s := s) (protect := keepNames) (seen := seen) m).mp valid
    exact (value_comparison_old unchanged hx hy).mp (consequence x hx y hy binder new current)
  · intro all
    exact result_in_extension views (fun m valid => ((model_append m).mp valid).1)
      (fresh_shared mode all)

end Yulang.GeneralDeclarativeRigidBatch323
