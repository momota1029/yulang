import Yulang.GeneralNominalRefinementTrace197

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalFinishedObservation197
open GeneralNominalInspection (Query Bounds)
open GeneralNominalRecursiveInspection
open GeneralNominalRefinementTrace197

inductive Syntax : Query → Prop where
  | variables : Syntax (.variables names)
  | nominal (children : ∀ query ∈ patterns, Syntax query) : Syntax (.nominal expected patterns)

theorem finished_visit (value : Report state) :
    Finished (Report.visit bounds origin test value) ↔ Finished value := Iff.rfl

theorem finished_append (first last : Report state) :
    Finished (first.append last) ↔ Finished first ∧ Finished last := by
  simp only [Finished,Report.append,List.append_eq_nil_iff]
  constructor
  · rintro ⟨⟨a,b⟩,⟨c,d⟩,e,f⟩
    exact ⟨⟨a,c,e⟩,b,d,f⟩
  · rintro ⟨⟨a,c,e⟩,b,d,f⟩
    exact ⟨⟨a,b⟩,⟨c,d⟩,e,f⟩

mutual
  theorem observed_of_finished (shape : Syntax query)
      (finished : Finished (inspect state query bounds origin)) : Observed state query bounds := by
    cases shape with
    | variables => exact .variables
    | @nominal patterns expected children =>
      simp only [inspect,finished_visit] at finished
      cases lowerEq : state.nominals bounds.1 with
      | none =>
        simp only [lowerEq] at finished
        cases headEq : state.view.heads bounds.1 <;> simp [headEq,Finished,block] at finished
      | some lower =>
        simp only [lowerEq] at finished
        split at finished
        next lowerName =>
          cases argsEq : typeArguments lower.arguments with
          | none => simp [argsEq,Finished,block] at finished
          | some actuals =>
            simp only [argsEq] at finished
            split at finished
            next same =>
              obtain ⟨first,last⟩ := bounds
              change first = last at same
              subst last
              exact .point lowerEq lowerName argsEq (many_observed_of_finished children finished)
            next different =>
              cases upperEq : state.nominals bounds.2 with
              | none => simp [upperEq,Finished,block] at finished
              | some upper =>
                simp only [upperEq] at finished
                split at finished
                next upperName =>
                  cases targetEq : typeArguments upper.arguments with
                  | none => simp [targetEq,Finished,block] at finished
                  | some targets =>
                    simp only [targetEq,finished_append] at finished
                    exact .interval different lowerEq upperEq lowerName upperName argsEq targetEq
                      (many_observed_of_finished children finished.1)
                      (many_observed_of_finished children finished.2)
                next wrong => simp [Finished] at finished
        next wrong => simp [Finished] at finished
  termination_by sizeOf query
  theorem many_observed_of_finished (shape : ∀ query ∈ queries, Syntax query)
      (finished : Finished (inspectMany state queries bounds origins index)) :
      ObservedMany state queries bounds := by
    cases queries with
    | nil =>
      cases bounds with
      | nil => exact .nil
      | cons head tail => simp [inspectMany,Finished] at finished
    | cons query queries =>
      cases bounds with
      | nil => simp [inspectMany,Finished] at finished
      | cons head tail =>
        rw [inspectMany,finished_append] at finished
        exact .cons (observed_of_finished (shape query (by simp)) finished.1)
          (many_observed_of_finished (fun q member => shape q (by simp [member])) finished.2)
  termination_by sizeOf queries
end
end Yulang.GeneralNominalFinishedObservation197
