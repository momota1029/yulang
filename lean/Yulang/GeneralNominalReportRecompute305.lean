import Yulang.GeneralNominalReportCoordinates305

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalReportRecompute305
open GeneralNominalInspection (Bounds Query)
open GeneralNominalState (State)
open GeneralNominalRecursiveInspection
open GeneralNominalReportCoordinates305
open GeneralNominalReportSourceTransport (moveBounds moveCapture moveReport)
variable {a b : State}

theorem move_append (f : Fin a.base.slots → Fin b.base.slots) (x y : Report a) :
    moveReport f (x.append y) = (moveReport f x).append (moveReport f y) := by
  simp [moveReport,Report.append,List.map_append]

theorem move_visit (f : Fin a.base.slots → Fin b.base.slots) (span : Bounds a)
    (origin : Option Origin) (test : Test) (report : Report a) :
    moveReport f (Report.visit span origin test report) =
      Report.visit (moveBounds f span) origin test (moveReport f report) := by
  cases origin <;> simp [moveReport,Report.visit]

theorem zip_bounds (f : Fin a.base.slots → Fin b.base.slots)
    (left right : List (Fin a.base.slots)) :
    (left.zip right).map (moveBounds f) = (left.map f).zip (right.map f) := by
  induction left generalizing right with
  | nil => rfl
  | cons i tail ih =>
    cases right with
    | nil => rfl
    | cons j rest => simp [List.zip,moveBounds]

theorem move_nominal_ref (rel : Coordinates a b) (span : Bounds a) :
    (moveBounds rel.slot span).1 = (moveBounds rel.slot span).2 ↔ span.1 = span.2 :=
  ⟨fun same => rel.injective same,fun same => congrArg rel.slot same⟩

mutual
theorem inspect_exact (rel : Coordinates a b) (q : Query) (span : Bounds a) (origin : Option Origin) :
    inspect b q (moveBounds rel.slot span) origin =
      moveReport rel.slot (inspect a q span origin) := by
  cases q with
  | variables names =>
    cases origin <;> simp [inspect,moveReport,moveCapture,List.map_map,Function.comp_def]
  | deferred reason => simp [inspect,block,moveReport]
  | scalar expected =>
    rw [scalar_equation,scalar_equation,move_visit]
    congr 1
    change (if (nominalRead b (rel.slot span.1)).isSome then _ else scalarMiss _ _ (observed b (rel.slot span.1))) = _
    rw [rel.nominal,rel.normalized]
    cases nominalRead a span.1 with
    | some names => rfl
    | none =>
      cases observed a span.1 with
      | pending => rfl
      | scalar actual => by_cases eq : expected = actual <;> simp [scalarMiss,eq,nominalMove,HeadData.move,moveReport]
      | structural shape children => rfl
  | node expected patterns =>
    rw [node_equation,node_equation,move_visit]
    congr 1
    change nodeBody b (moveBounds rel.slot span) origin expected patterns
      (observed b (rel.slot span.1)) (observed b (rel.slot span.2)) = _
    rw [rel.normalized,rel.normalized]
    cases observed a span.1 with
    | pending => cases observed a span.2 <;> rfl
    | scalar actual => cases observed a span.2 <;> rfl
    | structural lower left =>
      cases observed a span.2 with
      | pending => rfl
      | scalar actual => rfl
      | structural upper right =>
        by_cases shapes : lower = expected ∧ upper = expected
        · simp only [HeadData.move,nodeBody,ite_eq_left shapes]
          rw [← zip_bounds rel.slot left right]
          exact many_exact rel patterns (left.zip right)
            (fun i => origin.map fun parent => .structural parent expected i) 0
        · simp only [HeadData.move,nodeBody,ite_eq_right shapes]
          rfl
  | nominal expected patterns =>
    rw [nominal_equation,nominal_equation,move_visit]
    congr 1
    change nominalBody b (moveBounds rel.slot span) origin expected patterns
      (nominalRead b (rel.slot span.1)) (nominalRead b (rel.slot span.2)) (observed b (rel.slot span.1)) = _
    rw [rel.nominal,rel.nominal,rel.normalized]
    cases nominalRead a span.1 with
    | none => cases nominalRead a span.2 <;> cases observed a span.1 <;> rfl
    | some entry =>
      obtain ⟨name,args⟩ := entry
      by_cases named : name = expected
      · cases args with
        | none => simp [nominalMove,nominalBody,named] <;> rfl
        | some arguments =>
          have left := many_exact rel patterns arguments
            (fun i => some (.nominal (origin.getD (.source (a.base.source span.1))) expected i)) 0
          by_cases point : span.1 = span.2
          · simp only [nominalMove,Option.map_some,nominalBody,ite_eq_left named,
              move_nominal_ref rel span,ite_eq_left point]
            simpa only [moveBounds,rel.source_eq] using left
          · have mappedNot : ¬ rel.slot span.1 = rel.slot span.2 := fun x => point (rel.injective x)
            cases nominalRead a span.2 with
            | none => simp [nominalMove,nominalBody,named,point,moveBounds,mappedNot] <;> rfl
            | some entry =>
              obtain ⟨other,more⟩ := entry
              by_cases also : other = expected
              · cases more with
                | none => simp [nominalMove,nominalBody,named,point,also,moveBounds,mappedNot] <;> rfl
                | some targets =>
                  have right := many_exact rel patterns targets
                    (fun i => some (.nominal (origin.getD (.source (a.base.source span.2))) expected i)) 0
                  simp [nominalMove,nominalBody,named,point,also,moveBounds,mappedNot,rel.source_eq,
                    left,right,move_append]
              · simp [nominalMove,nominalBody,named,point,also,moveBounds,mappedNot] <;> rfl
      · simp [nominalMove,nominalBody,named] <;> rfl
termination_by sizeOf q

theorem many_exact (rel : Coordinates a b) (qs : List Query) (spans : List (Bounds a))
    (origins : Nat → Option Origin) (offset : Nat) :
    inspectMany b qs (spans.map (moveBounds rel.slot)) origins offset =
      moveReport rel.slot (inspectMany a qs spans origins offset) := by
  cases qs with
  | nil => cases spans <;> simp [inspectMany,moveReport]
  | cons q rest =>
    cases spans with
    | nil => simp [inspectMany,moveReport]
    | cons point tail =>
      simp only [List.map_cons,inspectMany,move_append]
      rw [inspect_exact rel q point (origins offset),many_exact rel rest tail origins (offset+1)]
termination_by sizeOf qs
end

end Yulang.GeneralNominalReportRecompute305
