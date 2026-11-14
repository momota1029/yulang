import Yulang.GeneralNominalInspectionAlignment

/-! Changing observation origins does not change allocated capture intervals.
This is independent of model validity and of inspection completion. -/
namespace Yulang.GeneralNominalCaptureOrigins187
open GeneralNominalRecursiveInspection
open GeneralNominalInspection (Query Bounds)

def shape (report : Report state) := report.captures.map fun captured => (captured.name,captured.bounds)

 theorem shape_visit (bounds : Bounds state) (origin : Option Origin) (test : Test) (report : Report state) :
    shape (report.visit bounds origin test) = shape report := rfl

 theorem shape_append (one two : Report state) : shape (one.append two) = shape one ++ shape two := by
  simp [shape,Report.append]

mutual
 theorem inspect_shape (state : GeneralNominalState.State) (query : Query) (bounds : Bounds state)
    (first last : Option Origin) : shape (inspect state query bounds first) = shape (inspect state query bounds last) := by
  cases query with
  | variables names => simp [inspect,shape,List.map_map]
  | deferred => simp only [inspect]
  | scalar => simp only [inspect,shape_visit]
  | node sh children =>
    simp only [inspect,shape_visit]
    split
    · split
      · exact many_shape state children _ _ _ 0 0
      · rfl
    · rfl
    · rfl
  | nominal name children =>
    simp only [inspect,shape_visit]
    split
    · split <;> rfl
    · split
      · split
        · rfl
        · split
          · exact many_shape state children _ _ _ 0 0
          · split
            · rfl
            · split
              · split
                · rfl
                · rw [shape_append,shape_append]
                  congr 1 <;> exact many_shape state children _ _ _ 0 0
              · rfl
      · rfl
 termination_by sizeOf query

 theorem many_shape (state : GeneralNominalState.State) (queries : List Query)
    (bounds : List (Bounds state)) (first last : Nat → Option Origin) (one two : Nat) :
    shape (inspectMany state queries bounds first one) = shape (inspectMany state queries bounds last two) := by
  cases queries with
  | nil => cases bounds <;> simp only [inspectMany]
  | cons query rest =>
    cases bounds with
    | nil => simp only [inspectMany]
    | cons head tail =>
      simp only [inspectMany,shape_append,inspect_shape state query head (first one) (last two),
        many_shape state rest tail first last (one+1) (two+1)]
 termination_by sizeOf queries
end

 theorem bindings_shape (state : GeneralNominalState.State) (report : Report state) :
    bindings state report = (shape report).map
      (fun entry => (entry.1,state.base.source entry.2.1,state.base.source entry.2.2)) := by
  simp [bindings,shape,List.map_map]

 theorem many_bindings (state : GeneralNominalState.State) (queries : List Query)
    (bounds : List (Bounds state)) (first last : Nat → Option Origin) (one two : Nat) :
    bindings state (inspectMany state queries bounds first one) =
      bindings state (inspectMany state queries bounds last two) := by
  rw [bindings_shape,bindings_shape,many_shape state queries bounds first last one two]

end Yulang.GeneralNominalCaptureOrigins187
