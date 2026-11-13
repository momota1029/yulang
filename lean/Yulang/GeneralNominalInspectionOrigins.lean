import Yulang.GeneralNominalGroundProduction

/-! The actual-position certificate forces a retained or recovered origin
at every inspected root. Missing unused variable positions need no origin. -/
namespace Yulang.GeneralNominalInspectionOrigins
open GeneralNominalRecursiveInspection
open GeneralNominalInspection (Query Bounds)

def Counted (report : Report state) : Prop := report.tests.length ≤ report.inspected.length

private theorem append_counted (one : Counted (first : Report state))
    (two : Counted (last : Report state)) : Counted (first.append last) := by
  simp only [Counted,Report.append,List.length_append] at *
  omega

private theorem visit_counted (bounded : Counted (report : Report state)) :
    Counted (report.visit bounds origin test) := by
  cases origin <;> simp only [Counted,Report.visit,Option.toList,List.map_nil,List.map_cons,
    List.length_append,List.length_cons,List.length_nil] at * <;> omega

mutual
  theorem inspect_counted (state : GeneralNominalState.State) (query : Query)
      (bounds : Bounds state) (origin : Option Origin) : Counted (inspect state query bounds origin) := by
    cases query with
    | variables | deferred => simp [inspect,Counted,block]
    | scalar base =>
      simp only [inspect]
      apply visit_counted
      split
      · simp [Counted]
      · split
        · split <;> simp [Counted]
        · simp [Counted]
        · simp [Counted,block]
    | node shape children =>
      simp only [inspect]
      apply visit_counted
      split
      · split
        · exact many_counted state children _ _ 0
        · simp [Counted,block]
      · simp [Counted]
      · simp [Counted,block]
    | nominal name children =>
      simp only [inspect]
      apply visit_counted
      split
      · split <;> simp [Counted,block]
      · split
        · split
          · simp [Counted,block]
          · split
            · exact many_counted state children _ _ 0
            · split
              · simp [Counted,block]
              · split
                · split
                  · simp [Counted,block]
                  · exact append_counted (many_counted state children _ _ 0) (many_counted state children _ _ 0)
                · simp [Counted]
        · simp [Counted]
    termination_by sizeOf query

  theorem many_counted (state : GeneralNominalState.State) (queries : List Query)
      (bounds : List (Bounds state)) (origins : Nat → Option Origin) (offset : Nat) :
      Counted (inspectMany state queries bounds origins offset) := by
    cases queries with
    | nil => cases bounds <;> simp [inspectMany,Counted]
    | cons query rest =>
      cases bounds with
      | nil => simp [inspectMany,Counted]
      | cons head tail =>
        simp only [inspectMany]
        exact append_counted (inspect_counted state query head (origins offset))
          (many_counted state rest tail origins (offset+1))
    termination_by sizeOf queries
end

def Constructor : Query → Prop
  | .scalar _ | .node _ _ | .nominal _ _ => True
  | _ => False

theorem missing_root (state : GeneralNominalState.State) (query : Query) (constructor : Constructor query)
    (bounds : Bounds state) :
    (inspect state query bounds none).tests.length < (inspect state query bounds none).inspected.length := by
  have strict (report : Report state) (counted : Counted report) (test : Test) :
      (report.visit bounds none test).tests.length < (report.visit bounds none test).inspected.length := by
    simpa only [Report.visit,Option.toList,List.map_nil,List.nil_append,List.length_cons] using Nat.lt_succ_of_le counted
  cases query with
  | variables | deferred => cases constructor
  | scalar base =>
    simp only [inspect]
    apply strict
    split
    · simp [Counted]
    · split
      · split <;> simp [Counted]
      · simp [Counted]
      · simp [Counted,block]
  | node shape children =>
    simp only [inspect]
    apply strict
    split
    · split
      · exact many_counted state children _ _ 0
      · simp [Counted,block]
    · simp [Counted]
    · simp [Counted,block]
  | nominal name children =>
    simp only [inspect]
    apply strict
    split
    · split <;> simp [Counted,block]
    · split
      · split
        · simp [Counted,block]
        · split
          · exact many_counted state children _ _ 0
          · split
            · simp [Counted,block]
            · split
              · split
                · simp [Counted,block]
                · exact append_counted (many_counted state children _ _ 0) (many_counted state children _ _ 0)
              · simp [Counted]
      · simp [Counted]

theorem many_complete_component (state : GeneralNominalState.State) {query : Query} {interval : Bounds state} (queries : List Query)
    (bounds : List (Bounds state)) (origins : Nat → Option Origin) (offset index : Nat)
    (queryAt : queries[index]? = some query) (boundsAt : bounds[index]? = some interval)
    (complete : (inspectMany state queries bounds origins offset).tests.length =
      (inspectMany state queries bounds origins offset).inspected.length) :
    (inspect state query interval (origins (offset+index))).tests.length =
      (inspect state query interval (origins (offset+index))).inspected.length := by
  induction queries generalizing bounds offset index with
  | nil => cases queryAt
  | cons head rest ih =>
    cases bounds with
    | nil => cases boundsAt
    | cons first tail =>
      have one := inspect_counted state head first (origins offset)
      have two := many_counted state rest tail origins (offset+1)
      simp only [inspectMany,Report.append,List.length_append] at complete
      unfold Counted at one two
      cases index with
      | zero =>
        cases Option.some.inj queryAt
        cases Option.some.inj boundsAt
        simpa only [Nat.add_zero] using (show (inspect state query interval (origins offset)).tests.length =
          (inspect state query interval (origins offset)).inspected.length from by omega)
      | succ index =>
        have next := ih tail (offset+1) index queryAt boundsAt (by omega)
        simpa only [Nat.add_assoc,Nat.add_comm 1 index] using next

theorem complete_root (state : GeneralNominalState.State) {query : Query} {interval : Bounds state} (queries : List Query)
    (bounds : List (Bounds state)) (origins : Nat → Option Origin) (index : Nat)
    (queryAt : queries[index]? = some query) (boundsAt : bounds[index]? = some interval)
    (constructor : Constructor query)
    (complete : (inspectMany state queries bounds origins 0).tests.length =
      (inspectMany state queries bounds origins 0).inspected.length) : ∃ origin, origins index = some origin := by
  have component := many_complete_component state queries bounds origins 0 index queryAt boundsAt complete
  simp only [Nat.zero_add] at component
  cases recorded : origins index with
  | some origin => exact ⟨origin,rfl⟩
  | none =>
    rw [recorded] at component
    have strict := missing_root state query constructor interval
    omega

end Yulang.GeneralNominalInspectionOrigins
