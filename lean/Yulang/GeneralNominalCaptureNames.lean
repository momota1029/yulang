import Yulang.GeneralNominalPeelingOrigins

/-! Capture names are produced by the finite query syntax. This fact applies
to arbitrary endpoint descriptors and to missing or retained input roots. -/
namespace Yulang.GeneralNominalCaptureNames
open GeneralNominalRecursiveInspection
open GeneralNominalInspection (Query Bounds)

mutual
  def names : Query → List Nat
    | .variables binders => binders
    | .node _ children | .nominal _ children => manyNames children
    | _ => []
  def manyNames : List Query → List Nat
    | [] => []
    | query :: rest => names query ++ manyNames rest
end

def Named (report : Report state) (allowed : List Nat) : Prop :=
  ∀ capture ∈ report.captures, capture.name ∈ allowed

private theorem blank (report : Report state) (empty : report.captures = []) : Named report allowed := by
  intro capture member
  rw [empty] at member
  cases member

private theorem append_same (one : Named (first : Report state) allowed)
    (two : Named (last : Report state) allowed) : Named (first.append last) allowed := by
  intro capture member
  rcases List.mem_append.mp member with member | member
  · exact one capture member
  · exact two capture member

private theorem append_named (one : Named (first : Report state) left)
    (two : Named (last : Report state) right) : Named (first.append last) (left ++ right) :=
  append_same (fun capture member => List.mem_append_left _ (one capture member))
    (fun capture member => List.mem_append_right _ (two capture member))

mutual
  theorem inspect_named (state : GeneralNominalState.State) (query : Query)
      (bounds : Bounds state) (origin : Option Origin) :
      Named (inspect state query bounds origin) (names query) := by
    cases query with
    | variables binders =>
      intro capture member
      simp only [inspect] at member
      obtain ⟨binder,present,rfl⟩ := List.mem_map.mp member
      exact present
    | deferred source => simpa only [inspect] using blank (block bounds) rfl
    | scalar base =>
      simp only [inspect,Report.visit]
      split
      · exact blank _ rfl
      · split
        · split <;> exact blank _ rfl
        · exact blank _ rfl
        · exact blank _ rfl
    | node shape children =>
      simp only [inspect,Report.visit,names]
      split
      · split
        · exact many_named state children _ _ 0
        · exact blank _ rfl
      · exact blank _ rfl
      · exact blank _ rfl
    | nominal name children =>
      simp only [inspect,Report.visit,names]
      split
      · split <;> exact blank _ rfl
      · split
        · split
          · exact blank _ rfl
          · split
            · exact many_named state children _ _ 0
            · split
              · exact blank _ rfl
              · split
                · split
                  · exact blank _ rfl
                  · exact append_same (many_named state children _ _ 0) (many_named state children _ _ 0)
                · exact blank _ rfl
        · exact blank _ rfl
  termination_by sizeOf query

  theorem many_named (state : GeneralNominalState.State) (queries : List Query)
      (bounds : List (Bounds state)) (origins : Nat → Option Origin) (index : Nat) :
      Named (inspectMany state queries bounds origins index) (manyNames queries) := by
    cases queries with
    | nil => cases bounds <;> simpa only [inspectMany] using blank (state := state) _ rfl
    | cons query rest =>
      cases bounds with
      | nil => simpa only [inspectMany] using blank (state := state) _ rfl
      | cons head tail =>
        simp only [inspectMany,manyNames]
        exact append_named (inspect_named state query head (origins index))
          (many_named state rest tail origins (index+1))
  termination_by sizeOf queries
end

theorem distinguished_capture (packet : GeneralNominalSaturationState.Packet roles)
    (query : GeneralNominalInspection.queries packet.context.state packet.context.interpretation packet.declaration =
      .nominal name [.variables [binder]] :: rest)
    (separate : binder ∉ manyNames rest)
    (recorded : packet.site.inputs[0]? = some (some origin))
    (usable : GeneralNominalSharedCaptures.Usable packet binder actual) :
    actual = .nominal origin name 0 := by
  obtain ⟨capture,member,same,retained⟩ := usable.1.1
  unfold GeneralNominalSharedCaptures.inheritedReport at member
  rw [query] at member
  cases boundsEq : packet.bounds with
  | nil => simp [boundsEq,inspectMany] at member
  | cons head tail =>
    simp only [boundsEq,inspectMany,Report.append,recorded,Option.join_some] at member
    rcases List.mem_append.mp member with first | later
    · exact Option.some.inj (retained.symm.trans
        (GeneralNominalPeelingOrigins.nominal_captures _ binder name head origin capture first))
    · exact False.elim (separate (same ▸ many_named _ rest tail _ 1 capture later))

end Yulang.GeneralNominalCaptureNames
