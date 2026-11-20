import Yulang.GeneralSourceMetadataReport291

/-! With a fixed query, the recursive inspector reads base coordinates,
the normalized view and recorded heads, not the extra constructor table. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 15000000
namespace Yulang.GeneralSourceMetadataInspectTransport291
open GeneralNominalState (State)
open GeneralNominalInspection (Bounds Query)
open GeneralNominalRecursiveInspection (Origin inspect inspectMany block Report typeArguments)
open GeneralSourceMetadataRows291 (Source)
open GeneralSourceMetadataSnapshot291 (Fits retag)
open GeneralSourceMetadataReport291

mutual
 theorem inspect_lower (s : State) (src : Source) (fit : Fits s src) (q : Query)
    (b : Bounds s) (o : Option Origin) :
    lower s src fit (inspect (retag s src fit) q b o) = inspect s q b o := by
  cases q with
  | variables names =>
    simp only [inspect,lower,List.map_map]
    rfl
  | deferred p => simp [inspect]
  | scalar x =>
    simp only [inspect,lower_visit,identical_nominals,identical_view]
    congr 1
    cases h : s.nominals b.1 with
    | some d => rfl
    | none =>
      cases v : s.view.heads b.1 with
      | scalar actual =>
        change lower s src fit (if x = actual then {} else { conflicts := [b] }) =
          if x = actual then {} else { conflicts := [b] }
        by_cases same : x = actual <;> simp only [same,ite_true,ite_false] <;> rfl
      | structural _ _ => rfl
      | deferred _ => rfl
  | node expected children =>
    simp only [inspect,lower_visit,identical_view]
    congr 1
    cases l : s.view.heads b.1 with
    | structural lo ls =>
      cases r : s.view.heads b.2 with
      | structural hi hs =>
        change lower s src fit
          (if s.view.shapes lo = expected ∧ s.view.shapes hi = expected then
            inspectMany (retag s src fit) children ((List.ofFn ls).zip (List.ofFn hs))
              (fun k => o.map fun parent => .structural parent expected k) 0
          else block b) =
          if s.view.shapes lo = expected ∧ s.view.shapes hi = expected then
            inspectMany s children ((List.ofFn ls).zip (List.ofFn hs))
              (fun k => o.map fun parent => .structural parent expected k) 0
          else block b
        by_cases accepted : s.view.shapes lo = expected ∧ s.view.shapes hi = expected
        · rw [ite_eq_left accepted,ite_eq_left accepted]
          exact many_lower _ _ _ _ _ _ _
        · rw [ite_eq_right accepted,ite_eq_right accepted]
          rfl
      | scalar _ => rfl
      | deferred _ => rfl
    | scalar _ => rfl
    | deferred _ => rfl
  | nominal expected children =>
    simp only [inspect,lower_visit,identical_nominals,identical_view,identical_base]
    congr 1
    cases lh : s.nominals b.1 with
    | none => cases v : s.view.heads b.1 <;> rfl
    | some lo =>
      by_cases name : lo.declaration.name = expected
      · simp only [name,ite_true]
        cases ll : typeArguments lo.arguments with
        | none => rfl
        | some args =>
          by_cases point : b.1 = b.2
          · simp only [point,ite_true]
            exact many_lower _ _ _ _ _ _ _
          · simp only [point,ite_false]
            cases uh : s.nominals b.2 with
            | none => rfl
            | some up =>
              by_cases nameU : up.declaration.name = expected
              · simp only [nameU,ite_true]
                cases ur : typeArguments up.arguments with
                | none => rfl
                | some targets =>
                  rw [lower_append]
                  congr 1
                  · exact many_lower _ _ _ _ _ _ _
                  · exact many_lower _ _ _ _ _ _ _
              · simp only [nameU,ite_false]
                rfl
      · simp only [name,ite_false]
        rfl

 theorem many_lower (s : State) (src : Source) (fit : Fits s src) (qs : List Query)
    (bs : List (Bounds s)) (origin : Nat → Option Origin) (index : Nat) :
    lower s src fit (inspectMany (retag s src fit) qs bs origin index) =
      inspectMany s qs bs origin index := by
  cases qs with
  | nil => cases bs <;> simp [inspectMany,lower]
  | cons q qs =>
    cases bs with
    | nil => simp [inspectMany,lower]
    | cons b bs =>
      simp only [inspectMany,lower_append,inspect_lower s src fit q b (origin index),
        many_lower s src fit qs bs origin (index+1)]
end

end Yulang.GeneralSourceMetadataInspectTransport291
