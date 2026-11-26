import Yulang.GeneralDeclarativeI65I74WhereRawCohorts451

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.WhereSites450.OriginalCohorts451
open Yulang.GeneralDeclarativeI65
open Checker408 (Problem)
open RetainedFull445
open GeneralDeclarations (Declaration Clause)
open GeneralDeclarationPatterns
open GeneralDeclarativeWitnessDeclaredState357 (point)
open ListSites449.Frame (AuthoredFrame frame_lookup_preserves_original_capture449)

theorem original_clause_capture_is_in_exact_roster451 {s args heads} (a : AuthoredFrame s args heads)
    {x : Nat} (inHead : x ∈ variablesArgs (normalizeArgs heads)) :
    ∃ payload, (x,payload) ∈ a.bindings := by
  induction a with
  | nil => simp [normalizeArgs,variablesArgs] at inHead
  | cons first tail ih =>
    rw [first.headSyntax] at inHead
    simp only [normalizeArgs,normalize,variablesArgs,Pattern.variables,List.append_nil,
      List.singleton_append,List.mem_cons] at inHead
    rcases inHead with rfl|rest
    · exact ⟨first.payload,List.mem_cons_self⟩
    · obtain ⟨payload,found⟩ := ih rest
      exact ⟨payload,List.mem_cons_of_mem _ found⟩

structure ActualPoint (q : I72.Request) where
  center : Nat
  literal : q.demand.arguments = [point center]

def ActualPoint.tag {q : I72.Request} (a : ActualPoint q) : RolePoint :=
  (q.demand.role,a.center)

theorem actual_point_center_unique451 {q : I72.Request} (a b : ActualPoint q) :
    a = b := by
  cases a with
  | mk ca ha =>
    cases b with
    | mk cb hb =>
      have e := congrArg GeneralDeclarativeWhere319.Capture.center
        (List.singleton_inj.mp (ha.symm.trans hb))
      cases e
      rfl

def readPoint (q : I72.Request) : Option (ActualPoint q) :=
  match actual : q.demand.arguments with
  | [arg] =>
    if h : arg.lower = arg.center ∧ arg.upper = arg.center then
      have same : arg = point arg.center := by
        cases arg
        obtain ⟨one,two⟩ := h
        simp only at one two
        subst_vars
        rfl
      some ⟨arg.center,actual.trans (congrArg (fun x => [x]) same)⟩
    else none
  | _ => none

theorem point_reader_recovers_independent_actual_named_center451 {q} (a : ActualPoint q) :
    readPoint q = some a := by
  unfold readPoint
  split
  · rename_i arg known
    have eq := List.singleton_inj.mp (known.symm.trans a.literal)
    subst arg
    simp [point]
  · rename_i none
    exact (none _ a.literal).elim

theorem known_original_clause_has_actual_payload451 {p : Problem}
    (a : ParentSelection p) {i : Nat} {c : Clause} (written : a.decl.requirements[i]? = some c) :
    ∃ binder payload, c.arguments = [.var binder] ∧
      (binder,payload) ∈ a.chosen.roster.bindings ∧
      a.chosen.roster.capture binder = point payload ∧
      a.children[i]? = some ⟨p.root.occurrence ++ [i],⟨c.role,[point payload],[]⟩⟩ := by
  have belongs := List.mem_of_getElem? written
  obtain ⟨binder,args,_⟩ := a.chosen.literal c belongs
  have lexical := a.chosen.checked.scope.1 c belongs binder
    (by simp [args,normalizeArgs,normalize,variablesArgs,Pattern.variables])
  obtain ⟨payload,found⟩ := original_clause_capture_is_in_exact_roster451 a.chosen.roster lexical
  have actual := frame_lookup_preserves_original_capture449 a.chosen.roster a.chosen.distinct found
  refine ⟨binder,payload,args,found,actual,?_⟩
  simpa [literalDemand,args,actual] using actual_child_at_original_clause450 a written

inductive Points : List I72.Request → Type where
  | nil : Points []
  | cons {q qs} (a : ActualPoint q) (rest : Points qs) : Points (q::qs)

def Points.tags {qs} : Points qs → List RolePoint
  | .nil => []
  | .cons a tail => a.tag::tail.tags

theorem Points.length_tags {qs} (p : Points qs) :
    p.tags.length = qs.length := by
  induction p with
  | nil => rfl
  | cons a tail ih => simp [Points.tags,ih]

def readPoints : (qs : List I72.Request) → Option (Points qs)
  | [] => some .nil
  | q::qs => do
    let head ← readPoint q
    let tail ← readPoints qs
    pure (.cons head tail)

theorem readPoints_replays_all_exactly451 {qs} (a : Points qs) :
    readPoints qs = some a := by
  induction a with
  | nil => rfl
  | cons first _ ih =>
    simp [readPoints,point_reader_recovers_independent_actual_named_center451 first,ih,
      Bind.bind,Option.bind,Option.pure_def]

theorem source_replayed_points_are_total451 {p : Problem} (a : ParentSelection p) :
    ∃ r : Points a.children, readPoints a.children = some r := by
  have known : ∀ q ∈ a.children, (readPoint q).isSome = true := by
    intro q belongs
    obtain ⟨i,atReq⟩ := List.mem_iff_getElem?.mp belongs
    cases atClause : a.decl.requirements[i]? with
    | none =>
      simp [ParentSelection.children,GeneralDeclarativeI65.children,List.getElem?_map,List.getElem?_zipIdx,atClause] at atReq
    | some c =>
      obtain ⟨_,n,_,_,_,w⟩ := known_original_clause_has_actual_payload451 a atClause
      rw [atReq] at w
      cases Option.some.inj w
      let source : ActualPoint ⟨p.root.occurrence ++ [i],⟨c.role,[point n],[]⟩⟩ := ⟨n,rfl⟩
      rw [point_reader_recovers_independent_actual_named_center451 source]
      rfl
  have every : ∀ qs : List I72.Request, (∀ q ∈ qs, (readPoint q).isSome = true) →
      ∃ r : Points qs, readPoints qs = some r := by
    intro qs
    induction qs with
    | nil => intro _; exact ⟨.nil,rfl⟩
    | cons q qs ih =>
      intro pass
      cases here : readPoint q with
      | none =>
        have impossible := pass q List.mem_cons_self
        simp [here] at impossible
      | some first =>
        obtain ⟨tail,ok⟩ := ih (fun c mem => pass c (List.mem_cons_of_mem _ mem))
        exact ⟨.cons first tail,by simp [readPoints,here,ok,Bind.bind,Option.bind,Option.pure_def]⟩
  exact every _ known

theorem indexed_point_from_ordered_actual_requests451 {qs} (a : Points qs) (i : Nat) {q : I72.Request}
    (actual : qs[i]? = some q) :
    ∃ p : ActualPoint q, a.tags[i]? = some p.tag := by
  induction a generalizing i with
  | nil => simp at actual
  | cons first _ ih =>
    cases i with
    | zero =>
      have eq := Option.some.inj actual
      cases eq
      exact ⟨first,rfl⟩
    | succ i =>
      exact ih _ (by simpa using actual)

end Yulang.GeneralDeclarativeI65.I72.WhereSites450.OriginalCohorts451
